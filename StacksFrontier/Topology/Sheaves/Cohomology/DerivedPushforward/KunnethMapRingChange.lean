module

public import StacksFrontier.CategoryTheory.Adjunction.KunnethLegRingChange
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionAlongAComposite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionAssociativity
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorIsoCompositionLaw

/-!
# The relative Künneth map under a change of the ringed spaces over the base

Let `S` be a ringed space and consider two levels of ringed spaces over it: `X₂, Y₂, W₂` with
`a₂ : X₂ ⟶ S`, `b₂ : Y₂ ⟶ S` and projections `p₂ : W₂ ⟶ X₂`, `q₂ : W₂ ⟶ Y₂` with
`q₂ ≫ b₂ = p₂ ≫ a₂`; and `X₁, Y₁, W₁` with morphisms `ι_X : X₁ ⟶ X₂`, `ι_Y : Y₁ ⟶ Y₂`,
`ι_W : W₁ ⟶ W₂` and projections `p₁ : W₁ ⟶ X₁`, `q₁ : W₁ ⟶ Y₁` making the squares
`p₁ ≫ ι_X = ι_W ≫ p₂` and `q₁ ≫ ι_Y = ι_W ≫ q₂` commute. Then the relative Künneth map of
[Stacks, Tag 0FLP] on the first level, at `K ∈ D(X₁)` and `M ∈ D(Y₁)`, is the one on the second
level at `Rι_{X*}K` and `Rι_{Y*}M`, followed by `R(p₂ ≫ a₂)_*` of

`Lp₂^*Rι_{X*}K ⊗^𝐋 Lq₂^*Rι_{Y*}M ⟶ Rι_{W*}Lp₁^*K ⊗^𝐋 Rι_{W*}Lq₁^*M ⟶ Rι_{W*}(Lp₁^*K ⊗^𝐋 Lq₁^*M)`,

the two derived base change maps of [Stacks, Tag 08HY] followed by the relative cup product of
[Stacks, Tag 0B68] for `ι_W`, all read through the composition isomorphisms of
[Stacks, Tag 0D5T].

It is used with `X₁ = (X, 𝒪_X)` and `X₂ = (X, a^{-1}𝒪_S)`, where it compares the Künneth map of
a fibre product of schemes with the one of the inverse-image ringed spaces on which the de Rham
Künneth map of [Stacks, Tag 0G4B] is built.

## Main results

* `Stacks.Cohomology.DerivedKunneth.kunnethMap_ringChange`: the comparison.

## Implementation notes

The whole argument is abstract and lives in
`StacksFrontier/CategoryTheory/Adjunction/KunnethLegRingChange.lean`; here it is applied, with the
hypotheses discharged by the derived adjunction of a composite
(`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_comp`), the monoidality of
a composite (`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_comp`), the cocycle
identity of [Stacks, Tag 0D5S]
(`Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackCompIsoCanonical_assoc`) and
two transports proved here, all of them equalities of natural transformations or isomorphisms
and none of components: at the derived categories of module sheaves the kernel does not settle
definitional equalities between components in reasonable time, as the implementation notes of
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/KunnethBaseChangeLeg.lean` record.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped CategoryTheory.Prod
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedPullback.Composition

universe u

namespace Stacks.Cohomology.DerivedKunneth

attribute [local instance] HasDerivedCategory.standard

/-- The composition isomorphism of [Stacks, Tag 0D5S] at the standard derived categories, with
its three `HasDerivedCategory` instances given at the spelling
`SheafOfModules (structureSheafRing _)` that the derived pullback itself is stated at. -/
abbrev compIsoS {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  @derivedPullbackCompIsoCanonical X Y Z f g
    (HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing X)))
    (HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing Y)))
    (HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing Z)))

/-- **The composition isomorphism of derived pullback is compatible with replacing the inner
morphism by an equal one.** -/
theorem derivedPullbackCompIsoCanonical_transport_left {Z₁ Z₂ Z₃ : RingedSpace.{u, u}}
    {u v : Z₁ ⟶ Z₂} (h : u = v) (g : Z₂ ⟶ Z₃) :
    Functor.isoWhiskerLeft (derivedPullback g)
        (eqToIso (congrArg (fun w : Z₁ ⟶ Z₂ => derivedPullback w) h)) ≪≫
        derivedPullbackCompIsoCanonical v g =
      derivedPullbackCompIsoCanonical u g ≪≫
        eqToIso (congrArg (fun w : Z₁ ⟶ Z₂ => derivedPullback (w ≫ g)) h) := by
  subst h
  simp

/-- **The composition isomorphism of derived pullback is compatible with replacing the outer
morphism by an equal one.** -/
theorem derivedPullbackCompIsoCanonical_transport_right {Z₁ Z₂ Z₃ : RingedSpace.{u, u}}
    (f : Z₁ ⟶ Z₂) {u v : Z₂ ⟶ Z₃} (h : u = v) :
    Functor.isoWhiskerRight (eqToIso (congrArg (fun w : Z₂ ⟶ Z₃ => derivedPullback w) h))
        (derivedPullback f) ≪≫
        derivedPullbackCompIsoCanonical f v =
      derivedPullbackCompIsoCanonical f u ≪≫
        eqToIso (congrArg (fun w : Z₂ ⟶ Z₃ => derivedPullback (f ≫ w)) h) := by
  subst h
  simp

/-- The cocycle identity of [Stacks, Tag 0D5S] for `compIsoS`, with the composite `g ≫ h` named
and the reassociation carried by a transport. -/
theorem compIsoS_assoc {Z₁ Z₂ Z₃ Z₄ : RingedSpace.{u, u}} (f : Z₁ ⟶ Z₂) (g : Z₂ ⟶ Z₃)
    (h : Z₃ ⟶ Z₄) (a : Z₂ ⟶ Z₄) (ha : g ≫ h = a) (hfa : (f ≫ g) ≫ h = f ≫ a) :
    Functor.isoWhiskerLeft (derivedPullback h) (compIsoS f g) ≪≫
        (compIsoS (f ≫ g) h ≪≫ eqToIso (congrArg (fun w : Z₁ ⟶ Z₄ => derivedPullback w) hfa)) =
      (Functor.associator (derivedPullback h) (derivedPullback g) (derivedPullback f)).symm ≪≫
        Functor.isoWhiskerRight
          (compIsoS g h ≪≫ eqToIso (congrArg (fun w : Z₂ ⟶ Z₄ => derivedPullback w) ha))
          (derivedPullback f) ≪≫ compIsoS f a := by
  subst ha
  have e := Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackCompIsoCanonical_assoc
    f g h
  have hr : eqToIso (congrArg (fun w : Z₁ ⟶ Z₄ => derivedPullback w) hfa) = Iso.refl _ :=
    eqToIso_refl _
  rw [← Iso.trans_assoc]
  refine (congrArg (_ ≪≫ ·) hr).trans ((Iso.trans_refl _).trans (e.trans ?_))
  ext M
  simp

/-- The cocycle identity of [Stacks, Tag 0D5S] for `compIsoS`, with the reassociation carried by
a transport. -/
theorem compIsoS_assoc' {Z₁ Z₂ Z₃ Z₄ : RingedSpace.{u, u}} (f : Z₁ ⟶ Z₂) (g : Z₂ ⟶ Z₃)
    (h : Z₃ ⟶ Z₄) (hfa : (f ≫ g) ≫ h = f ≫ g ≫ h) :
    Functor.isoWhiskerLeft (derivedPullback h) (compIsoS f g) ≪≫
        (compIsoS (f ≫ g) h ≪≫ eqToIso (congrArg (fun w : Z₁ ⟶ Z₄ => derivedPullback w) hfa)) =
      (Functor.associator (derivedPullback h) (derivedPullback g) (derivedPullback f)).symm ≪≫
        Functor.isoWhiskerRight (compIsoS g h) (derivedPullback f) ≪≫ compIsoS f (g ≫ h) := by
  have := compIsoS_assoc f g h (g ≫ h) rfl hfa
  simpa only [eqToIso_refl, Iso.trans_refl] using this

/-- Transport of `compIsoS` along an equality of the outer morphism. -/
theorem compIsoS_transport_right {Z₁ Z₂ Z₃ : RingedSpace.{u, u}} (f : Z₁ ⟶ Z₂)
    {u v : Z₂ ⟶ Z₃} (h : u = v) (F : Z₁ ⟶ Z₃) (hF : f ≫ v = F) (hF' : f ≫ u = F) :
    Functor.isoWhiskerRight (eqToIso (congrArg (fun w : Z₂ ⟶ Z₃ => derivedPullback w) h.symm))
        (derivedPullback f) ≪≫ compIsoS f u =
      (compIsoS f v ≪≫ eqToIso (congrArg (fun w : Z₁ ⟶ Z₃ => derivedPullback w) hF)) ≪≫
        eqToIso (congrArg (fun w : Z₁ ⟶ Z₃ => derivedPullback w) hF'.symm) := by
  subst h hF
  simp

/-- Transport of `compIsoS` along an equality of the inner morphism. -/
theorem compIsoS_transport_left {Z₁ Z₂ Z₃ : RingedSpace.{u, u}} {u v : Z₁ ⟶ Z₂} (h : u = v)
    (g : Z₂ ⟶ Z₃) (F G : Z₁ ⟶ Z₃) (hu : u ≫ g = F) (hv : v ≫ g = G) (hFG : F = G) :
    Functor.isoWhiskerLeft (derivedPullback g)
        (eqToIso (congrArg (fun w : Z₁ ⟶ Z₂ => derivedPullback w) h)) ≪≫
        (compIsoS v g ≪≫ eqToIso (congrArg (fun w : Z₁ ⟶ Z₃ => derivedPullback w) hv)) =
      (compIsoS u g ≪≫ eqToIso (congrArg (fun w : Z₁ ⟶ Z₃ => derivedPullback w) hu)) ≪≫
        eqToIso (congrArg (fun w : Z₁ ⟶ Z₃ => derivedPullback w) hFG) := by
  subst h hu hv
  simp

/-- The derived adjunction of a named composite is the composite adjunction transported along
`compIsoS` and the composition isomorphism of derived pushforward. -/
theorem derivedAdjunction_comp_of_eq {Z₁ Z₂ Z₃ : RingedSpace.{u, u}} (f : Z₁ ⟶ Z₂)
    (g : Z₂ ⟶ Z₃) (k : Z₁ ⟶ Z₃) (hk : f ≫ g = k) :
    (((derivedAdjunction g).comp (derivedAdjunction f)).ofNatIsoLeft
        (compIsoS f g ≪≫
          eqToIso (congrArg (fun w : Z₁ ⟶ Z₃ => derivedPullback w) hk))).ofNatIsoRight
        (derivedPushforwardCompIso f g ≪≫
          eqToIso (congrArg (fun w : Z₁ ⟶ Z₃ => derivedPushforward w) hk)) =
      derivedAdjunction k := by
  subst hk
  simpa using derivedAdjunction_comp f g

section Leg

variable {S X₂ W₂ X₁ W₁ : RingedSpace.{u, u}} (a₂ : X₂ ⟶ S) (p₂ : W₂ ⟶ X₂)
  (ιX : X₁ ⟶ X₂) (ιW : W₁ ⟶ W₂) (p₁ : W₁ ⟶ X₁) (sqp : p₁ ≫ ιX = ιW ≫ p₂)
  (a₁ : X₁ ⟶ S) (ha : ιX ≫ a₂ = a₁) (f₂ : W₂ ⟶ S) (hp₂ : p₂ ≫ a₂ = f₂) (f₁ : W₁ ⟶ S)
  (hf : ιW ≫ f₂ = f₁) (hp₁ : p₁ ≫ a₁ = f₁)

/-- **The counit leg on the first projection under a change of the spaces.** The counit leg of
the first level at `a₁ = ι_X ≫ a₂`, read through the composition isomorphisms, is the counit leg
of the second level at `Rι_{X*}K` followed by the derived base change map of the square
`p₁ ≫ ι_X = ι_W ≫ p₂` and the counit of `Lι_W^* ⊣ Rι_{W*}`. -/
theorem pullbackCounitLeg_ringChange
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X₁))) :
    (derivedPullback ιW).map ((derivedPullback f₂).map
        ((derivedPushforwardCompIso ιX a₂ ≪≫
          eqToIso (congrArg (fun w : X₁ ⟶ S => derivedPushforward w) ha)).hom.app K)) ≫
        (compIsoS ιW f₂ ≪≫
          eqToIso (congrArg (fun w : W₁ ⟶ S => derivedPullback w) hf)).hom.app
          ((derivedPushforward a₁).obj K) ≫
        (pullbackCounitLeg a₁ p₁ f₁ hp₁).app K =
      (derivedPullback ιW).map ((pullbackCounitLeg a₂ p₂ f₂ hp₂).app
          ((derivedPushforward ιX).obj K)) ≫
        (derivedPullback ιW).map
          ((Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeSquare p₁ ιW ιX p₂ sqp).app K) ≫
        (derivedAdjunction ιW).counit.app ((derivedPullback p₁).obj K) :=
  CategoryTheory.KunnethLegRingChange.leg_ringChange_of_eq (derivedAdjunction a₂)
    (derivedAdjunction ιX) (derivedAdjunction a₁) (derivedAdjunction ιW)
    (compIsoS ιX a₂ ≪≫ eqToIso (congrArg (fun w : X₁ ⟶ S => derivedPullback w) ha))
    (derivedPushforwardCompIso ιX a₂ ≪≫
      eqToIso (congrArg (fun w : X₁ ⟶ S => derivedPushforward w) ha))
    (compIsoS p₁ a₁)
    (compIsoS ιW f₂ ≪≫ eqToIso (congrArg (fun w : W₁ ⟶ S => derivedPullback w) hf))
    (compIsoS p₁ ιX) (compIsoS ιW p₂)
    (compIsoS (p₁ ≫ ιX) a₂ ≪≫ eqToIso (congrArg (fun w : W₁ ⟶ S => derivedPullback w)
      (show (p₁ ≫ ιX) ≫ a₂ = p₁ ≫ a₁ by rw [Category.assoc, ha])))
    (compIsoS p₂ a₂) (compIsoS ιW (p₂ ≫ a₂))
    (compIsoS (ιW ≫ p₂) a₂ ≪≫ eqToIso (congrArg (fun w : W₁ ⟶ S => derivedPullback w)
      (Category.assoc ιW p₂ a₂)))
    (derivedAdjunction_comp_of_eq ιX a₂ a₁ ha)
    (compIsoS_assoc p₁ ιX a₂ a₁ ha (by rw [Category.assoc, ha]))
    (compIsoS_assoc' ιW p₂ a₂ (Category.assoc ιW p₂ a₂))
    (congrArg (fun w : W₂ ⟶ S => derivedPullback w) hp₂.symm)
    (congrArg (fun w : W₁ ⟶ S => derivedPullback w)
      (hf.symm.trans (congrArg (ιW ≫ ·) hp₂.symm)))
    (compIsoS_transport_right ιW hp₂ f₁ hf ((congrArg (ιW ≫ ·) hp₂).trans hf))
    (congrArg (fun w : W₁ ⟶ X₂ => derivedPullback w) sqp.symm)
    (congrArg (fun w : W₁ ⟶ S => derivedPullback w)
      ((congrArg (ιW ≫ ·) hp₂).trans (hf.trans hp₁.symm)))
    (compIsoS_transport_left sqp.symm a₂ _ _ (Category.assoc ιW p₂ a₂)
      (by rw [Category.assoc, ha]) ((congrArg (ιW ≫ ·) hp₂).trans (hf.trans hp₁.symm)))
    (pullbackCounitLeg a₁ p₁ f₁ hp₁)
    (congrArg (fun z : W₁ ⟶ S => derivedPushforward a₁ ⋙ derivedPullback z) hp₁.symm) rfl
    (pullbackCounitLeg a₂ p₂ f₂ hp₂)
    (congrArg (fun z : W₂ ⟶ S => derivedPushforward a₂ ⋙ derivedPullback z) hp₂.symm) rfl
    (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeSquare p₁ ιW ιX p₂ sqp) rfl K

end Leg

section Assembly

/-- In `a ≫ b = c ≫ e.hom` with `a` and `b` invertible and `e` an isomorphism, `c` is
invertible. -/
theorem isIso_of_comp_eq_comp_hom {C : Type*} [Category C] {P Q R T : C} (a : P ⟶ Q) (b : Q ⟶ T)
    (c : P ⟶ R) (e : R ≅ T) (h : a ≫ b = c ≫ e.hom) [IsIso a] [IsIso b] : IsIso c := by
  have : c = (a ≫ b) ≫ e.inv := by rw [h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [this]
  infer_instance

variable {S X₂ Y₂ W₂ X₁ Y₁ W₁ : RingedSpace.{u, u}}

/-- The monoidality of [Stacks, Tag 079U] for a named composite, at `compIsoS`. -/
theorem pullbackTensorComparison_comp_of_eq (ιW : W₁ ⟶ W₂) (f₂ : W₂ ⟶ S) (f₁ : W₁ ⟶ S)
    (hf : ιW ≫ f₂ = f₁) :
    Functor.whiskerLeft (Functor.uncurry.obj
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.sheaf))
        (compIsoS ιW f₂ ≪≫ eqToIso (congrArg (fun w : W₁ ⟶ S => derivedPullback w) hf)).hom ≫
        Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f₁ =
      (Functor.whiskerRight (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f₂)
          (derivedPullback ιW) ≫
        Functor.whiskerLeft ((derivedPullback f₂).prod (derivedPullback f₂))
          (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison ιW)) ≫
        Functor.whiskerRight (NatTrans.prod
          (compIsoS ιW f₂ ≪≫ eqToIso (congrArg (fun w : W₁ ⟶ S => derivedPullback w) hf)).hom
          (compIsoS ιW f₂ ≪≫ eqToIso (congrArg (fun w : W₁ ⟶ S => derivedPullback w) hf)).hom)
          (Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor W₁.sheaf)) := by
  subst hf
  have h := Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_comp ιW f₂
  simp only [eqToIso_refl, Iso.trans_refl]
  exact h.trans (Category.assoc _ _ _).symm

variable (a₂ : X₂ ⟶ S) (b₂ : Y₂ ⟶ S) (p₂ : W₂ ⟶ X₂) (q₂ : W₂ ⟶ Y₂) (f₂ : W₂ ⟶ S)
  (hp₂ : p₂ ≫ a₂ = f₂) (hq₂ : q₂ ≫ b₂ = f₂)
  (ιX : X₁ ⟶ X₂) (ιY : Y₁ ⟶ Y₂) (ιW : W₁ ⟶ W₂) (p₁ : W₁ ⟶ X₁) (q₁ : W₁ ⟶ Y₁)
  (sqp : p₁ ≫ ιX = ιW ≫ p₂) (sqq : q₁ ≫ ιY = ιW ≫ q₂)
  (a₁ : X₁ ⟶ S) (ha : ιX ≫ a₂ = a₁) (b₁ : Y₁ ⟶ S) (hb : ιY ≫ b₂ = b₁)
  (f₁ : W₁ ⟶ S) (hf : ιW ≫ f₂ = f₁) (hp₁ : p₁ ≫ a₁ = f₁) (hq₁ : q₁ ≫ b₁ = f₁)

/-- **The relative Künneth map of [Stacks, Tag 0FLP] under a change of the ringed spaces over
the base.** With two levels of ringed spaces over `S` related by `ι_X`, `ι_Y`, `ι_W` as in the
introduction, the Künneth map of the first level at `K` and `M`, read through the composition
isomorphisms `Rι_{X*} ⋙ Ra₂_* ≅ Ra₁_*` and `Rι_{Y*} ⋙ Rb₂_* ≅ Rb₁_*`, is the Künneth map of the
second level at `Rι_{X*}K` and `Rι_{Y*}M`, followed by `Rf₂_*` of the two derived base change
maps of [Stacks, Tag 08HY] and of the relative cup product of [Stacks, Tag 0B68] for `ι_W`, and
by the composition isomorphism `Rι_{W*} ⋙ Rf₂_* ≅ Rf₁_*`. -/
theorem kunnethMap_ringChange
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X₁)))
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y₁))) :
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.sheaf)).map
        ((derivedPushforwardCompIso ιX a₂ ≪≫
            eqToIso (congrArg (fun w : X₁ ⟶ S => derivedPushforward w) ha)).hom.app K ×ₘ
          (derivedPushforwardCompIso ιY b₂ ≪≫
            eqToIso (congrArg (fun w : Y₁ ⟶ S => derivedPushforward w) hb)).hom.app M) ≫
        kunnethMap a₁ b₁ p₁ q₁ f₁ hp₁ hq₁ K M =
      kunnethMap a₂ b₂ p₂ q₂ f₂ hp₂ hq₂ ((derivedPushforward ιX).obj K)
          ((derivedPushforward ιY).obj M) ≫
        (derivedPushforward f₂).map
          ((Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor W₂.sheaf)).map
              ((Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeSquare p₁ ιW ιX p₂ sqp).app
                  K ×ₘ
                (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeSquare q₁ ιW ιY q₂ sqq).app
                  M) ≫
            Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct ιW
              ((derivedPullback p₁).obj K) ((derivedPullback q₁).obj M)) ≫
        (derivedPushforwardCompIso ιW f₂ ≪≫
            eqToIso (congrArg (fun w : W₁ ⟶ S => derivedPushforward w) hf)).hom.app
          (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor W₁.sheaf).obj
            ((derivedPullback p₁).obj K)).obj ((derivedPullback q₁).obj M)) :=
  CategoryTheory.KunnethLegRingChange.kunneth_ringChange (derivedAdjunction f₂)
    (derivedAdjunction ιW) (derivedAdjunction f₁)
    (compIsoS ιW f₂ ≪≫ eqToIso (congrArg (fun w : W₁ ⟶ S => derivedPullback w) hf))
    (derivedPushforwardCompIso ιW f₂ ≪≫
      eqToIso (congrArg (fun w : W₁ ⟶ S => derivedPushforward w) hf))
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.sheaf))
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor W₂.sheaf))
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor W₁.sheaf))
    (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f₂)
    (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison ιW)
    (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f₁)
    (pullbackCounitLeg a₁ p₁ f₁ hp₁) (pullbackCounitLeg b₁ q₁ f₁ hq₁)
    (pullbackCounitLeg a₂ p₂ f₂ hp₂) (pullbackCounitLeg b₂ q₂ f₂ hq₂)
    (derivedPushforwardCompIso ιX a₂ ≪≫
      eqToIso (congrArg (fun w : X₁ ⟶ S => derivedPushforward w) ha))
    (derivedPushforwardCompIso ιY b₂ ≪≫
      eqToIso (congrArg (fun w : Y₁ ⟶ S => derivedPushforward w) hb))
    (derivedAdjunction_comp_of_eq ιW f₂ f₁ hf)
    (pullbackTensorComparison_comp_of_eq ιW f₂ f₁ hf) K M
    ((Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeSquare p₁ ιW ιX p₂ sqp).app K)
    ((Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeSquare q₁ ιW ιY q₂ sqq).app M)
    (pullbackCounitLeg_ringChange a₂ p₂ ιX ιW p₁ sqp a₁ ha f₂ hp₂ f₁ hf hp₁ K)
    (pullbackCounitLeg_ringChange b₂ q₂ ιY ιW q₁ sqq b₁ hb f₂ hq₂ f₁ hf hq₁ M)

include ha hb hf in
/-- **The Künneth map of the second level followed by the change of spaces is invertible as soon
as the Künneth map of the first level is.** This is `kunnethMap_ringChange` read as an
invertibility statement: the other factors are composition isomorphisms. -/
theorem isIso_kunnethMap_ringChange
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X₁)))
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y₁)))
    (hκ : IsIso (kunnethMap a₁ b₁ p₁ q₁ f₁ hp₁ hq₁ K M)) :
    IsIso (kunnethMap a₂ b₂ p₂ q₂ f₂ hp₂ hq₂ ((derivedPushforward ιX).obj K)
          ((derivedPushforward ιY).obj M) ≫
        (derivedPushforward f₂).map
          ((Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor W₂.sheaf)).map
              ((Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeSquare p₁ ιW ιX p₂ sqp).app
                  K ×ₘ
                (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeSquare q₁ ιW ιY q₂ sqq).app
                  M) ≫
            Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct ιW
              ((derivedPullback p₁).obj K) ((derivedPullback q₁).obj M))) := by
  have : IsIso ((Functor.uncurry.obj
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.sheaf)).map
        ((derivedPushforwardCompIso ιX a₂ ≪≫
            eqToIso (congrArg (fun w : X₁ ⟶ S => derivedPushforward w) ha)).hom.app K ×ₘ
          (derivedPushforwardCompIso ιY b₂ ≪≫
            eqToIso (congrArg (fun w : Y₁ ⟶ S => derivedPushforward w) hb)).hom.app M)) :=
    Functor.map_isIso _ (((derivedPushforwardCompIso ιX a₂ ≪≫
            eqToIso (congrArg (fun w : X₁ ⟶ S => derivedPushforward w) ha)).app K).prod
          ((derivedPushforwardCompIso ιY b₂ ≪≫
            eqToIso (congrArg (fun w : Y₁ ⟶ S => derivedPushforward w) hb)).app M)).hom
  exact isIso_of_comp_eq_comp_hom _ _ _ ((derivedPushforwardCompIso ιW f₂ ≪≫
      eqToIso (congrArg (fun w : W₁ ⟶ S => derivedPushforward w) hf)).app _)
    ((kunnethMap_ringChange a₂ b₂ p₂ q₂ f₂ hp₂ hq₂ ιX ιY ιW p₁ q₁ sqp sqq a₁ ha b₁ hb f₁ hf
      hp₁ hq₁ K M).trans (Category.assoc _ _ _).symm)

end Assembly

end Stacks.Cohomology.DerivedKunneth

end
