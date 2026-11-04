module

import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.OrdinaryLocality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.OrdinaryLocality
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.OrdinaryLocalityCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.OrdinaryLocalityCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.SmallEtaleBaseChangeAbBridge

/-!
# From set coefficients to abelian coefficients on Mathlib's small étale sites

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a commutative square of schemes. Two base change comparisons of this square live on Mathlib's
small étale sites `AlgebraicGeometry.Scheme.Etale`: the comparison
`Stacks.EtaleCohomology.smallEtaleSetsBaseChange` for sheaves of **sets**, which is the mate of
the identification of the two composite direct images, and the comparison
`Stacks.EtaleCohomology.smallEtaleBaseChangeAb` for sheaves of **abelian groups**, which is the
mate of that same identification at abelian coefficients. This file carries invertibility from
the first to the second.

Nothing is assumed of the square beyond commutativity. Which squares have an invertible
set-valued comparison is the geometric question — it is Stacks 0959 for a finite morphism and
Stacks 0EZR for an étale-local situation — and here it is the hypothesis.

## Main results

* `Stacks.EtaleCohomology.isIso_smallEtaleBaseChangeAb_of_isIso_smallEtaleSetsBaseChange` —
  **invertibility of the base change comparison of sheaves of sets forces invertibility of the
  base change comparison of abelian sheaves**, both on Mathlib's small étale sites.

## Implementation notes

The device is `Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms`: a mate
transports along a change of the four categories of its square. The four functors joining the
abelian square to the set-valued one are all composition with the forgetful functor of abelian
groups, `CategoryTheory.sheafCompose`, which reflects isomorphisms — all the transport lemma asks
of the functor at the lower-right corner. The side faces through a direct image are filled by
identities, because direct image is restriction along a functor of sites and so commutes with a
change of coefficients on the nose; the side faces through an inverse image are filled by
`Stacks.EtaleCohomology.coefficientPullbackTwoSquare`, whose invertibility is
`Stacks.EtaleCohomology.isIso_coefficientPullbackTwoSquare`. All of that is the work done in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransfer`;
what this file adds is the same cube with the 2-cell of **Mathlib's** sites,
`Stacks.EtaleCohomology.smallEtaleSquarePushforwardIsoAt`, in place of the one of the
size-bounded sites of Stacks 021B, so that the input is the comparison of
`Stacks.EtaleCohomology.smallEtaleSetsBaseChange` rather than
`AlgebraicGeometry.smallEtaleBaseChangeNatTrans`. The compatibility of that 2-cell with the
change of coefficients is `smallEtaleSquarePushforwardIsoAt_forget`: both sides restrict sections
along one and the same comparison of composite base changes of sites, by
`Stacks.EtaleCohomology.smallEtaleSquarePushforwardIsoAt_app`, and restriction commutes with
applying the forgetful functor to the sections.

The last step changes the left adjoints. The cube is run with the inverse image built as a left
Kan extension followed by sheafification, which is the presentation
`Stacks.EtaleCohomology.coefficientPullbackTwoSquare` is about, whereas
`Stacks.EtaleCohomology.smallEtaleBaseChangeAb` is a mate along the abstract left adjoint
`CategoryTheory.Functor.sheafPullback`. The two right adjoints agree, so
`Stacks.CategoryTheory.isIso_mateEquiv_symm_of_isIso_mateEquiv_symm` absorbs the difference.

Coefficients are `AddCommGrpCat.{u + 1}`, which is `Ab.{u + 1}`, and the sheaves of sets are
those of `Type (u + 1)`, which is the coefficient category of
`Stacks.EtaleCohomology.smallEtaleSetsBaseChange.{u, 0}`.

## References

* [Stacks Project, Tag 0959](https://stacks.math.columbia.edu/tag/0959)
* [Stacks Project, Tag 0EZR](https://stacks.math.columbia.edu/tag/0EZR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.TwoSquare
open Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe vA uA u

namespace Stacks.EtaleCohomology

/-! ### The two images and the change of coefficients, on Mathlib's small étale sites -/

section Coefficients

variable {S T : Scheme.{u}}

/-- Composition with the forgetful functor of abelian groups, on sheaves of Mathlib's small
étale site of a scheme. -/
private abbrev forgetSheafAt (S : Scheme.{u}) :
    Sheaf (smallEtaleTopology S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (smallEtaleTopology S) (Type (u + 1)) :=
  sheafCompose (smallEtaleTopology S) (forget AddCommGrpCat.{u + 1})

/-- Inverse image of abelian sheaves on Mathlib's small étale sites, built as a left Kan
extension along base change followed by sheafification. -/
private abbrev abPullbackAt (k : T ⟶ S) :
    Sheaf (smallEtaleTopology S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (smallEtaleTopology T) AddCommGrpCat.{u + 1} :=
  Functor.sheafPullbackConstruction.sheafPullback (smallEtaleBaseChange k)
    AddCommGrpCat.{u + 1} (smallEtaleTopology S) (smallEtaleTopology T)

/-- Inverse image of sheaves of sets on Mathlib's small étale sites, built as a left Kan
extension along base change followed by sheafification. This is
`Stacks.EtaleCohomology.smallEtaleInverseImage.{u, 0}`. -/
private abbrev setsPullbackAt (k : T ⟶ S) :
    Sheaf (smallEtaleTopology S) (Type (u + 1)) ⥤ Sheaf (smallEtaleTopology T) (Type (u + 1)) :=
  Functor.sheafPullbackConstruction.sheafPullback (smallEtaleBaseChange k)
    (Type (u + 1)) (smallEtaleTopology S) (smallEtaleTopology T)

/-- The inverse-image/direct-image adjunction for abelian sheaves on Mathlib's small étale
sites. -/
private abbrev abAdjAt (k : T ⟶ S) :
    abPullbackAt k ⊣ smallEtalePushforwardAt k AddCommGrpCat.{u + 1} :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _

/-- The inverse-image/direct-image adjunction for sheaves of sets on Mathlib's small étale
sites. This is `Stacks.EtaleCohomology.smallEtaleSetsAdjunction.{u, 0}`. -/
private abbrev setsAdjAt (k : T ⟶ S) :
    setsPullbackAt k ⊣ smallEtalePushforwardAt k (Type (u + 1)) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _

/-- The comparison of the two composites of an inverse image with the change of coefficients, on
Mathlib's small étale sites. -/
private abbrev pullbackForgetAt (k : T ⟶ S) :
    TwoSquare (forgetSheafAt S) (abPullbackAt k) (setsPullbackAt k) (forgetSheafAt T) :=
  coefficientPullbackTwoSquare (smallEtaleBaseChange k)
    (smallEtaleTopology S) (smallEtaleTopology T) (forget AddCommGrpCat.{u + 1})

/-- **Direct image commutes with the change of coefficients on the nose**: both composites
restrict sections along base change and then forget the group structure. -/
private abbrev pushForgetAt (k : T ⟶ S) :
    smallEtalePushforwardAt k AddCommGrpCat.{u + 1} ⋙ forgetSheafAt S ⟶
      forgetSheafAt T ⋙ smallEtalePushforwardAt k (Type (u + 1)) :=
  𝟙 _

/-- `pushForgetAt` is invertible, being an identity natural transformation. -/
private instance isIso_pushForgetAt (k : T ⟶ S) : IsIso (pushForgetAt k) := by
  change IsIso (𝟙 (smallEtalePushforwardAt k AddCommGrpCat.{u + 1} ⋙ forgetSheafAt S))
  infer_instance

/-- The comparison of `pushForgetAt` read in the other direction. -/
private abbrev pushForgetAt' (k : T ⟶ S) :
    forgetSheafAt T ⋙ smallEtalePushforwardAt k (Type (u + 1)) ⟶
      smallEtalePushforwardAt k AddCommGrpCat.{u + 1} ⋙ forgetSheafAt S :=
  𝟙 _

/-- `pushForgetAt'` is invertible, being an identity natural transformation. -/
private instance isIso_pushForgetAt' (k : T ⟶ S) : IsIso (pushForgetAt' k) := by
  change IsIso (𝟙 (forgetSheafAt T ⋙ smallEtalePushforwardAt k (Type (u + 1))))
  infer_instance

end Coefficients

/-! ### The transfer -/

section Transfer

variable {X X' Y Y' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
  (w : g' ≫ f = f' ≫ g)

/-- **The comparison of the two composite direct images around the square is compatible with the
change of coefficients.** Both sides restrict sections along the component of the comparison
`Stacks.EtaleCohomology.siteSquare` of the two composite base changes of sites, by
`Stacks.EtaleCohomology.smallEtaleSquarePushforwardIsoAt_app`, so the statement is the
compatibility of that restriction with the forgetful functor. -/
private lemma smallEtaleSquarePushforwardIsoAt_forget
    (F : Sheaf (smallEtaleTopology X') AddCommGrpCat.{u + 1}) :
    (smallEtaleSquarePushforwardIsoAt g' f' f g w (Type (u + 1))).hom.app
          ((forgetSheafAt X').obj F) =
      (forgetSheafAt Y).map
        ((smallEtaleSquarePushforwardIsoAt g' f' f g w AddCommGrpCat.{u + 1}).hom.app F) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun VV => ?_))
  obtain ⟨V⟩ := VV
  rw [smallEtaleSquarePushforwardIsoAt_app, sheafCompose_map_hom, Functor.whiskerRight_app,
    smallEtaleSquarePushforwardIsoAt_app]
  rfl

/-- **The cube identity for the change of coefficients.** The comparison of the two composite
direct images around the square at set coefficients, pasted with the comparisons of the two
coefficient categories, is the comparison at abelian coefficients. Every side comparison through
a direct image is an identity, so this is `smallEtaleSquarePushforwardIsoAt_forget` padded with
identities. -/
private lemma coefficient_cube_eq :
    ((mateEquiv (abAdjAt g') (setsAdjAt g') (pullbackForgetAt g') ≫ᵥ
          TwoSquare.mk _ _ _ _
            (smallEtaleSquarePushforwardIsoAt g' f' f g w (Type (u + 1))).hom).whiskerRight
        (pushForgetAt f)).whiskerLeft (pushForgetAt' f') =
      TwoSquare.mk _ _ _ _
          (smallEtaleSquarePushforwardIsoAt g' f' f g w AddCommGrpCat.{u + 1}).hom ≫ᵥ
        mateEquiv (abAdjAt g) (setsAdjAt g) (pullbackForgetAt g) := by
  rw [mateEquiv_coefficientPullbackTwoSquare, mateEquiv_coefficientPullbackTwoSquare]
  refine TwoSquare.ext _ _ fun F => ?_
  rw [AlgebraicGeometry.SmallEtale.ts_whiskerLeft_app,
    AlgebraicGeometry.SmallEtale.ts_whiskerRight_app, AlgebraicGeometry.SmallEtale.ts_vComp_app,
    AlgebraicGeometry.SmallEtale.ts_vComp_app]
  have pad : ∀ {𝒟 : Type _} [Category 𝒟] {X₀ Y₀ : 𝒟} (m n : X₀ ⟶ Y₀) (a b : X₀ ⟶ X₀)
      (c d : Y₀ ⟶ Y₀), m = n → a = 𝟙 X₀ → b = 𝟙 X₀ → c = 𝟙 Y₀ → d = 𝟙 Y₀ →
        (a ≫ b ≫ m) ≫ c = n ≫ d := by
    intro _ _ _ _ m n a b c d h ha hb hc hd
    subst ha hb hc hd h
    simp
  exact pad _ _ _ _ _ _ (smallEtaleSquarePushforwardIsoAt_forget g' f' f g w F) rfl
    (CategoryTheory.Functor.map_id _ _) (CategoryTheory.Functor.map_id _ _) rfl

/-- **The mate of the comparison of the two composite direct images is invertible at abelian
coefficients as soon as it is at set coefficients**, on Mathlib's small étale sites, for an
arbitrary commutative square of schemes.

This is the transport of the cube identity `coefficient_cube_eq` through
`Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms`, whose hypothesis at the
lower-right corner is only that composition with the forgetful functor of abelian groups reflects
isomorphisms. The inverse images are the ones built as a left Kan extension followed by
sheafification. -/
private theorem isIso_mateEquiv_symm_smallEtaleSquarePushforwardIsoAt_ab
    (hsets : IsIso ((mateEquiv (setsAdjAt g') (setsAdjAt g)).symm
      (TwoSquare.mk _ _ _ _
        (smallEtaleSquarePushforwardIsoAt g' f' f g w (Type (u + 1))).hom)).natTrans) :
    IsIso ((mateEquiv (abAdjAt g') (abAdjAt g)).symm
      (TwoSquare.mk _ _ _ _
        (smallEtaleSquarePushforwardIsoAt g' f' f g w AddCommGrpCat.{u + 1}).hom)).natTrans :=
  Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms
    (abAdjAt g') (abAdjAt g) (setsAdjAt g') (setsAdjAt g)
    (pullbackForgetAt g') (pullbackForgetAt g) (pushForgetAt f) (pushForgetAt' f')
    (TwoSquare.mk _ _ _ _
      (smallEtaleSquarePushforwardIsoAt g' f' f g w AddCommGrpCat.{u + 1}).hom)
    (TwoSquare.mk _ _ _ _
      (smallEtaleSquarePushforwardIsoAt g' f' f g w (Type (u + 1))).hom)
    (coefficient_cube_eq g' f' f g w)

/-- **The abelian base change comparison of Mathlib's small étale sites is invertible as soon as
the one for sheaves of sets is.** For a commutative square

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

of schemes, invertibility of `Stacks.EtaleCohomology.smallEtaleSetsBaseChange`, the comparison
`g^{-1} f_* ⟶ f'_* (g')^{-1}` for sheaves of sets on Mathlib's small étale sites, forces
invertibility of `Stacks.EtaleCohomology.smallEtaleBaseChangeAb`, the comparison for abelian
sheaves on the same sites — the one the condition `BC(f, n, q₀)` of [Stacks, Tag 0F02] and the
higher base change maps are built from.

No geometry is used and the square need not be cartesian: both comparisons are mates of the same
identification of the two composite direct images, at the two coefficient categories, and the
transfer between them is the cube
`isIso_mateEquiv_symm_smallEtaleSquarePushforwardIsoAt_ab`. -/
public theorem isIso_smallEtaleBaseChangeAb_of_isIso_smallEtaleSetsBaseChange
    (hsets : IsIso (smallEtaleSetsBaseChange.{u, 0} g' f' f g w)) :
    IsIso (smallEtaleBaseChangeAb g f f' g' w.symm) := by
  have key := isIso_mateEquiv_symm_smallEtaleSquarePushforwardIsoAt_ab g' f' f g w hsets
  have hdef : smallEtaleBaseChangeAb g f f' g' w.symm =
      ((mateEquiv (smallEtaleAdjunctionAb g') (smallEtaleAdjunctionAb g)).symm
        (TwoSquare.mk _ _ _ _
          (smallEtaleSquarePushforwardIsoAt g' f' f g w Ab.{u + 1}).hom)).natTrans := by
    have hmate : smallEtaleBaseChangeAb g f f' g' w.symm =
        Stacks.Cohomology.BaseChange.mate (smallEtaleAdjunctionAb g) (smallEtaleAdjunctionAb g')
          (smallEtalePushforwardAb f) (smallEtalePushforwardAb f')
          ((smallEtalePushforwardAbCompIso g' f).trans
            ((eqToIso (congrArg smallEtalePushforwardAb w.symm.symm)).trans
              (smallEtalePushforwardAbCompIso f' g).symm)) := rfl
    have hiso : ((smallEtalePushforwardAbCompIso g' f).trans
          ((eqToIso (congrArg smallEtalePushforwardAb w.symm.symm)).trans
            (smallEtalePushforwardAbCompIso f' g).symm)).hom =
        (smallEtaleSquarePushforwardIsoAt g' f' f g w Ab.{u + 1}).hom := rfl
    rw [hmate, Stacks.Cohomology.BaseChange.mate_eq_mateEquiv_symm, hiso]
    rfl
  rw [hdef]
  exact Stacks.CategoryTheory.isIso_mateEquiv_symm_of_isIso_mateEquiv_symm
    (abAdjAt g') (smallEtaleAdjunctionAb g') (abAdjAt g) (smallEtaleAdjunctionAb g) _ key

end Transfer

/-! ### The two 2-cells of Mathlib's sites agree -/

section TwoCells

/-- **The named-composite comparison of direct images is the comparison at the written-out
composite, transported along the equation naming it.** This is
`Stacks.EtaleCohomology.smallEtalePushforwardAbCompIso'_eq` at an arbitrary coefficient category:
the tree had it only for the abelian groups of `Ab.{u + 1}`, and the comparison to be identified
here is at sheaves of sets. -/
private lemma smallEtalePushforwardComp'_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) (A : Type uA) [Category.{vA} A] :
    smallEtalePushforwardComp' f g fg hfg A =
      smallEtalePushforwardCompIsoAt f g A ≪≫
        eqToIso (congrArg (fun m : X ⟶ Z => smallEtalePushforwardAt m A) hfg.symm) := by
  subst hfg
  have h : smallEtaleBaseChangeComp' f g (f ≫ g) rfl = smallEtaleBaseChangeComp f g :=
    Iso.ext (by simp [smallEtaleBaseChangeComp'])
  have h1 : smallEtalePushforwardComp' f g (f ≫ g) rfl A =
      smallEtalePushforwardCompIsoAt f g A :=
    congrArg (fun z => Functor.sheafPushforwardContinuousComp' (Iso.symm z) A _ _ _) h
  exact h1.trans (Iso.ext (by simp)).symm

variable (B : BigEtaleSite.{u}) {X X' Y Y' : B.Scheme} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X)
  (f' : X' ⟶ Y') (P : X' ⟶ Y) (hP₁ : g' ≫ f = P) (hP₂ : f' ≫ g = P)

/-- **The comparison of the two composite direct images around the square is the same 2-cell in
the two developments.** `AlgebraicGeometry.SmallEtale.unboundedBaseChangeMate` carries the
diagonal of the square as a named morphism `P`, while
`Stacks.EtaleCohomology.smallEtaleSquarePushforwardIsoAt` writes the two composites out and
transports along the commutativity of the square; the two named-composite comparisons absorb
that transport, which is `smallEtalePushforwardComp'_eq`. -/
public theorem unboundedBaseChangeMate_eq_smallEtaleSquarePushforwardIsoAt (A : Type uA)
    [Category.{vA} A]
    (w : B.inclusion.map g' ≫ B.inclusion.map f = B.inclusion.map f' ≫ B.inclusion.map g) :
    (AlgebraicGeometry.SmallEtale.unboundedBaseChangeMate B A f g g' f' P hP₁ hP₂).natTrans =
      (smallEtaleSquarePushforwardIsoAt (B.inclusion.map g') (B.inclusion.map f')
        (B.inclusion.map f) (B.inclusion.map g) w A).hom := by
  have e : ∀ {V : B.Scheme} (a : X' ⟶ V) (b : V ⟶ Y) (hP : a ≫ b = P),
      AlgebraicGeometry.SmallEtale.unboundedPushforwardCompIso B A a b P hP =
        smallEtalePushforwardComp' (B.inclusion.map a) (B.inclusion.map b) (B.inclusion.map P)
          ((congrArg B.inclusion.map hP.symm).trans (B.inclusion.map_comp a b)) A :=
    fun _ _ _ => rfl
  show (AlgebraicGeometry.SmallEtale.unboundedPushforwardCompIso B A g' f P hP₁).hom ≫
      (AlgebraicGeometry.SmallEtale.unboundedPushforwardCompIso B A f' g P hP₂).inv = _
  rw [e g' f hP₁, e f' g hP₂, smallEtalePushforwardComp'_eq, smallEtalePushforwardComp'_eq,
    smallEtaleSquarePushforwardIsoAt]
  simp

/-- **The base change comparison of sheaves of sets on Mathlib's small étale sites is invertible
exactly when the mate of `AlgebraicGeometry.SmallEtale.unboundedBaseChangeMate` is.**

Both are mates, on the same sites and for the same square, of the comparison of the two composite
direct images — the 2-cells agree by
`unboundedBaseChangeMate_eq_smallEtaleSquarePushforwardIsoAt` — and they are taken along
adjunctions which differ only in their left adjoints, which
`Stacks.CategoryTheory.isIso_mateEquiv_symm_of_isIso_mateEquiv_symm` absorbs. The two
inverse-image/direct-image adjunctions on the left-hand side are therefore arbitrary. -/
public theorem isIso_mateEquiv_symm_unboundedBaseChangeMate_iff
    (w : B.inclusion.map g' ≫ B.inclusion.map f = B.inclusion.map f' ≫ B.inclusion.map g)
    {LUg : Sheaf (Scheme.smallEtaleTopology Y.obj) (Type (u + 1)) ⥤
      Sheaf (Scheme.smallEtaleTopology Y'.obj) (Type (u + 1))}
    {LUg' : Sheaf (Scheme.smallEtaleTopology X.obj) (Type (u + 1)) ⥤
      Sheaf (Scheme.smallEtaleTopology X'.obj) (Type (u + 1))}
    (adjUg : LUg ⊣ AlgebraicGeometry.SmallEtale.unboundedPushforward B (Type (u + 1)) g)
    (adjUg' : LUg' ⊣ AlgebraicGeometry.SmallEtale.unboundedPushforward B (Type (u + 1)) g') :
    IsIso ((mateEquiv adjUg' adjUg).symm
        (AlgebraicGeometry.SmallEtale.unboundedBaseChangeMate B (Type (u + 1)) f g g' f'
          P hP₁ hP₂)).natTrans ↔
      IsIso (smallEtaleSetsBaseChange.{u, 0} (B.inclusion.map g') (B.inclusion.map f')
        (B.inclusion.map f) (B.inclusion.map g) w) := by
  have hcell : AlgebraicGeometry.SmallEtale.unboundedBaseChangeMate B (Type (u + 1)) f g g' f'
        P hP₁ hP₂ =
      TwoSquare.mk _ _ _ _ (smallEtaleSquarePushforwardIsoAt (B.inclusion.map g')
        (B.inclusion.map f') (B.inclusion.map f) (B.inclusion.map g) w (Type (u + 1))).hom :=
    unboundedBaseChangeMate_eq_smallEtaleSquarePushforwardIsoAt B f g g' f' P hP₁ hP₂
      (Type (u + 1)) w
  rw [hcell]
  constructor
  · intro h
    exact Stacks.CategoryTheory.isIso_mateEquiv_symm_of_isIso_mateEquiv_symm
      adjUg' (smallEtaleSetsAdjunction.{u, 0} (B.inclusion.map g'))
      adjUg (smallEtaleSetsAdjunction.{u, 0} (B.inclusion.map g)) _ h
  · intro h
    exact Stacks.CategoryTheory.isIso_mateEquiv_symm_of_isIso_mateEquiv_symm
      (smallEtaleSetsAdjunction.{u, 0} (B.inclusion.map g')) adjUg'
      (smallEtaleSetsAdjunction.{u, 0} (B.inclusion.map g)) adjUg _ h

end TwoCells

/-! ### Transporting a mate back along a change of the four categories -/

section ReverseCube

/-- The component of a horizontal pasting of 2-squares at an object; `private` in
`StacksFrontier.CategoryTheory.Adjunction.MatesChangeOfCategories`, so it is re-derived here. -/
private theorem hComp_natTrans_app {C₁ C₂ C₃ C₄ C₅ C₆ : Type*} [Category* C₁] [Category* C₂]
    [Category* C₃] [Category* C₄] [Category* C₅] [Category* C₆]
    {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {Bo : C₃ ⥤ C₄}
    {T' : C₂ ⥤ C₅} {R' : C₅ ⥤ C₆} {B' : C₄ ⥤ C₆}
    (w : TwoSquare T L R Bo) (w' : TwoSquare T' R R' B') (c : C₁) :
    (w ≫ₕ w').natTrans.app c = w'.natTrans.app (T.obj c) ≫ B'.map (w.natTrans.app c) := by
  simp [TwoSquare.hComp]

/-- A horizontal pasting of two invertible 2-squares is invertible; `private` in
`StacksFrontier.CategoryTheory.Adjunction.MatesChangeOfCategories`, so it is re-derived here. -/
private theorem isIso_hComp_natTrans {C₁ C₂ C₃ C₄ C₅ C₆ : Type*} [Category* C₁] [Category* C₂]
    [Category* C₃] [Category* C₄] [Category* C₅] [Category* C₆]
    {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {Bo : C₃ ⥤ C₄}
    {T' : C₂ ⥤ C₅} {R' : C₅ ⥤ C₆} {B' : C₄ ⥤ C₆}
    (w : TwoSquare T L R Bo) (w' : TwoSquare T' R R' B')
    [IsIso w.natTrans] [IsIso w'.natTrans] : IsIso (w ≫ₕ w').natTrans := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro c
  rw [hComp_natTrans_app]
  infer_instance

/-- The transformation of a 2-square whiskered at the top and at the bottom. -/
private theorem whiskerTop_whiskerBottom_natTrans {C₁ C₂ C₃ C₄ : Type*} [Category* C₁]
    [Category* C₂] [Category* C₃] [Category* C₄] {T T' : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄}
    {Bo Bo' : C₃ ⥤ C₄} (w : TwoSquare T' L R Bo) (φ : T ⟶ T') (ψ : Bo ⟶ Bo') :
    ((w.whiskerTop φ).whiskerBottom ψ).natTrans =
      (Functor.whiskerRight φ R ≫ w.natTrans) ≫ Functor.whiskerLeft L ψ :=
  rfl

/-- **A natural transformation whose components are invertible at every object in the image of
an essentially surjective functor is invertible.** Every object of the target is isomorphic to
one in the image, and invertibility of a component transports along such an isomorphism by
naturality. -/
private theorem isIso_natTrans_of_essSurj {C C' D : Type*} [Category* C] [Category* C']
    [Category* D] (Φ : C ⥤ C') [Φ.EssSurj] {Fn Gn : C' ⥤ D} (m : Fn ⟶ Gn)
    (h : ∀ c : C, IsIso (m.app (Φ.obj c))) : IsIso m := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro d
  have := h (Φ.objPreimage d)
  have he : Φ.obj (Φ.objPreimage d) ≅ d := Φ.objObjPreimageIso d
  have hnat : m.app d = Fn.map he.inv ≫ m.app (Φ.obj (Φ.objPreimage d)) ≫ Gn.map he.hom := by
    rw [← m.naturality he.hom, ← Category.assoc, ← Fn.map_comp, he.inv_hom_id, Fn.map_id,
      Category.id_comp]
  rw [hnat]
  infer_instance

variable {C D E F C' D' E' F' : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
  [Category* C'] [Category* D'] [Category* E'] [Category* F']
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  {L₁' : C' ⥤ D'} {R₁' : D' ⥤ C'} {L₂' : E' ⥤ F'} {R₂' : F' ⥤ E'}
  {G : C ⥤ E} {H : D ⥤ F} {G' : C' ⥤ E'} {H' : D' ⥤ F'}
  {ΦC : C ⥤ C'} {ΦD : D ⥤ D'} {ΦE : E ⥤ E'} {ΦF : F ⥤ F'}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₁' : L₁' ⊣ R₁') (adj₂' : L₂' ⊣ R₂')
  (τ₁ : TwoSquare ΦC L₁ L₁' ΦD) (τ₂ : TwoSquare ΦE L₂ L₂' ΦF)
  (σG : G ⋙ ΦE ⟶ ΦC ⋙ G') (σH : ΦD ⋙ H' ⟶ H ⋙ ΦF)
  (β : TwoSquare R₁ H G R₂) (β' : TwoSquare R₁' H' G' R₂')

/-- **Invertibility of a mate transports backwards along a change of the four categories of its
square**, from the front face to the back face, when the functor `ΦC` at the upper-left corner
is essentially surjective.

This is `Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms` read in the other
direction, and it is read off from the same cube identity
`Stacks.CategoryTheory.mateEquiv_symm_hComp_eq`: the left-hand side of that identity is
invertible, so the right-hand side is, and peeling off the two whiskerings and the invertible
pasting with `τ₁` leaves the components of the mate of `β'` at the objects `ΦC.obj c`
invertible. Essential surjectivity of `ΦC` upgrades that to invertibility.

The tree has only the forward transport; both directions are needed when the two squares are
two presentations of one site, where the comparisons are halves of an equivalence. -/
private theorem isIso_mateEquiv_symm_of_essSurj [ΦC.EssSurj]
    [IsIso τ₁.natTrans] [IsIso τ₂.natTrans] [IsIso σG] [IsIso σH]
    [IsIso ((mateEquiv adj₁ adj₂).symm β).natTrans]
    (h : ((mateEquiv adj₁ adj₁' τ₁ ≫ᵥ β').whiskerRight σG).whiskerLeft σH =
      β ≫ᵥ mateEquiv adj₂ adj₂' τ₂) :
    IsIso ((mateEquiv adj₁' adj₂').symm β').natTrans := by
  have hl : IsIso ((mateEquiv adj₁ adj₂).symm β ≫ₕ τ₂).natTrans :=
    isIso_hComp_natTrans _ _
  rw [Stacks.CategoryTheory.mateEquiv_symm_hComp_eq adj₁ adj₂ adj₁' adj₂' τ₁ τ₂ σG σH β β' h,
    whiskerTop_whiskerBottom_natTrans] at hl
  have hmid : IsIso (Functor.whiskerRight σG L₂' ≫
      (τ₁ ≫ₕ (mateEquiv adj₁' adj₂').symm β').natTrans) :=
    IsIso.of_isIso_comp_right _ (Functor.whiskerLeft L₁ σH)
  have htop : IsIso (τ₁ ≫ₕ (mateEquiv adj₁' adj₂').symm β').natTrans :=
    IsIso.of_isIso_comp_left (Functor.whiskerRight σG L₂') _
  refine isIso_natTrans_of_essSurj ΦC _ fun c => ?_
  have hc : IsIso ((τ₁ ≫ₕ (mateEquiv adj₁' adj₂').symm β').natTrans.app c) := inferInstance
  rw [hComp_natTrans_app] at hc
  exact IsIso.of_isIso_comp_right _ (H'.map (τ₁.natTrans.app c))

end ReverseCube

/-! ### The converse site transfer for sheaves of sets -/

section SiteTransfer

variable (B : BigEtaleSite.{u}) {X X' Y Y' : B.Scheme} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X)
  (f' : X' ⟶ Y')

/-- **The base change comparison for sheaves of sets passes from Mathlib's small étale sites back
to the size-bounded sites of Stacks 021B.** For a commutative square

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

of the underlying category of a big étale site, invertibility of the base change comparison on
Mathlib's sites — the mate of `AlgebraicGeometry.SmallEtale.unboundedBaseChangeMate`, for any
choice of left adjoints of the two direct images — forces invertibility of
`AlgebraicGeometry.smallEtaleBaseChangeNatTrans`, the comparison on the bounded sites.

This is the converse of
`AlgebraicGeometry.SmallEtale.isIso_mateEquiv_symm_unboundedBaseChangeMate_of_isIso`, read off
from the same cube identity `AlgebraicGeometry.SmallEtale.baseChangeMate_cube_eq` through
`isIso_mateEquiv_symm_of_essSurj`: every side comparison of that cube is an isomorphism, and the
functor at the corner that has to be essentially surjective is restriction along the embedding
of the bounded site of `X`, one half of the equivalence
`AlgebraicGeometry.SmallEtale.sheafEquiv`. No geometry is used. -/
public theorem isIso_smallEtaleBaseChangeNatTrans_of_isIso_mateEquiv_symm
    (h : g' ≫ f = f' ≫ g) (P : X' ⟶ Y) (hP₁ : g' ≫ f = P) (hP₂ : f' ≫ g = P)
    {LUg : Sheaf (Scheme.smallEtaleTopology Y.obj) (Type (u + 1)) ⥤
      Sheaf (Scheme.smallEtaleTopology Y'.obj) (Type (u + 1))}
    {LUg' : Sheaf (Scheme.smallEtaleTopology X.obj) (Type (u + 1)) ⥤
      Sheaf (Scheme.smallEtaleTopology X'.obj) (Type (u + 1))}
    (adjUg : LUg ⊣ AlgebraicGeometry.SmallEtale.unboundedPushforward B (Type (u + 1)) g)
    (adjUg' : LUg' ⊣ AlgebraicGeometry.SmallEtale.unboundedPushforward B (Type (u + 1)) g')
    (hunb : IsIso ((mateEquiv adjUg' adjUg).symm
      (AlgebraicGeometry.SmallEtale.unboundedBaseChangeMate B (Type (u + 1)) f g g' f'
        P hP₁ hP₂)).natTrans) :
    IsIso (AlgebraicGeometry.smallEtaleBaseChangeNatTrans B g' f' f g h) := by
  have hEq : ((AlgebraicGeometry.SmallEtale.toEtaleSite B X.obj X.property
      ).sheafPushforwardContinuous (Type (u + 1))
      (AlgebraicGeometry.SmallEtale.topology B X.obj X.property)
      X.obj.smallEtaleTopology).IsEquivalence :=
    (AlgebraicGeometry.SmallEtale.sheafEquiv B X.obj X.property
      (Type (u + 1))).isEquivalence_inverse
  have key : IsIso ((mateEquiv (B.smallPullbackAdjunction g' (Type (u + 1)))
        (B.smallPullbackAdjunction g (Type (u + 1)))).symm
      (AlgebraicGeometry.SmallEtale.boundedBaseChangeMate B (Type (u + 1)) f g g' f'
        P hP₁ hP₂)).natTrans :=
    isIso_mateEquiv_symm_of_essSurj adjUg' adjUg
      (B.smallPullbackAdjunction g' (Type (u + 1))) (B.smallPullbackAdjunction g (Type (u + 1)))
      (AlgebraicGeometry.SmallEtale.restrictionPullbackBaseChange B (Type (u + 1)) g' adjUg' _)
      (AlgebraicGeometry.SmallEtale.restrictionPullbackBaseChange B (Type (u + 1)) g adjUg _)
      (AlgebraicGeometry.SmallEtale.toEtaleSitePushforwardBaseChangeIso B f (Type (u + 1))).hom
      (AlgebraicGeometry.SmallEtale.toEtaleSitePushforwardBaseChangeIso B f' (Type (u + 1))).inv
      (AlgebraicGeometry.SmallEtale.unboundedBaseChangeMate B (Type (u + 1)) f g g' f' P hP₁ hP₂)
      (AlgebraicGeometry.SmallEtale.boundedBaseChangeMate B (Type (u + 1)) f g g' f' P hP₁ hP₂)
      (AlgebraicGeometry.SmallEtale.baseChangeMate_cube_eq B (Type (u + 1)) f g g' f'
        P hP₁ hP₂ adjUg _ adjUg' _)
  rw [← AlgebraicGeometry.SmallEtale.smallEtaleBaseChangeMate_eq_boundedBaseChangeMate
    B f g g' f' h P hP₁ hP₂] at key
  exact key

end SiteTransfer

end Stacks.EtaleCohomology

end
