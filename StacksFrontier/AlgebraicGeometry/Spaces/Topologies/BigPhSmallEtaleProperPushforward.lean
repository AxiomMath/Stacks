module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigPhSmallEtalePullbackSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigPhToSmallEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.ProperBaseChangeUnconditional
public import StacksFrontier.CategoryTheory.Sites.PushforwardFullyFaithful

/-!
# Inverse image to the big ph topos and direct image along a proper morphism (Stacks 0DGX (1))

Let `P` be a big ph site and `E` a big étale site of algebraic spaces over `S` built on the same
big fppf site, and let `f : Y ⟶ X` be a morphism of algebraic spaces. The comparison morphism
`a = π ∘ ε` of **Stacks 0DGW** from the big ph topos to the small étale topos gives a canonical
base change map `f_{small,*} ⋙ a_X⁻¹ ⟶ a_Y⁻¹ ⋙ f_{big,ph,*}`, the mate of the commutative square
`a_{X,*} ∘ f_{big,ph,*} = f_{small,*} ∘ a_{Y,*}`. Stacks 0DGX, part (1), says that it is an
isomorphism when `f` is proper.

## Main definitions

* `AlgebraicGeometry.BigPHSpaceSite.phToSmallEtaleSquare`: the square of direct images, pasted
  from the big ph–big étale square of Stacks 0DGW and the big–small étale square of Stacks 0DF6.
* `AlgebraicGeometry.BigPHSpaceSite.phToSmallEtaleBaseChange`: its mate, the base change map.

## Main results

* `AlgebraicGeometry.BigPHSpaceSite.phToSmallEtaleBaseChange_eq_vComp`: the base change map is the
  étale base change map of Stacks 0DGD followed by the mate of the big ph–big étale square.
* `AlgebraicGeometry.BigPHSpaceSite.isIso_phToSmallEtaleBaseChange_app_of_isIso_unit`: for `f`
  proper, the base change map is invertible at `F` as soon as the unit of `ε_Y` is invertible at
  `π_Y⁻¹ F`.
* `AlgebraicGeometry.BigPHSpaceSite.phToSmallEtalePushforwardIsoOfIsProper`: **Stacks 0DGX, part
  (1)**, `a_X⁻¹ ∘ f_{small,*} ≅ f_{big,ph,*} ∘ a_Y⁻¹` for `f` proper.

## Implementation notes

The source deduces part (1) from Stacks 0DGD, part (1), and Stacks 0DGT, part (1): `ε_{Y,*}`
reflects isomorphisms and `ε_* a⁻¹ = π⁻¹`. Here the same two inputs enter through the mates
calculus. Since `a = π ∘ ε` by definition, the mate across the composite adjunctions of the pasted
square is the vertical pasting of the two mates (`CategoryTheory.mateEquiv_hcomp`). The first is
the étale base change map `π_X⁻¹ ∘ f_{small,*} ⟶ f_{big,*} ∘ π_Y⁻¹`, invertible for `f` proper by
Stacks 0DGD (1). The second, the mate `f_{big,*} ⋙ ε_X⁻¹ ⟶ ε_Y⁻¹ ⋙ f_{big,ph,*}` of the big
square, is invertible at a sheaf `M` as soon as the unit of `ε_Y` is invertible at `M`: the counit
of `ε_X` is invertible because `ε_{X,*}` is fully faithful (a ph sheaf is an étale sheaf, and a map
of ph sheaves is a map of étale sheaves). At `M = π_Y⁻¹ F` that unit is invertible by Stacks 0DGT,
part (1).

The big étale direct image is used in the form of restriction along `Over.pullback`, as in the
Stacks 0DGD development, and identified with the direct image of the big étale morphism of
Stacks 0DF5 by `CategoryTheory.StacksRelocalization.sheafPushforwardOverMapIso`.

## References

* [Stacks Project, Tag 0DGX](https://stacks.math.columbia.edu/tag/0DGX)
* [Stacks Project, Tag 0DGW](https://stacks.math.columbia.edu/tag/0DGW)
* [Stacks Project, Tag 0DGD](https://stacks.math.columbia.edu/tag/0DGD)
* [Stacks Project, Tag 0DGT](https://stacks.math.columbia.edu/tag/0DGT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TwoSquare

universe u

namespace CategoryTheory

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C} {G : A ⥤ C} {H : B ⥤ D}

/-- **A mate is invertible at an object where the source unit is invertible**, for an invertible
square and an invertible target counit: the component of the mate `G ⋙ L₂ ⟶ L₁ ⋙ H` at `c` is
`L₂` of `G` of the unit at `c`, followed by `L₂` of the square at `L₁ c` and the counit at
`H (L₁ c)`. -/
theorem isIso_mateEquiv_symm_app_of_isIso_unit_app (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (θ : TwoSquare R₁ H G R₂) [IsIso θ.natTrans] [IsIso adj₂.counit] (c : A)
    [IsIso (adj₁.unit.app c)] :
    IsIso (((mateEquiv adj₁ adj₂).symm θ).natTrans.app c) := by
  simp only [mateEquiv, Equiv.coe_fn_symm_mk]
  dsimp
  infer_instance

end CategoryTheory

namespace AlgebraicGeometry.BigPHSpaceSite

variable {S : Scheme.{u}} (P : BigPHSpaceSite S) (E : BigEtaleSpaceSite S)
  (h : P.fppfSite = E.fppfSite)

/-- The counit of the change-of-topology morphism `ε_X` is invertible: its direct image is
restriction along the inverse of an equivalence of slice categories, whose left adjoint is fully
faithful, so the direct image is fully faithful (a ph sheaf is an étale sheaf, and maps of ph
sheaves are the maps of the underlying étale sheaves). -/
instance isIso_phToBigEtaleMorphism_counit (X : P.Spaces) :
    IsIso (phToBigEtaleMorphism P E h X).adj.counit :=
  letI := phToBigEtale_isContinuous P E h X
  Functor.isIso_counit_of_fullyFaithful_leftAdjoint (Type (u + 1))
    (Over.postEquiv (canonicalSpaceEquivalence P E h).1 (X := X)).inverse
    (Over.postEquiv (canonicalSpaceEquivalence P E h).1 (X := X)).toAdjunction
    (E.bigEtaleTopology (etaleSpace P E h X)) (BigPHSpaceOver.topology P X)
    (phToBigEtaleMorphism P E h X).adj

variable {X Y : P.Spaces} (f : Y ⟶ X)

/-- A proper morphism of algebraic spaces of the big ph site stays proper when read in the big
étale site built on the same big fppf site of schemes: the two categories of algebraic spaces are
the same. -/
theorem isProper_etaleMap (hf : Space.IsProper P.fppfSite S P.fppf_mem f.hom) :
    Space.IsProper E.fppfSite S E.fppf_mem (etaleMap P E h f).hom := by
  cases P
  cases E
  cases h
  exact hf

/-- The big ph–big étale square of **Stacks 0DGW**, with the big étale direct image along `f`
written as restriction along `Over.pullback`: `ε_{Y,*} ⋙ f_{big,*} ≅ f_{big,ph,*} ⋙ ε_{X,*}`. -/
def phToBigEtaleSquare :
    (phToBigEtaleMorphism P E h Y).pushforward ⋙
        (Over.pullback (etaleMap P E h f)).sheafPushforwardContinuous (Type (u + 1))
          (E.bigEtaleTopology (etaleSpace P E h X)) (E.bigEtaleTopology (etaleSpace P E h Y)) ≅
      (bigPHMorphism P f).pushforward ⋙ (phToBigEtaleMorphism P E h X).pushforward :=
  Functor.isoWhiskerLeft (phToBigEtaleMorphism P E h Y).pushforward
      (StacksRelocalization.sheafPushforwardOverMapIso E.topology (etaleMap P E h f)).symm ≪≫
    bigPHBigEtale_pushforwardCommIso P E h f

/-- **The square of direct images of Stacks 0DGW for the comparison morphisms `a = π ∘ ε`**:
`a_{Y,*} ⋙ f_{small,*} ⟶ f_{big,ph,*} ⋙ a_{X,*}`, the horizontal pasting of the big ph–big étale
square `AlgebraicGeometry.BigPHSpaceSite.phToBigEtaleSquare` with the big–small étale square of
Stacks 0DF6 (`AlgebraicGeometry.BigEtaleSpaceSite.bigSmallEtalePullbackSquare`). -/
def phToSmallEtaleSquare :
    TwoSquare (phToSmallEtaleMorphism P E h Y).pushforward (bigPHMorphism P f).pushforward
      (E.smallEtaleMorphism (etaleMap P E h f)).pushforward
      (phToSmallEtaleMorphism P E h X).pushforward :=
  TwoSquare.mk _ _ _ _ (phToBigEtaleSquare P E h f).hom ≫ₕ
    TwoSquare.mk _ _ _ _ (E.bigSmallEtalePullbackSquare (etaleMap P E h f)).hom

/-- **The base change map of Stacks 0DGX (1)**, `f_{small,*} ⋙ a_X⁻¹ ⟶ a_Y⁻¹ ⋙ f_{big,ph,*}`: the
mate of the square of direct images `AlgebraicGeometry.BigPHSpaceSite.phToSmallEtaleSquare`
across the adjunctions `a_Y⁻¹ ⊣ a_{Y,*}` and `a_X⁻¹ ⊣ a_{X,*}`. -/
def phToSmallEtaleBaseChange :
    (E.smallEtaleMorphism (etaleMap P E h f)).pushforward ⋙
        (phToSmallEtaleMorphism P E h X).inverseImage ⟶
      (phToSmallEtaleMorphism P E h Y).inverseImage ⋙ (bigPHMorphism P f).pushforward :=
  ((mateEquiv (phToSmallEtaleMorphism P E h Y).adj (phToSmallEtaleMorphism P E h X).adj).symm
    (phToSmallEtaleSquare P E h f)).natTrans

/-- The mate `f_{big,*} ⋙ ε_X⁻¹ ⟶ ε_Y⁻¹ ⋙ f_{big,ph,*}` of the big ph–big étale square. -/
def phToBigEtaleBaseChange :
    TwoSquare ((Over.pullback (etaleMap P E h f)).sheafPushforwardContinuous (Type (u + 1))
          (E.bigEtaleTopology (etaleSpace P E h X)) (E.bigEtaleTopology (etaleSpace P E h Y)))
      (phToBigEtaleMorphism P E h Y).inverseImage (phToBigEtaleMorphism P E h X).inverseImage
      (bigPHMorphism P f).pushforward :=
  (mateEquiv (phToBigEtaleMorphism P E h Y).adj (phToBigEtaleMorphism P E h X).adj).symm
    (TwoSquare.mk _ _ _ _ (phToBigEtaleSquare P E h f).hom)

/-- **The base change map is the étale one followed by the big ph–big étale one.** Since
`a = π ∘ ε`, the mate across the composite adjunctions of the horizontally pasted square is the
vertical pasting of the two mates (`CategoryTheory.mateEquiv_hcomp`): the étale base change map
`π_X⁻¹ ∘ f_{small,*} ⟶ f_{big,*} ∘ π_Y⁻¹` of Stacks 0DGD, then
`AlgebraicGeometry.BigPHSpaceSite.phToBigEtaleBaseChange`. -/
theorem phToSmallEtaleBaseChange_eq_vComp :
    (mateEquiv ((E.bigToSmallEtaleMorphism (etaleSpace P E h Y)).adj.comp
        (phToBigEtaleMorphism P E h Y).adj)
      ((E.bigToSmallEtaleMorphism (etaleSpace P E h X)).adj.comp
        (phToBigEtaleMorphism P E h X).adj)).symm (phToSmallEtaleSquare P E h f) =
      TwoSquare.mk _ _ _ _ (E.bigToSmallEtaleBaseChange (etaleMap P E h f)) ≫ᵥ
        phToBigEtaleBaseChange P E h f := by
  refine (Equiv.symm_apply_eq _).2 ?_
  rw [mateEquiv_hcomp, show TwoSquare.mk _ _ _ _ (E.bigToSmallEtaleBaseChange (etaleMap P E h f)) =
      (mateEquiv (E.bigToSmallEtaleMorphism (etaleSpace P E h Y)).adj
        (E.bigToSmallEtaleMorphism (etaleSpace P E h X)).adj).symm
        (TwoSquare.mk _ _ _ _ (E.bigSmallEtalePullbackSquare (etaleMap P E h f)).hom) from rfl]
  simp only [phToBigEtaleBaseChange, Equiv.apply_symm_apply]
  rfl

/-- **Stacks 0DGX (1) at a sheaf, from the unit of `ε_Y`.** Let `f : Y ⟶ X` be proper. The base
change map `f_{small,*} ⋙ a_X⁻¹ ⟶ a_Y⁻¹ ⋙ f_{big,ph,*}` is invertible at a sheaf `F` on the small
étale site of `Y` as soon as the unit of `ε_Y` is invertible at `π_Y⁻¹ F`; Stacks 0DGT, part (1),
says that it is, `π_Y⁻¹ F` being a ph sheaf. -/
theorem isIso_phToSmallEtaleBaseChange_app_of_isIso_unit
    (hf : Space.IsProper E.fppfSite S E.fppf_mem (etaleMap P E h f).hom)
    (F : Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace P E h Y))
      (Type (u + 1)))
    [IsIso ((phToBigEtaleMorphism P E h Y).adj.unit.app
      ((E.bigToSmallEtaleMorphism (etaleSpace P E h Y)).inverseImage.obj F))] :
    IsIso ((phToSmallEtaleBaseChange P E h f).app F) := by
  have e := congrArg (fun w : TwoSquare _ _ _ _ ↦ w.natTrans.app F)
    (phToSmallEtaleBaseChange_eq_vComp P E h f)
  show IsIso (((mateEquiv ((E.bigToSmallEtaleMorphism (etaleSpace P E h Y)).adj.comp
        (phToBigEtaleMorphism P E h Y).adj)
      ((E.bigToSmallEtaleMorphism (etaleSpace P E h X)).adj.comp
        (phToBigEtaleMorphism P E h X).adj)).symm (phToSmallEtaleSquare P E h f)).natTrans.app F)
  rw [e]
  have := BigEtaleSpaceSite.isIso_bigToSmallEtaleBaseChange_of_isProper E (etaleMap P E h f) hf
  have : IsIso ((phToBigEtaleBaseChange P E h f).natTrans.app
      ((E.bigToSmallEtaleMorphism (etaleSpace P E h Y)).inverseImage.obj F)) :=
    isIso_mateEquiv_symm_app_of_isIso_unit_app _ _ _ _
  simp only [TwoSquare.vComp, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.id_comp, Category.comp_id]
  infer_instance

/-- **Stacks 0DGX (1), as invertibility of the base change map.** For a proper morphism
`f : Y ⟶ X` of algebraic spaces, the canonical base change map
`f_{small,*} ⋙ a_X⁻¹ ⟶ a_Y⁻¹ ⋙ f_{big,ph,*}` is an isomorphism: at every sheaf `F` the unit of
`ε_Y` is invertible at `π_Y⁻¹ F` (Stacks 0DGT, part (1),
`AlgebraicGeometry.BigPHSpaceSite.isIso_phToBigEtale_unit_app_inverseImage`), and
`AlgebraicGeometry.BigPHSpaceSite.isIso_phToSmallEtaleBaseChange_app_of_isIso_unit` applies. -/
theorem isIso_phToSmallEtaleBaseChange_of_isProper
    (hf : Space.IsProper P.fppfSite S P.fppf_mem f.hom) :
    IsIso (phToSmallEtaleBaseChange P E h f) := by
  have hf' := isProper_etaleMap P E h f hf
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  have := isIso_phToBigEtale_unit_app_inverseImage P E h Y F
  exact isIso_phToSmallEtaleBaseChange_app_of_isIso_unit P E h f hf' F

/-- **Stacks 0DGX, part (1).** Let `f : Y ⟶ X` be a proper morphism of algebraic spaces over `S`,
and let `a = π ∘ ε` be the comparison morphisms from the big ph topoi to the small étale topoi of
Stacks 0DGW. Then `a_X⁻¹ ∘ f_{small,*} = f_{big,ph,*} ∘ a_Y⁻¹` as functors from sheaves on the
small étale site of `Y` to sheaves on the big ph site of `X`: the canonical base change map
`AlgebraicGeometry.BigPHSpaceSite.phToSmallEtaleBaseChange`, the mate of the commutative square of
Stacks 0DGW, is an isomorphism. -/
@[stacks 0DGX "(1)"]
def phToSmallEtalePushforwardIsoOfIsProper
    (hf : Space.IsProper P.fppfSite S P.fppf_mem f.hom) :
    (E.smallEtaleMorphism (etaleMap P E h f)).pushforward ⋙
        (phToSmallEtaleMorphism P E h X).inverseImage ≅
      (phToSmallEtaleMorphism P E h Y).inverseImage ⋙ (bigPHMorphism P f).pushforward :=
  haveI := isIso_phToSmallEtaleBaseChange_of_isProper P E h f hf
  asIso (phToSmallEtaleBaseChange P E h f)

end AlgebraicGeometry.BigPHSpaceSite

end
