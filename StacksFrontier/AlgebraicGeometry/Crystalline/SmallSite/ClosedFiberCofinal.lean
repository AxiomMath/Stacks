module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.BinaryProductRestrict
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.StructureMorphism

/-!
# The closed fibre site is right-adjointable over the small Zariski site

Fix a global crystalline situation `(p, (S, I, γ), X)` with `p` locally nilpotent on the closed
fibre `S₀ = V(I)`, and assume moreover that the closed fibre inclusion `S₀ ↪ S` is itself a
thickening — by [Stacks, Tag 07GR] this holds as soon as `p` is locally nilpotent on `S`, see
`Crystalline.DividedPowerScheme.isThickening_closedFiberι_of_isNilpotent_natCast`.  Then the
triple `(S₀, S, γ)` is a *terminal* object of `Cris(S₀/S)`,
`Crystalline.GlobalCrystallineSituation.isTerminal_closedFiberCrystallineThickening`.

This file upgrades terminality to the statement it is really wanted for: the forgetful functor
`Cris(S₀/S) ⥤ S₀_Zar` of [Stacks, Tag 07IH] has a *right adjoint*, namely `V ↦ (V, S|_V, γ)`, the
restriction of the terminal object to the open of `S` matching `V`.  Restriction to an open is
`Crystalline.GlobalCrystallineSituation.Thickening.restrictOpen`, and the open of `S` matching `V`
is supplied by the homeomorphism of the thickening `S₀ ↪ S`.

The adjunction is what collapses the right Kan extension computing the direct image along
`u_{S₀/S}` of [Stacks, Tag 07IL] to a plain restriction: by [Stacks, Tag 00XX] (1) the sheaf
pushforward along a cocontinuous functor with a right adjoint is the sheaf pushforward along that
right adjoint.  Note that the upper square of [Stacks, Tag 07IM] does *not* turn on this
computation: `Crystalline.GlobalCrystallineSituation.closedFiberCrisUpperSquare` of
`SmallSite/UpperSquare.lean` proves it at the remark's own hypotheses, with no assumption on `I`,
by the covering-local route of `SmallSite/CrisZariskiSquare{Covering, Limit, Iso}.lean`.  What is
below is the shape the site takes when `p` is nilpotent on the base, which is strictly more than
the standing hypotheses give.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.closedFiberRestrict` — the object `(V, S|_V, γ)` of
  `CRIS(S₀/S)`, the terminal object restricted to the open of `S` matching `V ⊆ S₀`.
* `Crystalline.GlobalCrystallineSituation.closedFiberRestrictFunctor` and
  `Crystalline.GlobalCrystallineSituation.closedFiberRestrictCris` — its functoriality in `V`,
  into `CRIS(S₀/S)` and into `Cris(S₀/S)`.
* `Crystalline.GlobalCrystallineSituation.forgetToOpensClosedFiberAdjunction` — the forgetful
  functor `Cris(S₀/S) ⥤ S₀_Zar` is left adjoint to `V ↦ (V, S|_V, γ)`.

## Main results

* `Crystalline.GlobalCrystallineSituation.range_toBase_subset_closedFiberOpen_iff` — an object of
  `CRIS(S₀/S)` has ambient scheme mapping into the open of `S` matching `V` exactly when its
  thickened scheme maps into `V`.
* `Crystalline.GlobalCrystallineSituation.subsingleton_hom_closedFiberRestrict` and
  `Crystalline.GlobalCrystallineSituation.nonempty_hom_closedFiberRestrict_iff` — the hom-sets
  into `(V, S|_V, γ)` have at most one element, and are nonempty exactly under that condition.
* `Crystalline.GlobalCrystallineSituation.closedFiberRestrictCris_isContinuous` — the right
  adjoint is a continuous functor of sites.

## References

* [Stacks Project, Tag 07IM](https://stacks.math.columbia.edu/tag/07IM)
* [Stacks Project, Tag 07IL](https://stacks.math.columbia.edu/tag/07IL)
* [Stacks Project, Tag 07IH](https://stacks.math.columbia.edu/tag/07IH)
* [Stacks Project, Tag 00XX](https://stacks.math.columbia.edu/tag/00XX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.Thickenings

universe u

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

/-- The open of `S` matching an open of the closed fibre `S₀`, under the homeomorphism of the
thickening `S₀ ↪ S`. -/
def closedFiberOpen (hthick : IsThickening (DividedPowerScheme.closedFiberι S.S))
    (V : (DividedPowerScheme.closedFiber S.S).Opens) : S.S.scheme.Opens :=
  Stacks.Thickenings.IsThickening.opensCongr hthick V

/-- The preimage under `S₀ ↪ S` of the open of `S` matching an open `V` of `S₀` is `V`. -/
@[simp]
theorem preimage_closedFiberOpen (hthick : IsThickening (DividedPowerScheme.closedFiberι S.S))
    (V : (DividedPowerScheme.closedFiber S.S).Opens) :
    DividedPowerScheme.closedFiberι S.S ⁻¹ᵁ closedFiberOpen hthick V = V :=
  Stacks.Thickenings.IsThickening.preimage_opensCongr hthick V

section

variable (hlocnil : ∀ x : DividedPowerScheme.closedFiber S.S,
    IsNilpotent (S.p : (DividedPowerScheme.closedFiber S.S).presheaf.stalk x))

/-- **The structure maps of an object of `CRIS(S₀/S)` agree on points.**  The square of the
object's compatibility with the base commutes, and the structure morphism of the closed fibre
situation is the identity. -/
theorem toBase_immersion_apply (B : Thickening (closedFiberSituation S hlocnil))
    (y : B.thickening.source) :
    B.toBase.hom.base (B.thickening.immersion.base y) =
      (DividedPowerScheme.closedFiberι S.S).base (B.toX.base y) := by
  have h2 : B.thickening.immersion ≫ B.toBase.hom =
      B.toX ≫ DividedPowerScheme.closedFiberι S.S := by
    rw [B.over_base]
    simp [sourceToBase]
  simpa using congrArg (fun k : B.thickening.source ⟶ S.S.scheme ↦ k.base y) h2

/-- **The two readings of "an object of `CRIS(S₀/S)` lies over an open `V` of `S₀`" agree.**  The
ambient scheme of the object maps into the open of `S` matching `V` exactly when its thickened
scheme maps into `V`: the immersion of a thickening is surjective, so the image of the ambient
scheme is the image of the thickened scheme under `S₀ ↪ S`, and `V` is the preimage of the open
matching it. -/
theorem range_toBase_subset_closedFiberOpen_iff
    (hthick : IsThickening (DividedPowerScheme.closedFiberι S.S))
    (B : Thickening (closedFiberSituation S hlocnil))
    (V : (DividedPowerScheme.closedFiber S.S).Opens) :
    Set.range B.toBase.hom.base ⊆ (closedFiberOpen hthick V : Set S.S.scheme) ↔
      Set.range B.toX.base ⊆ (V : Set (DividedPowerScheme.closedFiber S.S)) := by
  constructor
  · rintro h _ ⟨y, rfl⟩
    have hy : (DividedPowerScheme.closedFiberι S.S).base (B.toX.base y) ∈
        closedFiberOpen hthick V := by
      rw [← toBase_immersion_apply hlocnil B y]
      exact h ⟨_, rfl⟩
    have : B.toX.base y ∈ DividedPowerScheme.closedFiberι S.S ⁻¹ᵁ closedFiberOpen hthick V := hy
    rwa [preimage_closedFiberOpen] at this
  · rintro h _ ⟨t, rfl⟩
    obtain ⟨y, rfl⟩ := B.thickening.isThickening.2 t
    rw [toBase_immersion_apply hlocnil B y]
    rw [← preimage_closedFiberOpen hthick V] at h
    exact h ⟨y, rfl⟩

variable (hthick : IsThickening (DividedPowerScheme.closedFiberι S.S))

/-- **The object `(V, S|_V, γ)` of `CRIS(S₀/S)`.**  It is the terminal object `(S₀, S, γ)` of
`Crystalline.GlobalCrystallineSituation.closedFiberThickening` restricted to the open of `S`
matching `V`. -/
def closedFiberRestrict (V : (DividedPowerScheme.closedFiber S.S).Opens) :
    Thickening (closedFiberSituation S hlocnil) :=
  (closedFiberThickening S hlocnil hthick).restrictOpen (closedFiberOpen hthick V)

/-- The thickened scheme of `(V, S|_V, γ)` is the open `V` of `S₀`. -/
@[simp]
theorem range_closedFiberRestrict_toX (V : (DividedPowerScheme.closedFiber S.S).Opens) :
    Set.range (closedFiberRestrict hlocnil hthick V).toX.base =
      (V : Set (DividedPowerScheme.closedFiber S.S)) := by
  change Set.range ((DividedPowerScheme.closedFiberι S.S ⁻¹ᵁ closedFiberOpen hthick V).ι ≫
    𝟙 (DividedPowerScheme.closedFiber S.S)).base = _
  rw [Category.comp_id, Scheme.Opens.range_ι, preimage_closedFiberOpen]

/-- The map to `S₀` of `(V, S|_V, γ)` is an open immersion, so the object lies in the small
crystalline site `Cris(S₀/S)`. -/
theorem isCrystalline_closedFiberRestrict (V : (DividedPowerScheme.closedFiber S.S).Opens) :
    Thickening.IsCrystalline (closedFiberRestrict hlocnil hthick V) :=
  Thickening.isCrystalline_restrictOpen (isCrystalline_closedFiberThickening S hlocnil hthick) _

/-- **A morphism into `(V, S|_V, γ)` is unique.**  Composing with the structure morphism to
`(S₀, S, γ)` gives a morphism into a terminal object, and the structure morphism of a restriction
to an open is a monomorphism. -/
instance subsingleton_hom_closedFiberRestrict (B : Thickening (closedFiberSituation S hlocnil))
    (V : (DividedPowerScheme.closedFiber S.S).Opens) :
    Subsingleton (B ⟶ closedFiberRestrict hlocnil hthick V) :=
  ⟨fun _ _ ↦ Thickening.restrictOpen_hom_ext
    ((isTerminal_closedFiberThickening S hlocnil hthick).hom_ext _ _)⟩

/-- **The morphism into `(V, S|_V, γ)` from an object lying over `V`.**  The unique morphism into
the terminal object `(S₀, S, γ)` has ambient map the structure map `T ⟶ S`, whose image lies in
the open matching `V`, so it factors through the restriction. -/
def toClosedFiberRestrict {B : Thickening (closedFiberSituation S hlocnil)}
    {V : (DividedPowerScheme.closedFiber S.S).Opens}
    (h : Set.range B.toX.base ⊆ (V : Set (DividedPowerScheme.closedFiber S.S))) :
    B ⟶ closedFiberRestrict hlocnil hthick V :=
  Thickening.restrictOpenLift (toClosedFiberThickening S hlocnil hthick B)
    (closedFiberOpen hthick V)
    ((range_toBase_subset_closedFiberOpen_iff hlocnil hthick B V).mpr h)

/-- **An object admitting a morphism into `(V, S|_V, γ)` lies over `V`.**  The composite with the
structure morphism of the restriction is the unique morphism into the terminal object, so the
structure map `T ⟶ S` factors through the open matching `V`. -/
theorem range_toX_subset_of_hom_closedFiberRestrict
    {B : Thickening (closedFiberSituation S hlocnil)}
    {V : (DividedPowerScheme.closedFiber S.S).Opens}
    (a : B ⟶ closedFiberRestrict hlocnil hthick V) :
    Set.range B.toX.base ⊆ (V : Set (DividedPowerScheme.closedFiber S.S)) := by
  refine (range_toBase_subset_closedFiberOpen_iff hlocnil hthick B V).mp ?_
  have hterm : a ≫ (closedFiberThickening S hlocnil hthick).restrictOpenHom
      (closedFiberOpen hthick V) = toClosedFiberThickening S hlocnil hthick B :=
    (isTerminal_closedFiberThickening S hlocnil hthick).hom_ext _ _
  have hb : B.toBase.hom = a.targetHom.hom ≫ (closedFiberOpen hthick V).ι :=
    (congrArg (fun k : B ⟶ closedFiberThickening S hlocnil hthick ↦ k.targetHom.hom) hterm).symm
  rintro _ ⟨x, rfl⟩
  have hx : B.toBase.hom.base x ∈ Set.range (closedFiberOpen hthick V).ι.base := by
    rw [hb]
    exact ⟨a.targetHom.hom.base x, rfl⟩
  rwa [Scheme.Opens.range_ι] at hx

/-- **The hom-sets into `(V, S|_V, γ)` are nonempty exactly for the objects lying over `V`.** -/
theorem nonempty_hom_closedFiberRestrict_iff (B : Thickening (closedFiberSituation S hlocnil))
    (V : (DividedPowerScheme.closedFiber S.S).Opens) :
    Nonempty (B ⟶ closedFiberRestrict hlocnil hthick V) ↔
      Set.range B.toX.base ⊆ (V : Set (DividedPowerScheme.closedFiber S.S)) :=
  ⟨fun ⟨a⟩ ↦ range_toX_subset_of_hom_closedFiberRestrict hlocnil hthick a,
    fun h ↦ ⟨toClosedFiberRestrict hlocnil hthick h⟩⟩

/-- **`V ↦ (V, S|_V, γ)` is a functor.**  Its action on an inclusion `V ⊆ V'` is the unique
morphism supplied by the universal property, and the functor laws hold because the hom-sets
involved have at most one element. -/
def closedFiberRestrictFunctor :
    (DividedPowerScheme.closedFiber S.S).Opens ⥤ Thickening (closedFiberSituation S hlocnil) where
  obj V := closedFiberRestrict hlocnil hthick V
  map h := toClosedFiberRestrict hlocnil hthick
    ((range_closedFiberRestrict_toX hlocnil hthick _).trans_subset (leOfHom h))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The functor `V ↦ (V, S|_V, γ)` sends `V` to the thickening `closedFiberRestrict V`. -/
@[simp]
theorem closedFiberRestrictFunctor_obj (V : (DividedPowerScheme.closedFiber S.S).Opens) :
    (closedFiberRestrictFunctor hlocnil hthick).obj V = closedFiberRestrict hlocnil hthick V :=
  rfl

/-- **`V ↦ (V, S|_V, γ)` as a functor into the small crystalline site `Cris(S₀/S)`.** -/
def closedFiberRestrictCris :
    (DividedPowerScheme.closedFiber S.S).Opens ⥤
      CrystallineThickening (closedFiberSituation S hlocnil) :=
  (Thickening.IsCrystalline (S := closedFiberSituation S hlocnil)).lift
    (closedFiberRestrictFunctor hlocnil hthick) (isCrystalline_closedFiberRestrict hlocnil hthick)

/-- The underlying object of `CRIS(S₀/S)` of the image of `V` in `Cris(S₀/S)` is
`(V, S|_V, γ)`. -/
@[simp]
theorem closedFiberRestrictCris_obj_obj (V : (DividedPowerScheme.closedFiber S.S).Opens) :
    ((closedFiberRestrictCris hlocnil hthick).obj V).obj =
      closedFiberRestrict hlocnil hthick V :=
  rfl

/-- The composite of `V ↦ (V, S|_V, γ)` with the inclusion of the small crystalline site into the
big one is the same functor read in `CRIS(S₀/S)`. -/
theorem closedFiberRestrictCris_comp_ι :
    closedFiberRestrictCris hlocnil hthick ⋙ CrystallineThickening.ι _ =
      closedFiberRestrictFunctor hlocnil hthick :=
  rfl

/-- **A morphism of `Cris(S₀/S)` into `(V, S|_V, γ)` is unique.**  The small crystalline site is
a full subcategory of the big one, where the hom-set already has at most one element. -/
instance subsingleton_hom_closedFiberRestrictCris
    (A : CrystallineThickening (closedFiberSituation S hlocnil))
    (V : (DividedPowerScheme.closedFiber S.S).Opens) :
    Subsingleton (A ⟶ (closedFiberRestrictCris hlocnil hthick).obj V) :=
  ⟨fun a b ↦ ObjectProperty.hom_ext _
    (Subsingleton.elim (α := A.obj ⟶ closedFiberRestrict hlocnil hthick V) a.hom b.hom)⟩

/-- **Stacks Project, Tag 07IM.**  The forgetful functor `Cris(S₀/S) ⥤ S₀_Zar` of
[Stacks, Tag 07IH] is left adjoint to `V ↦ (V, S|_V, γ)`.  A morphism of `Cris(S₀/S)` into
`(V, S|_V, γ)` is exactly an inclusion of the open image of the source into `V`: it is unique when
it exists, and it exists exactly then.

This is the shape the site takes when `p` is nilpotent on the base, which is strictly more than
[Stacks, Tag 07MF] and [Stacks, Tag 07IM] give: `Cris(S₀/S)` has a terminal object once `S₀ ↪ S`
is a thickening, and restricting it to the opens of `S` makes the forgetful functor a right
adjointable one.  The remark's upper square does not need this; see the module documentation. -/
def forgetToOpensClosedFiberAdjunction :
    forgetToOpens (closedFiberSituation S hlocnil) ⊣ closedFiberRestrictCris hlocnil hthick :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ ↦
        { toFun := fun h ↦ ObjectProperty.homMk
            (toClosedFiberRestrict hlocnil hthick (leOfHom h))
          invFun := fun a ↦ homOfLE
            (range_toX_subset_of_hom_closedFiberRestrict hlocnil hthick a.hom)
          left_inv := fun _ ↦ Subsingleton.elim _ _
          right_inv := fun _ ↦ Subsingleton.elim _ _ }
      homEquiv_naturality_left_symm := fun _ _ ↦ Subsingleton.elim _ _
      homEquiv_naturality_right := fun _ _ ↦ Subsingleton.elim _ _ }

/-- **The right adjoint `V ↦ (V, S|_V, γ)` is a continuous functor of sites.**  It is right
adjoint to a cocontinuous functor, [Stacks, Tag 00XX]. -/
instance closedFiberRestrictCris_isContinuous :
    (closedFiberRestrictCris hlocnil hthick).IsContinuous
      (Opens.grothendieckTopology (DividedPowerScheme.closedFiber S.S).carrier)
      (smallTopology (closedFiberSituation S hlocnil)) :=
  haveI : (forgetToOpens (closedFiberSituation S hlocnil)).IsCocontinuous
      (smallTopology (closedFiberSituation S hlocnil))
      (Opens.grothendieckTopology (DividedPowerScheme.closedFiber S.S).carrier) :=
    forgetToOpens_isCocontinuous (closedFiberSituation S hlocnil)
  (forgetToOpensClosedFiberAdjunction hlocnil hthick).isContinuous_of_isCocontinuous
    (smallTopology (closedFiberSituation S hlocnil))
    (Opens.grothendieckTopology (DividedPowerScheme.closedFiber S.S).carrier)

end

end Crystalline.GlobalCrystallineSituation

end
