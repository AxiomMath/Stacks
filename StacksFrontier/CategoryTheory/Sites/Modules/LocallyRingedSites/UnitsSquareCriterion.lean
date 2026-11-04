module

public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.Morphisms
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullback
public import StacksFrontier.CategoryTheory.Sites.InfinitaryExtensive
import StacksCore.Tactic.StacksAttribute

/-!
# When is the units square of a map of structure sheaves cartesian?

Stacks 04HA calls a morphism of ringed topoi *locally ringed* when its square

```
  f⁻¹(O_Y^*) ---> O_X^*
      |             |
      v             v
  f⁻¹(O_Y)  ---> O_X
```

of units subsheaves is cartesian.  After the inverse image of the units subsheaf of the target
has been identified with the units subsheaf of the inverse-image structure sheaf — which is
Stacks 04KR, `AlgebraicGeometry.inverseImageUnitsIso` — that square becomes the units square of
a *morphism of sheaves of commutative rings on one site*, and the question it poses is whether
that morphism **reflects units**.

This file answers the question in that form, for a morphism `φ : O₁ ⟶ O₂` of sheaves of
commutative rings on a site `(C, J)`, in two ways.

The answer given here is the one the criterion of Stacks 04H9 uses: the square is cartesian as
soon as it is cartesian at every member of a family of left exact functors to sets which detects
isomorphisms — in practice the stalk functors at a conservative family of points of the site.
Reflecting units at a stalk of a locally ringed topos is locality of the induced map of local
rings, which is why that is the shape the hypothesis is given.

## Main definitions

* `AlgebraicGeometry.RingedTopos.unitsMapOf`: the map of units subsheaves induced by a morphism
  of sheaves of commutative rings.
* `AlgebraicGeometry.RingedTopos.ReflectsUnitsObj`: reflection of units read through a functor
  to sets, with no reference to a ring structure on its values.

## Main results

* `AlgebraicGeometry.RingedTopos.unitsMapOf_comp_unitsιOf`: the units square commutes.
* `AlgebraicGeometry.RingedTopos.isPullback_map_unitsSquare`: a left exact functor to sets which
  reflects units carries the units square to a cartesian square of sets.
* `AlgebraicGeometry.RingedTopos.reflectsUnitsObj_of_isPullback`: conversely, if the units
  square is cartesian then every left exact functor to sets reflects units.
* `AlgebraicGeometry.RingedTopos.reflectsUnitsObj_of_comp`: reflection of units for a composite
  gives reflection of units for its left factor.
* `AlgebraicGeometry.RingedTopos.isPullback_unitsSquare_of_family`: if a family of left exact
  functors to sets detects isomorphisms and each member reflects units, the units square is
  cartesian.

## Implementation notes

`AlgebraicGeometry.RingedTopos.ReflectsUnitsObj` is stated with no ring structure on the values
of the functor: it says that a value of `P` on the underlying sheaf of sets of `O₁` lifts
through the units subsheaf of `O₁` as soon as its image lifts through the units subsheaf of
`O₂`.  For a left exact `P` this is equivalent to reflection of units for the transported ring
structures, by `AlgebraicGeometry.RingedTopos.isUnit_iff_exists_map_unitsIncl`; stating it
without them keeps the proof below free of any ring-structure transport and keeps the statement
usable before the transport has been identified with whatever concrete ring the application has
in hand.

The family is not required to be small, and conservativity is taken as a hypothesis in the form
it is used — the implication from pointwise isomorphism to isomorphism — rather than as
`CategoryTheory.GrothendieckTopology.IsConservativeFamily`, whose index type is forced into the
universe of the sheaves of sets.

## References

* [Stacks Project, Tag 04HA](https://stacks.math.columbia.edu/tag/04HA)
* [Stacks Project, Tag 04H9](https://stacks.math.columbia.edu/tag/04H9)
* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.RingedTopos

universe t w v u

variable {C : Type u} [Category.{v} C]

/-- The site `(C, J)` with a chosen sheaf of commutative rings on it, read as a ringed topos.
This is the ringed topos whose units subsheaf the square below is about. -/
abbrev ofStructureSheaf (J : GrothendieckTopology C) (O : Sheaf J CommRingCat.{w}) :
    RingedTopos.{v, u, w} :=
  { C := C, J := J, O := O }

variable {J : GrothendieckTopology C}

/-- The units subsheaf of a sheaf of commutative rings on `(C, J)`: the subsheaf of invertible
sections, as a sheaf of sets. -/
noncomputable abbrev unitsOf (O : Sheaf J CommRingCat.{w}) : Sheaf J (Type w) :=
  units (ofStructureSheaf J O)

/-- The inclusion of the units subsheaf into the underlying sheaf of sets. -/
noncomputable abbrev unitsιOf (O : Sheaf J CommRingCat.{w}) :
    unitsOf O ⟶ (sheafCompose J (forget CommRingCat.{w})).obj O :=
  unitsι (ofStructureSheaf J O)

variable {O₁ O₂ : Sheaf J CommRingCat.{w}}

/-- A morphism of sheaves of commutative rings, read on underlying sheaves of sets. -/
noncomputable abbrev forgetRingMap (φ : O₁ ⟶ O₂) :
    (sheafCompose J (forget CommRingCat.{w})).obj O₁ ⟶
      (sheafCompose J (forget CommRingCat.{w})).obj O₂ :=
  (sheafCompose J (forget CommRingCat.{w})).map φ

/-- A section of the units subsheaf of `O` over `U`, read as a unit of the sections of `O` over
`U`.  The two types are the same; naming the identification keeps the statements below typeable
without unfolding the units subsheaf by hand. -/
def toUnitsSection (O : Sheaf J CommRingCat.{w}) (U : Cᵒᵖ)
    (x : (Sheaf.sectionsFunctor J U).obj (unitsOf O)) : (O.obj.obj U)ˣ := x

/-- A section of the underlying sheaf of sets of `O` over `U`, read as a section of `O` over
`U`.  Again the two types are the same. -/
def toRingSection (O : Sheaf J CommRingCat.{w}) (U : Cᵒᵖ)
    (a : (Sheaf.sectionsFunctor J U).obj ((sheafCompose J (forget CommRingCat.{w})).obj O)) :
    O.obj.obj U := a

/-- The inclusion of the units subsheaf takes a section to the value of the corresponding
unit. -/
theorem toRingSection_map_unitsιOf (O : Sheaf J CommRingCat.{w}) (U : Cᵒᵖ)
    (x : (Sheaf.sectionsFunctor J U).obj (unitsOf O)) :
    toRingSection O U ((Sheaf.sectionsFunctor J U).map (unitsιOf O) x) =
      ((toUnitsSection O U x : (O.obj.obj U)ˣ) : O.obj.obj U) :=
  rfl

/-- Restriction of sections of the units subsheaf is restriction of the corresponding units. -/
theorem toUnitsSection_map {O : Sheaf J CommRingCat.{w}} {U V : Cᵒᵖ} (g : U ⟶ V)
    (x : (Sheaf.sectionsFunctor J U).obj (unitsOf O)) :
    (toUnitsSection O V ((unitsOf O).obj.map g x) : O.obj.obj V) =
      (O.obj.map g).hom ((toUnitsSection O U x : (O.obj.obj U)ˣ) : O.obj.obj U) :=
  rfl

/-- A morphism of sheaves of commutative rings acts on sections by its component. -/
theorem toRingSection_map_forgetRingMap (φ : O₁ ⟶ O₂) (U : Cᵒᵖ)
    (a : (Sheaf.sectionsFunctor J U).obj ((sheafCompose J (forget CommRingCat.{w})).obj O₁)) :
    toRingSection O₂ U ((Sheaf.sectionsFunctor J U).map (forgetRingMap φ) a) =
      (φ.hom.app U).hom (toRingSection O₁ U a) :=
  rfl

/-- The map of units subsheaves induced by a morphism of sheaves of commutative rings: a ring
homomorphism carries an invertible section to an invertible section. -/
noncomputable def unitsMapOf (φ : O₁ ⟶ O₂) : unitsOf O₁ ⟶ unitsOf O₂ :=
  Sheaf.unaryOpHom (A := unitsOf O₁) (E := unitsOf O₂)
    (fun U x ↦ Units.map (φ.hom.app U).hom.toMonoidHom (toUnitsSection O₁ U x))
    (fun {U _V} g x ↦ Units.ext
      (NatTrans.naturality_apply φ.hom g
        ((toUnitsSection O₁ U x : (O₁.obj.obj U)ˣ) : O₁.obj.obj U)).symm)

/-- The value of the map of units subsheaves is the image of the value. -/
theorem toRingSection_map_unitsMapOf (φ : O₁ ⟶ O₂) (U : Cᵒᵖ)
    (x : (Sheaf.sectionsFunctor J U).obj (unitsOf O₁)) :
    ((toUnitsSection O₂ U ((Sheaf.sectionsFunctor J U).map (unitsMapOf φ) x) :
        (O₂.obj.obj U)ˣ) : O₂.obj.obj U) =
      (φ.hom.app U).hom ((toUnitsSection O₁ U x : (O₁.obj.obj U)ˣ) : O₁.obj.obj U) :=
  rfl

/-- **The units square commutes.** -/
theorem unitsMapOf_comp_unitsιOf (φ : O₁ ⟶ O₂) :
    unitsMapOf φ ≫ unitsιOf O₂ = unitsιOf O₁ ≫ forgetRingMap φ :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-! ### The criterion at a family of left exact functors to sets -/

/-- **A functor to sets reflects units** for `φ` when a value of it on the underlying sheaf of
sets of `O₁` lifts through the units subsheaf of `O₁` as soon as its image lifts through the
units subsheaf of `O₂`.

No ring structure on the values of `P` appears.  When `P` is left exact its value on the
underlying sheaf of sets of a structure sheaf carries the transported ring structure and the
sections lifting through the transported units subsheaf are exactly the invertible ones, so
this is reflection of units for that ring structure. -/
def ReflectsUnitsObj (P : Sheaf J (Type w) ⥤ Type t) (φ : O₁ ⟶ O₂) : Prop :=
  ∀ a : P.obj ((sheafCompose J (forget CommRingCat.{w})).obj O₁),
    (∃ v : P.obj (unitsOf O₂), P.map (unitsιOf O₂) v = P.map (forgetRingMap φ) a) →
      ∃ u : P.obj (unitsOf O₁), P.map (unitsιOf O₁) u = a

section Transport

variable (P : Sheaf J (Type w) ⥤ Type t) [PreservesFiniteLimits P] (φ : O₁ ⟶ O₂)

/-- A left exact functor to sets carries the inclusion of a units subsheaf to an injection. -/
theorem injective_map_unitsιOf (O : Sheaf J CommRingCat.{w}) :
    Function.Injective (P.map (unitsιOf O)) := by
  have : Mono (unitsιOf O) := unitsι_mono (ofStructureSheaf J O)
  have : Mono (P.map (unitsιOf O)) := P.map_mono _
  rwa [← CategoryTheory.mono_iff_injective]

omit [PreservesFiniteLimits P] in
/-- The image under `P` of the units square commutes. -/
theorem map_unitsMapOf_comp_map_unitsιOf :
    P.map (unitsMapOf φ) ≫ P.map (unitsιOf O₂) =
      P.map (unitsιOf O₁) ≫ P.map (forgetRingMap φ) := by
  rw [← P.map_comp, ← P.map_comp, unitsMapOf_comp_unitsιOf]

omit [PreservesFiniteLimits P] in
/-- The image under `P` of the units square commutes, elementwise. -/
theorem map_unitsιOf_map_unitsMapOf (u : P.obj (unitsOf O₁)) :
    P.map (unitsιOf O₂) (P.map (unitsMapOf φ) u) =
      P.map (forgetRingMap φ) (P.map (unitsιOf O₁) u) := by
  simpa only [types_comp_apply] using
    ConcreteCategory.congr_hom (map_unitsMapOf_comp_map_unitsιOf P φ) u

/-- **A left exact functor to sets reflecting units carries the units square to a cartesian
square of sets.** The missing lift is the unit the hypothesis provides, and both factorisations
and the uniqueness come from injectivity of the two inclusions of units. -/
theorem isPullback_map_unitsSquare (h : ReflectsUnitsObj P φ) :
    IsPullback (P.map (unitsMapOf φ)) (P.map (unitsιOf O₁)) (P.map (unitsιOf O₂))
      (P.map (forgetRingMap φ)) := by
  refine Types.isPullback_of_existsUnique _ _ _ _ (map_unitsMapOf_comp_map_unitsιOf P φ)
    fun v a hva ↦ ?_
  obtain ⟨u, hu⟩ := h a ⟨v, hva⟩
  refine ⟨u, ⟨injective_map_unitsιOf P O₂ ?_, hu⟩,
    fun u' hu' ↦ injective_map_unitsιOf P O₁ (hu'.2.trans hu.symm)⟩
  rw [map_unitsιOf_map_unitsMapOf, hu, ← hva]

/-- **A cartesian units square is reflected by every left exact functor to sets.** The functor
carries the square to a cartesian square of sets, and the lift of a point of the one-point type
through it is the required unit. -/
theorem reflectsUnitsObj_of_isPullback
    (hsq : IsPullback (unitsMapOf φ) (unitsιOf O₁) (unitsιOf O₂) (forgetRingMap φ)) :
    ReflectsUnitsObj P φ := by
  intro a ⟨v, hv⟩
  obtain ⟨u, hu, -⟩ := Types.existsUnique_of_isPullback (hsq.map P) hv
  exact ⟨u, hu.2⟩

omit [PreservesFiniteLimits P] in
/-- **Reflection of units passes to a left factor.** If a functor to sets reflects units for a
composite `φ ≫ ψ` of morphisms of sheaves of commutative rings, it reflects units for `φ`.

Read through `AlgebraicGeometry.RingedTopos.isUnit_iff_exists_map_unitsIncl` this is the
elementary fact that `IsLocalHom (ψ.comp φ)` implies `IsLocalHom φ`: a section whose image under
`φ` is invertible has its image under `φ ≫ ψ` invertible too, because a ring homomorphism
carries units to units — which here is `AlgebraicGeometry.RingedTopos.unitsMapOf ψ`.  No left
exactness and no ring structure on the values of `P` are used.

This is what makes the units square of a morphism of ringed topoi whose source has a square-zero
extension `𝒜` of `O_X` for its structure sheaf cartesian: the structure map `f⁻¹O_B ⟶ 𝒜`
composed with the surjection `𝒜 ⟶ O_X` is the structure map of the morphism `X ⟶ B` of algebraic
spaces, which is locally ringed, so units are reflected for the composite and therefore for
`f⁻¹O_B ⟶ 𝒜` itself. -/
theorem reflectsUnitsObj_of_comp {O₃ : Sheaf J CommRingCat.{w}} (ψ : O₂ ⟶ O₃)
    (h : ReflectsUnitsObj P (φ ≫ ψ)) : ReflectsUnitsObj P φ := by
  rintro a ⟨v, hv⟩
  refine h a ⟨P.map (unitsMapOf ψ) v, ?_⟩
  rw [show forgetRingMap (φ ≫ ψ) = forgetRingMap φ ≫ forgetRingMap ψ from
      Functor.map_comp _ _ _, P.map_comp, types_comp_apply, ← hv]
  exact map_unitsιOf_map_unitsMapOf P ψ v

end Transport

/-- **The units square is cartesian as soon as it is cartesian at a family of left exact
functors to sets which detects isomorphisms.** This is how the criterion of Stacks 04H9 is
applied: the family is the family of stalk functors at a conservative family of points, and
reflecting units at a stalk is locality of the induced map of stalk rings. -/
theorem isPullback_unitsSquare_of_family (φ : O₁ ⟶ O₂) {ι : Type*}
    (P : ι → Sheaf J (Type w) ⥤ Type t) (hP : ∀ i, PreservesFiniteLimits (P i))
    [HasPullback (unitsιOf O₂) (forgetRingMap φ)]
    (hcons : ∀ {F G : Sheaf J (Type w)} (ψ : F ⟶ G), (∀ i, IsIso ((P i).map ψ)) → IsIso ψ)
    (h : ∀ i, ReflectsUnitsObj (P i) φ) :
    IsPullback (unitsMapOf φ) (unitsιOf O₁) (unitsιOf O₂) (forgetRingMap φ) := by
  have hcomm := unitsMapOf_comp_unitsιOf φ
  have hiso : IsIso (pullback.lift (unitsMapOf φ) (unitsιOf O₁) hcomm) := by
    refine hcons _ fun i ↦ ?_
    have := hP i
    have hQ := (IsPullback.of_hasPullback (unitsιOf O₂) (forgetRingMap φ)).map (P i)
    have hP := isPullback_map_unitsSquare (P i) φ (h i)
    have hce : (P i).map (pullback.lift (unitsMapOf φ) (unitsιOf O₁) hcomm) =
        (hP.isoIsPullback _ _ hQ).hom := by
      refine hQ.hom_ext ?_ ?_
      · rw [hP.isoIsPullback_hom_fst, ← (P i).map_comp, pullback.lift_fst]
      · rw [hP.isoIsPullback_hom_snd, ← (P i).map_comp, pullback.lift_snd]
    rw [hce]
    infer_instance
  refine IsPullback.of_iso_pullback ⟨hcomm⟩
    (asIso (pullback.lift (unitsMapOf φ) (unitsιOf O₁) hcomm)) ?_ ?_
  · rw [asIso_hom, pullback.lift_fst]
  · rw [asIso_hom, pullback.lift_snd]

end AlgebraicGeometry.RingedTopos

end
