module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.Separation
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PseudoTorsors
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocus

/-!
# Unramifiedness and quasi-finiteness of a pseudo-torsor

Let `X` be a pseudo-torsor under a group algebraic space `G` over an algebraic space `B`.  The
structure morphism `X ⟶ B` inherits unramifiedness and local quasi-finiteness from `G ⟶ B`.

## Main results

* `AlgebraicGeometry.Space.isUnramified_of_isPseudoTorsor`: **Stacks 0DSK**, the unramified
  case.
* `AlgebraicGeometry.Space.isLocallyQuasiFinite_of_isPseudoTorsor`: **Stacks 0DSK**, the
  locally quasi-finite case.

## Implementation notes

A group algebraic space over `B` is a group object of the slice of presheaves over `B`, so a
pseudo-torsor under it is an object of that slice whose shear map
`CategoryTheory.ModObj.leftSMul` is an isomorphism, and the structure morphisms of the slice
objects are the morphisms to `B`.  In the slice the monoidal product is the fibre product
over `B` and the monoidal unit is the identity of `B`, so the identity section of `G` is a
morphism `B ⟶ G` over `B` and the pair `x ↦ (1, x)` is a morphism `X ⟶ G ×_B X` over `B`.

The unramified case factors the relative diagonal of `X ⟶ B` as that pair followed by the
shear map.  The pair is a base change of the identity section of `G`, which is itself a base
change of the relative diagonal of `G ⟶ B` along
`CategoryTheory.Limits.isPullback_section_diagonal`; that diagonal is an open immersion by
**Stacks 05W1**, part (1), and the shear map is an isomorphism, so the relative diagonal of
`X ⟶ B` is an open immersion and **Stacks 05W1**, part (2) applies.  Being locally of finite
type is not assumed of `G ⟶ B`: an unramified morphism of algebraic spaces is locally of
finite type by **Stacks 05VZ**.

The locally quasi-finite case compares the two projections `G ×_B X ⟶ X` and `X ×_B X ⟶ X`
along the shear map: the first is a base change of `G ⟶ B`, so the second is locally
quasi-finite.  The relative diagonal of `X ⟶ B` is a section of that second projection, and
the quasi-finite locus commutes with base change by **Stacks 0ABM**, part (2), so every point
of `X` is a point at which `X ⟶ B` is quasi-finite; **Stacks 040Z** then concludes.  Local
quasi-finiteness of `G ⟶ B` already contains being locally of finite type, so again only
`X ⟶ B` needs that hypothesis.

## References

* [Stacks Project, Tag 0DSK](https://stacks.math.columbia.edu/tag/0DSK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonObj

universe u

namespace AlgebraicGeometry.Space

/-! ### The unit pair of an action -/

/-- The pair `x ↦ (1, x)` into the product with a monoid object is a base change of the
identity section of that monoid object along the first projection. -/
private theorem isPullback_lift_one {C : Type*} [Category C] [CartesianMonoidalCategory C]
    (G X : C) [MonObj G] :
    IsPullback (lift (1 : X ⟶ G) (𝟙 X)) (toUnit X) (fst G X) η[G] := by
  have hcomm : lift (1 : X ⟶ G) (𝟙 X) ≫ fst G X = toUnit X ≫ η[G] := by
    simp [Hom.one_def]
  refine ⟨⟨hcomm⟩, ⟨PullbackCone.IsLimit.mk hcomm (fun s => s.fst ≫ snd G X) ?_ ?_ ?_⟩⟩
  · intro s
    have hterm : (s.fst ≫ snd G X) ≫ toUnit X = s.snd := toUnit_unique _ _
    refine hom_ext _ _ ?_ ?_
    · rw [Category.assoc, hcomm, ← Category.assoc, hterm, s.condition]
    · simp
  · exact fun s => toUnit_unique _ _
  · intro s m hm _
    calc
      m = m ≫ lift (1 : X ⟶ G) (𝟙 X) ≫ snd G X := by simp
      _ = s.fst ≫ snd G X := by rw [← Category.assoc, hm]

/-- Acting with the identity on a point and remembering the point is the diagonal. -/
private theorem lift_one_leftSMul {C : Type*} [Category C] [CartesianMonoidalCategory C]
    (G X : C) [MonObj G] [ModObj G X] :
    lift (1 : X ⟶ G) (𝟙 X) ≫ ModObj.leftSMul G X = lift (𝟙 X) (𝟙 X) := by
  rw [ModObj.lift_leftSMul, one_smul]

/-- In the slice of presheaves over `B`, the diagonal of an object is the relative diagonal
of its structure morphism. -/
private theorem lift_id_left_eq_pullbackDiagonal (𝒞 : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : 𝒞.Contains S) {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} (X : Over B) :
    (lift (𝟙 X) (𝟙 X)).left = pullback.diagonal X.hom := by
  apply pullback.hom_ext <;>
    simp only [Over.lift_left, pullback.lift_fst, pullback.lift_snd,
      pullback.diagonal_fst, pullback.diagonal_snd, Over.id_left]

/-! ### Unramifiedness -/

/-- **Stacks 0DSK.** A pseudo-torsor under an unramified group algebraic space is unramified
over the base, provided it is locally of finite type over the base. -/
@[stacks 0DSK "the unramified case"]
theorem isUnramified_of_isPseudoTorsor (𝒞 : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : 𝒞.Contains S) {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u}
    (hB : IsAlgebraicSpace 𝒞 S hS B) (G : GroupAlgebraicSpace 𝒞 S hS B hB) (X : Over B)
    [ModObj G.obj.X X] (hX : IsAlgebraicSpace 𝒞 S hS X.left)
    (hXFiniteType : IsLocallyOfFiniteType 𝒞 S hS X.hom)
    (hG : IsUnramified 𝒞 S hS G.obj.X.hom) (hPseudo : IsPseudoTorsor G.obj.X X) :
    IsUnramified 𝒞 S hS X.hom := by
  let P := (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme 𝒞 S hS)).presheaf
  have : P.IsMultiplicative := MorphismProperty.relative_isMultiplicative _
  have hbc : P.IsStableUnderBaseChange := MorphismProperty.relative_isStableUnderBaseChange _
  have hOne : IsOpenImmersion 𝒞 S hS (η[G.obj.X]).left :=
    hbc.of_isPullback
      (isPullback_section_diagonal G.obj.X.hom (η[G.obj.X]).left (by simp))
      (isOpenImmersion_diagonal_of_isUnramified 𝒞 S hS G.property hB G.obj.X.hom hG)
  have hUnit : IsOpenImmersion 𝒞 S hS
      (lift (1 : X ⟶ G.obj.X) (𝟙 X) : X ⟶ G.obj.X ⊗ X).left :=
    hbc.of_isPullback
      (IsPullback.map (Over.forget B) (isPullback_lift_one G.obj.X X)).flip hOne
  have hShear : IsOpenImmersion 𝒞 S hS (ModObj.leftSMul G.obj.X X).left := by
    have : IsIso (ModObj.leftSMul G.obj.X X) := hPseudo
    have : IsIso (ModObj.leftSMul G.obj.X X).left :=
      inferInstanceAs (IsIso ((Over.forget B).map (ModObj.leftSMul G.obj.X X)))
    exact MorphismProperty.of_isIso P _
  have hDiagonal : IsOpenImmersion 𝒞 S hS (pullback.diagonal X.hom) := by
    rw [← lift_id_left_eq_pullbackDiagonal 𝒞 S hS X, ← lift_one_leftSMul G.obj.X X,
      Over.comp_left]
    exact MorphismProperty.comp_mem _ _ _ hUnit hShear
  exact isUnramified_of_isOpenImmersion_pullbackDiagonal 𝒞 S hS hX hB X.hom hXFiniteType
    hDiagonal

/-! ### Local quasi-finiteness -/

/-- For a pseudo-torsor `X` under `G` over `B`, the second projection of `X ×_B X` is
identified by the shear map with the second projection of `G ×_B X`, hence with a base change
of the structure morphism of `G`. -/
private theorem isLocallyQuasiFinite_pullbackSnd_of_isPseudoTorsor (𝒞 : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : 𝒞.Contains S) {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u}
    (hB : IsAlgebraicSpace 𝒞 S hS B) (G : GroupAlgebraicSpace 𝒞 S hS B hB) (X : Over B)
    [ModObj G.obj.X X] (hX : IsAlgebraicSpace 𝒞 S hS X.left)
    (hG : IsLocallyQuasiFinite 𝒞 S hS G.obj.X.hom) (hPseudo : IsPseudoTorsor G.obj.X X) :
    IsLocallyQuasiFinite 𝒞 S hS (pullback.snd X.hom X.hom) := by
  let B₀ : AlgebraicSpaces 𝒞 S hS := ⟨B, hB⟩
  let X₀ : AlgebraicSpaces 𝒞 S hS := ⟨X.left, hX⟩
  let G₀ : AlgebraicSpaces 𝒞 S hS := ⟨G.obj.X.left, G.property⟩
  let A : AlgebraicSpaces 𝒞 S hS :=
    ⟨(G.obj.X ⊗ X).left,
      isAlgebraicSpace_pullback 𝒞 S hS G.obj.X.hom X.hom G.property hX hB⟩
  let C : AlgebraicSpaces 𝒞 S hS :=
    ⟨(X ⊗ X).left, isAlgebraicSpace_pullback 𝒞 S hS X.hom X.hom hX hX hB⟩
  let pA : A ⟶ X₀ := ObjectProperty.homMk (snd G.obj.X X).left
  let pC : C ⟶ X₀ := ObjectProperty.homMk (snd X X).left
  have hpA : IsLocallyQuasiFinite 𝒞 S hS pA.hom :=
    (isLocallyQuasiFinite_isStableUnderBaseChange 𝒞 S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct 𝒞 S hS
        (ObjectProperty.homMk G.obj.X.hom : G₀ ⟶ B₀)
        (ObjectProperty.homMk X.hom : X₀ ⟶ B₀)) hG
  have : IsIso (ModObj.leftSMul G.obj.X X) := hPseudo
  let e : A ≅ C :=
    ObjectProperty.isoMk _ ((Over.forget B).mapIso (asIso (ModObj.leftSMul G.obj.X X)))
  have he : e.hom ≫ pC = pA := by
    apply ObjectProperty.hom_ext
    show (ModObj.leftSMul G.obj.X X).left ≫ (snd X X).left = (snd G.obj.X X).left
    exact congrArg Over.Hom.left ModObj.leftSMul_snd
  exact (isLocallyQuasiFinite_isStableUnderBaseChange 𝒞 S hS).of_isPullback
    (IsPullback.of_horiz_isIso (fst := e.inv) (snd := pC) (f := pA) (g := 𝟙 X₀)
      ⟨by simp [← he]⟩) hpA

/-- **Local quasi-finiteness descends from the second projection of the self-fibre-product.**
If `f : X ⟶ B` is a morphism of algebraic spaces over `S` which is locally of finite type, and
the second projection `X ×_B X ⟶ X` is locally quasi-finite, then `f` itself is locally
quasi-finite.

The relative diagonal of `f` is a section of that projection, so every point of `X` is the
image under the first projection of a point at which the projection is quasi-finite; the
quasi-finite locus commutes with base change by **Stacks 0ABM**, part (2), in the form
`AlgebraicGeometry.Space.setOf_isQuasiFiniteAt_eq_preimage_of_isPullback`, so every point of `X`
is one at which `f` is quasi-finite, and **Stacks 040Z** concludes.

This is the whole of the argument of **Stacks 0DSK** in the locally quasi-finite case *except*
the input `hsnd`, which is the only place a torsor structure enters: see
`AlgebraicGeometry.Space.isLocallyQuasiFinite_of_isPseudoTorsor`, which is this lemma fed by
`AlgebraicGeometry.Space.isLocallyQuasiFinite_pullbackSnd_of_isPseudoTorsor`. It is stated
separately because the hypothesis `hsnd` is also available when `f` is a base change of a
locally quasi-finite morphism along itself, with no group anywhere. -/
theorem isLocallyQuasiFinite_of_isLocallyQuasiFinite_pullbackSnd (𝒞 : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : 𝒞.Contains S) {Bs Xs : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u}
    (hB : IsAlgebraicSpace 𝒞 S hS Bs) (hX : IsAlgebraicSpace 𝒞 S hS Xs) (g : Xs ⟶ Bs)
    (hgFiniteType : IsLocallyOfFiniteType 𝒞 S hS g)
    (hsnd : IsLocallyQuasiFinite 𝒞 S hS (pullback.snd g g)) :
    IsLocallyQuasiFinite 𝒞 S hS g := by
  let B₀ : AlgebraicSpaces 𝒞 S hS := ⟨Bs, hB⟩
  let X₀ : AlgebraicSpaces 𝒞 S hS := ⟨Xs, hX⟩
  let f : X₀ ⟶ B₀ := ObjectProperty.homMk g
  let XX := AlgebraicSpaces.fiberProduct 𝒞 S hS f f
  let p : XX ⟶ X₀ := ObjectProperty.homMk (pullback.fst g g)
  let q : XX ⟶ X₀ := ObjectProperty.homMk (pullback.snd g g)
  let diag : X₀ ⟶ XX := ObjectProperty.homMk (pullback.diagonal g)
  have hsquare : IsPullback p q f f := AlgebraicSpaces.isPullback_fiberProduct 𝒞 S hS f f
  have hq : IsLocallyQuasiFinite 𝒞 S hS q.hom := hsnd
  have hlocus := setOf_isQuasiFiniteAt_eq_preimage_of_isPullback 𝒞 S hS hsquare hgFiniteType
  have hdiagPoints (x : points 𝒞 S hS Xs) :
      pointsMap 𝒞 S hS XX.obj p.hom (pointsMap 𝒞 S hS Xs diag.hom x) = x := by
    have h := congrFun (pointsMap_comp 𝒞 S hS Xs diag.hom p.hom) x
    rw [show diag.hom ≫ p.hom = 𝟙 Xs from pullback.diagonal_fst g,
      pointsMap_id] at h
    exact h.symm
  have hqf : ∀ x : points 𝒞 S hS Xs, IsQuasiFiniteAt 𝒞 S hS g x := by
    intro x
    have hz : pointsMap 𝒞 S hS Xs diag.hom x ∈
        {z : points 𝒞 S hS XX.obj | IsQuasiFiniteAt 𝒞 S hS q.hom z} :=
      (isLocallyQuasiFinite_iff_forall_isQuasiFiniteAt 𝒞 S hS XX.property hX q.hom).1 hq _
    rw [hlocus] at hz
    have hz' : IsQuasiFiniteAt 𝒞 S hS g
        (pointsMap 𝒞 S hS XX.obj p.hom (pointsMap 𝒞 S hS Xs diag.hom x)) := hz
    rwa [hdiagPoints x] at hz'
  exact (isLocallyQuasiFinite_iff_forall_isQuasiFiniteAt 𝒞 S hS hX hB g).2 hqf

/-- **Stacks 0DSK.** A pseudo-torsor under a locally quasi-finite group algebraic space is
locally quasi-finite over the base, provided it is locally of finite type over the base.

The shear map identifies the second projection of `X ×_B X` with that of `G ×_B X`, which is a
base change of `G ⟶ B`, so the projection is locally quasi-finite; that is the only use of the
torsor structure, and
`AlgebraicGeometry.Space.isLocallyQuasiFinite_of_isLocallyQuasiFinite_pullbackSnd` is the rest
of the argument. -/
@[stacks 0DSK "the locally quasi-finite case"]
theorem isLocallyQuasiFinite_of_isPseudoTorsor (𝒞 : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : 𝒞.Contains S) {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u}
    (hB : IsAlgebraicSpace 𝒞 S hS B) (G : GroupAlgebraicSpace 𝒞 S hS B hB) (X : Over B)
    [ModObj G.obj.X X] (hX : IsAlgebraicSpace 𝒞 S hS X.left)
    (hXFiniteType : IsLocallyOfFiniteType 𝒞 S hS X.hom)
    (hG : IsLocallyQuasiFinite 𝒞 S hS G.obj.X.hom) (hPseudo : IsPseudoTorsor G.obj.X X) :
    IsLocallyQuasiFinite 𝒞 S hS X.hom :=
  isLocallyQuasiFinite_of_isLocallyQuasiFinite_pullbackSnd 𝒞 S hS hB hX X.hom hXFiniteType
    (isLocallyQuasiFinite_pullbackSnd_of_isPseudoTorsor 𝒞 S hS hB G X hX hG hPseudo)

end AlgebraicGeometry.Space

end
