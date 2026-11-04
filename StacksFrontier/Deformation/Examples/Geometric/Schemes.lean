module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.Examples.Geometric.BaseSpectrum

/-!
# Deformations of a scheme

A flat scheme family over `𝒞_Λ` is a scheme flat over the spectrum of an object of `𝒞_Λ`. Its
morphisms go covariantly on the bases and contravariantly on the schemes, and record that the
scheme over the smaller base is the base change of the scheme over the larger one; forgetting
the scheme gives a functor to `𝒞_Λ`, and that functor is cofibered in groupoids because base
change of a flat morphism is flat.

A *deformation of a scheme* `X` over the residue field is a flat scheme family together with a
cartesian square identifying the fibre over the closed point with `X`. These also form a
category over `𝒞_Λ`.

The standing data of the glueing discussion is a scheme over `k` covered by two affine opens
with affine intersection, with coordinate rings chosen for the three affine schemes.

## Main definitions

* `Deformation.Examples.FlatSchemeFamily`: a scheme flat over the spectrum of an object
  of `𝒞_Λ`.
* `Deformation.Examples.FlatSchemeFamily.Hom`: a base-change morphism of flat families.
* `Deformation.Examples.flatSchemeFamilyProjection`: the functor to `𝒞_Λ`.
* `Deformation.Examples.SchemeDeformationCategory`: a flat family with an identification of its
  fibre over the closed point with a fixed scheme over `k`.
* `Deformation.Examples.SchemeDeformationCategory.Hom`: its morphisms.
* `Deformation.Examples.schemeDeformationCategoryProjection`: the functor to `𝒞_Λ`.
* `Deformation.Examples.GluingSituation`: a scheme over `k` with a two-element affine open
  covering whose intersection is affine, and coordinate rings for the three affine schemes.

## Main results

* `Deformation.Examples.flatSchemeFamilyProjection_cofiberedInGroupoids`: the projection from
  flat scheme families to `𝒞_Λ` is cofibered in groupoids.

## Implementation notes

The identification of the fibre over the closed point is encoded by a cartesian square from
`X` to the family rather than by an isomorphism `Y ×_{Spec A} Spec k ≅ X`; by the universal
property of the fibre product the two data are equivalent, and the square avoids choosing a
fibre product. The deformation category is given directly rather than as a slice of the
category of all flat families, so nothing about that larger category is needed to state it.

Neither category imposes Noetherianness or any finiteness on the structure morphisms; those
hypotheses are not used in the constructions.

In `GluingSituation` the identifications of the three affine opens with spectra are
isomorphisms *over* `Spec k`, which is what records the algebra structures on the three
coordinate rings and makes the restriction maps between them `k`-linear.

## References

* [Stacks Project, Tag 0DY7](https://stacks.math.columbia.edu/tag/0DY7)
* [Stacks Project, Tag 0DYY](https://stacks.math.columbia.edu/tag/0DYY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace Deformation.Examples

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-! ### Flat families of schemes over the base category -/

/-- A scheme flat over the spectrum of an object of `𝒞_Λ`. -/
@[stacks 0DY7 "flat_scheme_families"]
structure FlatSchemeFamily (Λ : Type u) (k : Type w) [CommRing Λ] [Field k] [Algebra Λ k] where
  /-- The object of `𝒞_Λ` the family lives over. -/
  base : ArtinianLocalAlgCat.{u, v, w} Λ k
  /-- The total space of the family. -/
  scheme : Scheme.{v}
  /-- The structure morphism to the spectrum of the base. -/
  toBase : scheme ⟶ baseSpec base
  /-- The structure morphism is flat. -/
  flat : Flat toBase

namespace FlatSchemeFamily

/-- A cartesian base-change arrow between flat scheme families. -/
@[ext, stacks 0DY7 "flat_scheme_families"]
structure Hom (P Q : FlatSchemeFamily.{u, v, w} Λ k) where
  /-- The morphism of the bases. -/
  base : P.base ⟶ Q.base
  /-- The morphism of total spaces, in the opposite direction. -/
  map : Q.scheme ⟶ P.scheme
  /-- The square exhibiting the second family as the base change of the first. -/
  cartesian : IsPullback map Q.toBase P.toBase (baseSpecMap base)

/-- Flat scheme families over objects of `𝒞_Λ` and their base-change arrows form
a category. -/
@[stacks 0DY7 "flat_scheme_families"]
instance instCategory : Category (FlatSchemeFamily.{u, v, w} Λ k) where
  Hom := Hom
  id P :=
    { base := 𝟙 P.base
      map := 𝟙 P.scheme
      cartesian := by
        rw [baseSpecMap_id]
        exact IsPullback.id_horiz P.toBase }
  comp f g :=
    { base := f.base ≫ g.base
      map := g.map ≫ f.map
      cartesian := by
        rw [baseSpecMap_comp]
        exact g.cartesian.paste_horiz f.cartesian }
  id_comp := by intros; ext <;> simp
  comp_id := by intros; ext <;> simp
  assoc := by
    intro W Y Z T f g h
    apply Hom.ext <;> simp [Category.assoc]

end FlatSchemeFamily

/-- The canonical functor sending a flat scheme family to its object of `𝒞_Λ`. -/
@[stacks 0DY7 "flat_scheme_families", implicit_reducible]
def flatSchemeFamilyProjection :
    FlatSchemeFamily.{u, v, w} Λ k ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k where
  obj P := P.base
  map f := f.base
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Base change makes the projection from flat scheme families cofibered in groupoids. -/
@[stacks 0DY7 "cofibred_projection"]
theorem flatSchemeFamilyProjection_cofiberedInGroupoids
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k] :
    IsCofiberedInGroupoids (flatSchemeFamilyProjection.{u, v, w} (Λ := Λ) (k := k)) := by
  classical
  let p := flatSchemeFamilyProjection.{u, v, w} (Λ := Λ) (k := k)
  change (p.op).IsFiberedInGroupoids
  refine ⟨?_, ?_⟩
  · intro V U f x hx
    cases hx
    let x₀ := x.unop
    have : Flat x₀.toBase := x₀.flat
    let f₀ := f.unop
    let X : FlatSchemeFamily.{u, v, w} Λ k :=
      { base := V.unop
        scheme := pullback x₀.toBase (baseSpecMap f₀)
        toBase := pullback.snd x₀.toBase (baseSpecMap f₀)
        flat := inferInstance }
    let φ : x₀ ⟶ X :=
      { base := f₀
        map := pullback.fst x₀.toBase (baseSpecMap f₀)
        cartesian := IsPullback.of_hasPullback _ _ }
    refine ⟨Opposite.op X, Opposite.op φ, ?_⟩
    rw [show f = (p.op).map (Opposite.op φ) from rfl]
    infer_instance
  · intro x y z φ ψ f h
    let x₀ := x.unop
    let y₀ := y.unop
    let z₀ := z.unop
    let φ₀ := φ.unop
    let ψ₀ := ψ.unop
    let f₀ := f.unop
    have h₀ : φ₀.base ≫ f₀ = ψ₀.base := by
      simpa [p, flatSchemeFamilyProjection, φ₀, ψ₀, f₀] using congrArg Quiver.Hom.unop h
    have hspec : baseSpecMap ψ₀.base = baseSpecMap f₀ ≫ baseSpecMap φ₀.base := by
      rw [← h₀, baseSpecMap_comp]
    let χmap : z₀.scheme ⟶ y₀.scheme :=
      φ₀.cartesian.lift ψ₀.map (z₀.toBase ≫ baseSpecMap f₀) (by
        rw [ψ₀.cartesian.w, hspec]
        simp [z₀, Category.assoc])
    let χ₀ : y₀ ⟶ z₀ :=
      { base := f₀
        map := χmap
        cartesian := IsPullback.of_right
          (by rw [φ₀.cartesian.lift_fst, ← hspec]; exact ψ₀.cartesian)
          (φ₀.cartesian.lift_snd _ _ _) φ₀.cartesian }
    have hcomp : φ₀ ≫ χ₀ = ψ₀ :=
      FlatSchemeFamily.Hom.ext h₀ (φ₀.cartesian.lift_fst _ _ _)
    refine ⟨Opposite.op χ₀,
      ⟨rfl, Quiver.Hom.unop_inj (by simpa [x₀, z₀, φ₀, ψ₀] using hcomp)⟩, ?_⟩
    intro χ hχ
    apply Quiver.Hom.unop_inj
    have hbase : χ.unop.base = f₀ := by
      simpa [p, flatSchemeFamilyProjection, f₀] using congrArg Quiver.Hom.unop hχ.1
    refine FlatSchemeFamily.Hom.ext hbase ?_
    apply φ₀.cartesian.hom_ext
    · have hmaps : χ.unop.map ≫ φ₀.map = ψ₀.map := by
        have hh := congrArg Quiver.Hom.unop hχ.2
        change φ₀ ≫ χ.unop = ψ₀ at hh
        change χ.unop.map ≫ φ₀.map = ψ₀.map
        exact congrArg (fun g : x₀ ⟶ z₀ => g.map) hh
      simpa [χ₀, χmap] using hmaps
    · simpa [hbase, χ₀, χmap] using χ.unop.cartesian.w

/-! ### Deformations of a fixed scheme over the residue field -/

section

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-- A flat family over an object of `𝒞_Λ` together with an identification of its fibre over
the closed point with a fixed scheme over `k`. The identification is recorded as a cartesian
square. -/
@[stacks 0DY7 "scheme_deformation_category", sga "7 VI 1.1(c)"]
structure SchemeDeformationCategory (X : Over (Spec (.of k))) where
  /-- The object of `𝒞_Λ` the deformation lives over. -/
  base : ArtinianLocalAlgCat.{u, u, u} Λ k
  /-- The total space of the deformation. -/
  scheme : Scheme.{u}
  /-- The structure morphism to the spectrum of the base. -/
  toBase : scheme ⟶ baseSpec base
  /-- The structure morphism is flat. -/
  flat : Flat toBase
  /-- The closed immersion of the fibre over the closed point. -/
  specialMap : X.left ⟶ scheme
  /-- The square identifying that fibre with `X`. -/
  specialCartesian : IsPullback specialMap X.hom toBase (residueSpecMap base)

namespace SchemeDeformationCategory

/-- A cartesian arrow of deformations: contravariant on the schemes, covariant on the objects
of `𝒞_Λ`, and compatible with the two identifications of the fibre over the closed point. -/
@[ext, stacks 0DY7 "scheme_deformation_category"]
structure Hom {X : Over (Spec (.of k))}
    (P Q : SchemeDeformationCategory (Λ := Λ) (k := k) X) where
  /-- The morphism of the bases. -/
  base : P.base ⟶ Q.base
  /-- The morphism of total spaces, in the opposite direction. -/
  map : Q.scheme ⟶ P.scheme
  /-- The square exhibiting the second deformation as the base change of the first. -/
  cartesian : IsPullback map Q.toBase P.toBase (baseSpecMap base)
  /-- Compatibility with the identifications of the fibre over the closed point. -/
  special_compat : Q.specialMap ≫ map = P.specialMap

/-- Deformations of a fixed scheme over `k` form a category. -/
@[stacks 0DY7 "scheme_deformation_category", sga "7 VI 1.1(c)"]
instance instCategory (X : Over (Spec (.of k))) :
    Category (SchemeDeformationCategory (Λ := Λ) (k := k) X) where
  Hom := Hom
  id P :=
    { base := 𝟙 P.base
      map := 𝟙 P.scheme
      cartesian := by
        rw [baseSpecMap_id]
        exact IsPullback.id_horiz P.toBase
      special_compat := by simp }
  comp f g :=
    { base := f.base ≫ g.base
      map := g.map ≫ f.map
      cartesian := by
        rw [baseSpecMap_comp]
        exact g.cartesian.paste_horiz f.cartesian
      special_compat := by
        rw [← Category.assoc, g.special_compat, f.special_compat] }
  id_comp := by intros; ext <;> simp
  comp_id := by intros; ext <;> simp
  assoc := by
    intro W Y Z T f g h
    apply Hom.ext <;> simp [Category.assoc]

end SchemeDeformationCategory

/-- The canonical projection from the category of deformations of a scheme to `𝒞_Λ`. -/
@[stacks 0DY7 "scheme_deformation_category", implicit_reducible]
def schemeDeformationCategoryProjection (X : Over (Spec (.of k))) :
    SchemeDeformationCategory (Λ := Λ) (k := k) X ⥤ ArtinianLocalAlgCat.{u, u, u} Λ k where
  obj P := P.base
  map f := f.base
  map_id _ := rfl
  map_comp _ _ := rfl

end

/-! ### The glueing situation -/

/-- A scheme over `k`, covered by two affine opens with affine intersection, together with
coordinate rings for the three affine schemes. -/
@[stacks 0DYY]
structure GluingSituation (Λ k : Type u) [CommRing Λ] [Field k] [Algebra Λ k] where
  /-- The scheme to be deformed, with its morphism to the residue field. -/
  X : Over (Spec (.of k))
  /-- The first affine open. -/
  U₁ : X.left.Opens
  /-- The second affine open. -/
  U₂ : X.left.Opens
  /-- The two opens cover the scheme. -/
  cover : U₁ ⊔ U₂ = ⊤
  /-- The first coordinate ring. -/
  P₁ : Type u
  [commRing₁ : CommRing P₁]
  [algebra₁ : Algebra k P₁]
  /-- The second coordinate ring. -/
  P₂ : Type u
  [commRing₂ : CommRing P₂]
  [algebra₂ : Algebra k P₂]
  /-- The coordinate ring of the intersection. -/
  P₁₂ : Type u
  [commRing₁₂ : CommRing P₁₂]
  [algebra₁₂ : Algebra k P₁₂]
  /-- The first open is the spectrum of its coordinate ring over `k`. -/
  affine₁ : Over.mk (U₁.ι ≫ X.hom) ≅ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k P₁)))
  /-- The second open is the spectrum of its coordinate ring over `k`. -/
  affine₂ : Over.mk (U₂.ι ≫ X.hom) ≅ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k P₂)))
  /-- The intersection is the spectrum of its coordinate ring over `k`. -/
  affine₁₂ : Over.mk ((U₁ ⊓ U₂).ι ≫ X.hom) ≅
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k P₁₂)))

attribute [instance] GluingSituation.commRing₁ GluingSituation.algebra₁
  GluingSituation.commRing₂ GluingSituation.algebra₂
  GluingSituation.commRing₁₂ GluingSituation.algebra₁₂

end Deformation.Examples

end
