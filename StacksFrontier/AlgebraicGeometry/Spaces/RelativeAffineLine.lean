module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteRepresentability
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleStructureSheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The relative affine line over an object of the big fppf site

Let `B` be a big fppf site containing a scheme `S` and let `V` be an object of the big fppf
category over `S`.  This file constructs the relative affine line `𝔸¹_V` as an object of that
same category, together with its projection to `V`, and identifies the morphisms of a presheaf
`W` over `V` into `𝔸¹_V` with the morphisms of `W` into the affine line `𝔸¹_S` over the base.
For an algebraic space `W` the latter are its global regular functions, so the file ends with
the *over-a-base* form of the passage from a function to a morphism: a global function on an
algebraic space over `V` is the same thing as a morphism to `𝔸¹_V` over `V`.

## Main definitions

* `AlgebraicGeometry.Space.relativeAffineLine`: the relative affine line `𝔸¹_V` over an object `V`
  of the big fppf category over `S`, as an object of that category.  Its underlying scheme is
  Mathlib's `AlgebraicGeometry.AffineSpace` on one variable over the underlying scheme of `V`,
  and its structure morphism to `S` factors through `V`.
* `AlgebraicGeometry.Space.relativeAffineLineProjection`: the projection `𝔸¹_V ⟶ V`.
* `AlgebraicGeometry.Space.relativeAffineLineToAffineLine`: the morphism `𝔸¹_V ⟶ 𝔸¹_S` over the
  base, which together with the projection exhibits `𝔸¹_V` as `V ×_S 𝔸¹_S`.
* `AlgebraicGeometry.Space.relativeAffineLineLift` and
  `AlgebraicGeometry.Space.relativeAffineLineHom`: the morphism into `𝔸¹_V` attached to a morphism
  to `V` and a morphism to `𝔸¹_S`, for an object of the site and for an arbitrary presheaf
  on it.

## Main results

* `AlgebraicGeometry.Space.isPullback_relativeAffineLine`: `𝔸¹_V` is the fibre product
  `V ×_S 𝔸¹_S` on underlying schemes.
* `AlgebraicGeometry.Space.relativeAffineLineHomEquiv`: the morphisms of a presheaf `W` into
  `𝔸¹_V` *over* `V` are the morphisms of `W` into `𝔸¹_S`.  This is the step that has no tag of
  its own in the source and that a relative form of Stacks 05Z1 would otherwise be needed for:
  the base `S` is not assumed terminal anywhere.
* `AlgebraicGeometry.Space.globalFunctionsRelativeAffineLineEquiv`: **the over-a-base
  function-to-morphism passage.**  For an algebraic space `W` over `V`, the morphisms
  `W ⟶ 𝔸¹_V` over `V` are the global regular functions on `W`.
* `AlgebraicGeometry.Space.isSeparated_relativeAffineLineProjection` and
  `AlgebraicGeometry.Space.isQuasiSeparated_relativeAffineLineProjection`: the projection
  `𝔸¹_V ⟶ V` is a separated, hence quasi-separated, morphism of algebraic spaces.  This is the
  hypothesis Stacks 03KS asks of the second factor of a composite.
* `AlgebraicGeometry.Space.isAffine_relativeAffineLine`: `𝔸¹_V` has affine underlying scheme when
  `V` does.

## Implementation notes

The identification of morphisms over `V` is obtained from the cartesian square
`𝔸¹_V = V ×_S 𝔸¹_S` of Mathlib's `AlgebraicGeometry.AffineSpace.isPullback_map`, read on
underlying schemes.  Nothing is assumed about `S`: a morphism of the big fppf category over `S`
commutes with the structure morphisms by `CategoryTheory.Over.w`, which is what supplies the
compatibility the cartesian square asks for, and the lift it returns is again a morphism over
`S` for the same reason.  This is why the construction needs no terminality hypothesis, unlike
`AlgebraicGeometry.Space.morphismToAffineEquiv`, whose target is an arbitrary affine object of
the site and which therefore has to produce the compatibility over `S` out of nothing.

Only the one-variable case is built, because that is what a single regular function needs; the
construction is the same for any finite index type.

**Nothing here carries a Stacks attribute, deliberately.**  The source takes the passage from a
function to a morphism over the base with no citation at all, inside the proof of Stacks 0A0Q;
Stacks 05Z1 is the absolute statement, over a terminal base, and is proved elsewhere; and the
Hom-set form of the mapping property of a relative spectrum is a statement about schemes,
Stacks 01LQ.  So this file is infrastructure for Stacks 0A0Q rather than a formalization of any
tag, and the tag stays where the assertion it belongs to is proved.

## References

* [Stacks Project, Tag 0A0Q](https://stacks.math.columbia.edu/tag/0A0Q)
* [Stacks Project, Tag 03KS](https://stacks.math.columbia.edu/tag/03KS)
* [Stacks Project, Tag 05Z1](https://stacks.math.columbia.edu/tag/05Z1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The relative affine line -/

/-- **The relative affine line over an object `V` of the big fppf category over `S`**, as an
object of that category: affine one-space over the underlying scheme of `V`, with structure
morphism the projection to `V` followed by the structure morphism of `V`.

It belongs to the site because it is of finite type and quasi-compact over `V`, which belongs
to the site. -/
@[ega "IV 20.5.4" "special case"]
noncomputable def relativeAffineLine (V : BigFppfOver B S hS) : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS
    (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact
      (𝔸(PUnit.{u + 1}; (BigFppfOver.toScheme B S hS).obj V) ↘
        (BigFppfOver.toScheme B S hS).obj V)
      (show B.Contains ((BigFppfOver.toScheme B S hS).obj V) from V.left.property))
    ((𝔸(PUnit.{u + 1}; (BigFppfOver.toScheme B S hS).obj V) ↘
      (BigFppfOver.toScheme B S hS).obj V) ≫ B.inclusion.map V.hom)

/-- The underlying scheme of the relative affine line over `V` is affine one-space over the
underlying scheme of `V`. -/
theorem toScheme_obj_relativeAffineLine (V : BigFppfOver B S hS) :
    (BigFppfOver.toScheme B S hS).obj (relativeAffineLine B S hS V) =
      𝔸(PUnit.{u + 1}; (BigFppfOver.toScheme B S hS).obj V) :=
  rfl

/-- The projection of the relative affine line over `V` to `V`. -/
noncomputable def relativeAffineLineProjection (V : BigFppfOver B S hS) :
    relativeAffineLine B S hS V ⟶ V :=
  Over.homMk (ObjectProperty.homMk
      (𝔸(PUnit.{u + 1}; (BigFppfOver.toScheme B S hS).obj V) ↘
        (BigFppfOver.toScheme B S hS).obj V))
    (by apply ObjectProperty.hom_ext; rfl)

/-- The projection of the relative affine line is, on underlying schemes, the structure
morphism of affine one-space. -/
theorem toScheme_map_relativeAffineLineProjection (V : BigFppfOver B S hS) :
    (BigFppfOver.toScheme B S hS).map (relativeAffineLineProjection B S hS V) =
      (𝔸(PUnit.{u + 1}; (BigFppfOver.toScheme B S hS).obj V) ↘
        (BigFppfOver.toScheme B S hS).obj V) :=
  rfl

/-- The morphism from the relative affine line over `V` to the affine line over the base `S`,
induced by the structure morphism of `V`. -/
noncomputable def relativeAffineLineToAffineLine (V : BigFppfOver B S hS) :
    relativeAffineLine B S hS V ⟶ affineLineBigFppfOver B S hS :=
  Over.homMk (ObjectProperty.homMk
      (AffineSpace.map PUnit.{u + 1} (B.inclusion.map V.hom)))
    (by apply ObjectProperty.hom_ext; exact AffineSpace.map_over _)

/-- The morphism to the affine line over the base is, on underlying schemes, the functoriality
of affine one-space in the base. -/
theorem toScheme_map_relativeAffineLineToAffineLine (V : BigFppfOver B S hS) :
    (BigFppfOver.toScheme B S hS).map (relativeAffineLineToAffineLine B S hS V) =
      AffineSpace.map PUnit.{u + 1} (B.inclusion.map V.hom) :=
  rfl

/-- **The relative affine line over `V` is the fibre product `V ×_S 𝔸¹_S`**, on underlying
schemes: this is the base-change property of affine space. -/
theorem isPullback_relativeAffineLine (V : BigFppfOver B S hS) :
    IsPullback ((BigFppfOver.toScheme B S hS).map (relativeAffineLineToAffineLine B S hS V))
      ((BigFppfOver.toScheme B S hS).map (relativeAffineLineProjection B S hS V))
      (𝔸(PUnit.{u + 1}; S) ↘ S) (B.inclusion.map V.hom) :=
  AffineSpace.isPullback_map (B.inclusion.map V.hom)

/-- The relative affine line over `V` has affine underlying scheme as soon as `V` does. -/
theorem isAffine_relativeAffineLine (V : BigFppfOver B S hS)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (relativeAffineLine B S hS V)) :=
  have := hV
  inferInstanceAs (IsAffine 𝔸(PUnit.{u + 1}; (BigFppfOver.toScheme B S hS).obj V))

/-! ### Morphisms into the relative affine line, for an object of the site -/

/-- The morphism of schemes into the relative affine line attached to a morphism `a` to `V`
and a morphism `b` to the affine line over the base: the lift through the cartesian square.
The compatibility the square asks for holds because every morphism of the site commutes with
the structure morphisms to `S`. -/
noncomputable def relativeAffineLineLiftScheme (V : BigFppfOver B S hS) {U : BigFppfOver B S hS}
    (a : U ⟶ V) (b : U ⟶ affineLineBigFppfOver B S hS) :
    (BigFppfOver.toScheme B S hS).obj U ⟶
      𝔸(PUnit.{u + 1}; (BigFppfOver.toScheme B S hS).obj V) :=
  (isPullback_relativeAffineLine B S hS V).lift ((BigFppfOver.toScheme B S hS).map b)
    ((BigFppfOver.toScheme B S hS).map a)
    ((BigFppfOver.toScheme_map_comp_structureHom B S hS b).trans
      (BigFppfOver.toScheme_map_comp_structureHom B S hS a).symm)

/-- The scheme-level lift followed by the projection of affine one-space is the given morphism
to `V`. -/
theorem relativeAffineLineLiftScheme_projection (V : BigFppfOver B S hS) {U : BigFppfOver B S hS}
    (a : U ⟶ V) (b : U ⟶ affineLineBigFppfOver B S hS) :
    relativeAffineLineLiftScheme B S hS V a b ≫
        (𝔸(PUnit.{u + 1}; (BigFppfOver.toScheme B S hS).obj V) ↘
          (BigFppfOver.toScheme B S hS).obj V) =
      (BigFppfOver.toScheme B S hS).map a :=
  (isPullback_relativeAffineLine B S hS V).lift_snd _ _ _

/-- The morphism of the site into `𝔸¹_V` attached to a morphism `a` to `V` and a morphism `b`
to the affine line over the base. -/
noncomputable def relativeAffineLineLift (V : BigFppfOver B S hS) {U : BigFppfOver B S hS}
    (a : U ⟶ V) (b : U ⟶ affineLineBigFppfOver B S hS) : U ⟶ relativeAffineLine B S hS V :=
  BigFppfOver.homMk B S hS
    (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact
      (𝔸(PUnit.{u + 1}; (BigFppfOver.toScheme B S hS).obj V) ↘
        (BigFppfOver.toScheme B S hS).obj V)
      (show B.Contains ((BigFppfOver.toScheme B S hS).obj V) from V.left.property))
    ((𝔸(PUnit.{u + 1}; (BigFppfOver.toScheme B S hS).obj V) ↘
      (BigFppfOver.toScheme B S hS).obj V) ≫ B.inclusion.map V.hom)
    (relativeAffineLineLiftScheme B S hS V a b)
    (by
      rw [← Category.assoc, relativeAffineLineLiftScheme_projection]
      exact BigFppfOver.toScheme_map_comp_structureHom B S hS a)

/-- The lift into `𝔸¹_V` composed with the projection to `V` is the given morphism to `V`. -/
theorem relativeAffineLineLift_projection (V : BigFppfOver B S hS) {U : BigFppfOver B S hS}
    (a : U ⟶ V) (b : U ⟶ affineLineBigFppfOver B S hS) :
    relativeAffineLineLift B S hS V a b ≫ relativeAffineLineProjection B S hS V = a :=
  (BigFppfOver.toScheme B S hS).map_injective
    ((isPullback_relativeAffineLine B S hS V).lift_snd _ _ _)

/-- The lift into `𝔸¹_V` composed with the morphism to the affine line over the base is the
given morphism to that affine line. -/
theorem relativeAffineLineLift_toAffineLine (V : BigFppfOver B S hS) {U : BigFppfOver B S hS}
    (a : U ⟶ V) (b : U ⟶ affineLineBigFppfOver B S hS) :
    relativeAffineLineLift B S hS V a b ≫ relativeAffineLineToAffineLine B S hS V = b :=
  (BigFppfOver.toScheme B S hS).map_injective
    ((isPullback_relativeAffineLine B S hS V).lift_fst _ _ _)

/-- A morphism of the site into `𝔸¹_V` is determined by its composites with the projection to
`V` and with the morphism to the affine line over the base. -/
theorem relativeAffineLine_hom_ext (V : BigFppfOver B S hS) {U : BigFppfOver B S hS}
    {m m' : U ⟶ relativeAffineLine B S hS V}
    (h₁ : m ≫ relativeAffineLineProjection B S hS V = m' ≫ relativeAffineLineProjection B S hS V)
    (h₂ : m ≫ relativeAffineLineToAffineLine B S hS V =
      m' ≫ relativeAffineLineToAffineLine B S hS V) :
    m = m' := by
  refine (BigFppfOver.toScheme B S hS).map_injective ?_
  refine (isPullback_relativeAffineLine B S hS V).hom_ext ?_ ?_
  · simpa only [Functor.map_comp] using congrArg (BigFppfOver.toScheme B S hS).map h₂
  · simpa only [Functor.map_comp] using congrArg (BigFppfOver.toScheme B S hS).map h₁

/-! ### Morphisms into the relative affine line, for a presheaf -/

/-- The morphism of presheaves into `𝔸¹_V` attached to a morphism `p` to `V` and a morphism
`r` to the affine line over the base: on each object of the site it is the lift of the two
morphisms of the site, and naturality is uniqueness of such lifts. -/
noncomputable def relativeAffineLineHom (V : BigFppfOver B S hS)
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : W ⟶ yoneda.obj V)
    (r : W ⟶ yoneda.obj (affineLineBigFppfOver B S hS)) :
    W ⟶ yoneda.obj (relativeAffineLine B S hS V) where
  app U := ↾fun w => relativeAffineLineLift B S hS V (p.app U w) (r.app U w)
  naturality U U' g := by
    ext w
    change relativeAffineLineLift B S hS V (p.app U' (W.map g w)) (r.app U' (W.map g w)) =
      g.unop ≫ relativeAffineLineLift B S hS V (p.app U w) (r.app U w)
    refine relativeAffineLine_hom_ext B S hS V ?_ ?_
    · rw [relativeAffineLineLift_projection, Category.assoc, relativeAffineLineLift_projection]
      exact ConcreteCategory.congr_hom (p.naturality g) w
    · rw [relativeAffineLineLift_toAffineLine, Category.assoc, relativeAffineLineLift_toAffineLine]
      exact ConcreteCategory.congr_hom (r.naturality g) w

/-- The morphism of presheaves into `𝔸¹_V` lies over the given morphism to `V`. -/
theorem relativeAffineLineHom_projection (V : BigFppfOver B S hS)
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : W ⟶ yoneda.obj V)
    (r : W ⟶ yoneda.obj (affineLineBigFppfOver B S hS)) :
    relativeAffineLineHom B S hS V p r ≫
        yoneda.map (relativeAffineLineProjection B S hS V) = p := by
  ext U w
  exact relativeAffineLineLift_projection B S hS V (p.app U w) (r.app U w)

/-- The morphism of presheaves into `𝔸¹_V` induces the given morphism to the affine line over
the base. -/
theorem relativeAffineLineHom_toAffineLine (V : BigFppfOver B S hS)
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : W ⟶ yoneda.obj V)
    (r : W ⟶ yoneda.obj (affineLineBigFppfOver B S hS)) :
    relativeAffineLineHom B S hS V p r ≫
        yoneda.map (relativeAffineLineToAffineLine B S hS V) = r := by
  ext U w
  exact relativeAffineLineLift_toAffineLine B S hS V (p.app U w) (r.app U w)

/-- A morphism of presheaves into `𝔸¹_V` is determined by its composites with the projection
to `V` and with the morphism to the affine line over the base. -/
theorem relativeAffineLine_presheaf_hom_ext (V : BigFppfOver B S hS)
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {m m' : W ⟶ yoneda.obj (relativeAffineLine B S hS V)}
    (h₁ : m ≫ yoneda.map (relativeAffineLineProjection B S hS V) =
      m' ≫ yoneda.map (relativeAffineLineProjection B S hS V))
    (h₂ : m ≫ yoneda.map (relativeAffineLineToAffineLine B S hS V) =
      m' ≫ yoneda.map (relativeAffineLineToAffineLine B S hS V)) :
    m = m' := by
  ext U w
  refine relativeAffineLine_hom_ext B S hS V ?_ ?_
  · exact congrArg (fun η : W ⟶ yoneda.obj V => η.app U w) h₁
  · exact congrArg
      (fun η : W ⟶ yoneda.obj (affineLineBigFppfOver B S hS) => η.app U w) h₂

/-- **The morphisms of a presheaf into the relative affine line over `V`, over `V`, are its
morphisms into the affine line over the base.**

This is the step the source takes without citing anything, in the shape it is needed in: no
terminality of `S` is involved, because `𝔸¹_V` is the fibre product `V ×_S 𝔸¹_S` and a morphism
of the site is automatically compatible with the structure morphisms to `S`. -/
noncomputable def relativeAffineLineHomEquiv (V : BigFppfOver B S hS)
    (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (p : W ⟶ yoneda.obj V) :
    { q : W ⟶ yoneda.obj (relativeAffineLine B S hS V) //
        q ≫ yoneda.map (relativeAffineLineProjection B S hS V) = p } ≃
      (W ⟶ yoneda.obj (affineLineBigFppfOver B S hS)) where
  toFun q := q.1 ≫ yoneda.map (relativeAffineLineToAffineLine B S hS V)
  invFun r := ⟨relativeAffineLineHom B S hS V p r, relativeAffineLineHom_projection B S hS V p r⟩
  left_inv q := by
    refine Subtype.ext (relativeAffineLine_presheaf_hom_ext B S hS V ?_ ?_)
    · rw [relativeAffineLineHom_projection, q.2]
    · rw [relativeAffineLineHom_toAffineLine]
  right_inv r := relativeAffineLineHom_toAffineLine B S hS V p r

/-! ### The function-to-morphism passage over a base -/

/-- **The over-a-base form of the passage from a regular function to a morphism to the affine
line.**  For an algebraic space `W` over an object `V` of the big fppf category over `S`, the
morphisms `W ⟶ 𝔸¹_V` *over* `V` are the global regular functions on `W`.

The absolute form — morphisms of an algebraic space to an affine object of the site against
ring homomorphisms out of its functions, Stacks 05Z1 — carries a terminality hypothesis on the
base, and the relative form is not a tag of the source.  It is obtained here from the absolute
identification of global functions with morphisms to `𝔸¹_S`
(`AlgebraicGeometry.Space.globalFunctionsHomEquiv`) together with
`AlgebraicGeometry.Space.relativeAffineLineHomEquiv`, which is where the base is dealt with. -/
noncomputable def globalFunctionsRelativeAffineLineEquiv (V : BigFppfOver B S hS)
    (W : AlgebraicSpaces B S hS) (p : W.obj ⟶ yoneda.obj V) :
    { q : W.obj ⟶ yoneda.obj (relativeAffineLine B S hS V) //
        q ≫ yoneda.map (relativeAffineLineProjection B S hS V) = p } ≃
      globalFunctions' B S hS W.obj :=
  (relativeAffineLineHomEquiv B S hS V W.obj p).trans
    ((({ toFun := fun f => ObjectProperty.homMk f
         invFun := fun f => f.hom
         left_inv := fun _ => rfl
         right_inv := fun _ => rfl } :
        (W.obj ⟶ yoneda.obj (affineLineBigFppfOver B S hS)) ≃
          (W ⟶ affineLineSpace B S hS))).trans
      (globalFunctionsHomEquiv B S hS W).symm)

/-! ### Separatedness of the projection -/

/-- **The projection of the relative affine line to `V` is a separated morphism of algebraic
spaces.**  Affine space is affine over its base, an affine morphism of schemes is separated,
and separatedness of a represented morphism of algebraic spaces is separatedness of the
underlying morphism of schemes. -/
@[ega "IV 20.5.4" "partial"]
theorem isSeparated_relativeAffineLineProjection (V : BigFppfOver B S hS) :
    IsSeparated B S hS (yoneda.map (relativeAffineLineProjection B S hS V)) := by
  refine (isSeparated_yoneda_map_iff B S hS (relativeAffineLineProjection B S hS V)).2 ?_
  rw [toScheme_map_relativeAffineLineProjection]
  exact _root_.AlgebraicGeometry.IsSeparated.of_isAffineHom
    (𝔸(PUnit.{u + 1}; (BigFppfOver.toScheme B S hS).obj V) ↘
      (BigFppfOver.toScheme B S hS).obj V)

/-- **The projection of the relative affine line to `V` is a quasi-separated morphism of
algebraic spaces.**  This is the hypothesis Stacks 03KS asks of the second factor of a
composite in order to conclude that the first factor is quasi-compact. -/
theorem isQuasiSeparated_relativeAffineLineProjection (V : BigFppfOver B S hS) :
    IsQuasiSeparated B S hS (yoneda.map (relativeAffineLineProjection B S hS V)) :=
  isQuasiSeparated_of_isSeparated B S hS (isSeparated_relativeAffineLineProjection B S hS V)

end AlgebraicGeometry.Space

end
