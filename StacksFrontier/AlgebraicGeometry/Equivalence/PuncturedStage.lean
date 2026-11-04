module

public import StacksFrontier.AlgebraicGeometry.StalkAffineNhdsLimit.Basic

/-!
# The stages of a punctured inverse system, identified

`AlgebraicGeometry.opensDiagram` and `AlgebraicGeometry.opensCone` present the inverse system of
preimages of a fixed open `U ⊆ D i` in the stages below `i`, and its limit cone.  Both are built
from `AlgebraicGeometry.Scheme.Hom.resLE`, so each stage carries an open immersion into the
corresponding stage of the original system, and the two commute with the transitions and with the
legs of the cone.  This file records those two equations, and — for the system of affine open
neighbourhoods of a point of a scheme — identifies the stage at an object of the over category as
the preimage of the open in the *smaller* neighbourhood.

## Why these are needed

Tag [0BPA](https://stacks.math.columbia.edu/tag/0BPA)'s descent step for
[Stacks, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q) runs over the punctured system of
affine open neighbourhoods of a closed point, and the two objects it descends live at the stage
indexed by the *identity* morphism.  That stage is **not** the open it looks like: the stage at
`CategoryTheory.Over.mk (𝟙 W)` is the preimage of `W.ι ⁻¹ᵁ V` along
`(affineOpenNhdsDiagram S x).map (𝟙 W)`, which is `S.homOfLE (le_refl _)` and not the identity, so
the identification needs `CategoryTheory.Functor.map_id` and
`AlgebraicGeometry.Scheme.Hom.id_preimage` rather than holding by `rfl`.
`AlgebraicGeometry.map_preimage_affineOpenNhds` settles this uniformly for every stage, and is
what lets the two charts over the stage be written down at all.

## Main results

* `AlgebraicGeometry.eqToHom_toScheme_ι`: the transport attached to an equality of opens is
  compatible with their inclusions.  This is what makes an identification of two opens usable as
  an isomorphism of the open subschemes without leaving an untreated `CategoryTheory.eqToHom`.
* `AlgebraicGeometry.preimage_inf_self`: inside an open subscheme, the preimage of an open of the
  ambient scheme and the preimage of its intersection with that subscheme agree.
* `AlgebraicGeometry.opensDiagram_map_comp_ι` and `AlgebraicGeometry.opensCone_π_comp_ι`: the
  transitions of a punctured system, and the legs of its limit cone, commute with the inclusions
  of the stages into the stages of the original system.
* `AlgebraicGeometry.affineOpenNhdsDiagram_map_comp_ι` and
  `AlgebraicGeometry.map_preimage_affineOpenNhds`: the transitions of the system of affine open
  neighbourhoods of a point are the inclusions of the smaller neighbourhood, and the stages of the
  punctured system are the punctured smaller neighbourhoods.

## Implementation notes

`AlgebraicGeometry.affineOpenNhdsDiagram_map_comp_ι` cannot be proved by
`rw [Scheme.homOfLE_ι]`: the two instance paths from `AlgebraicGeometry.Scheme.Opens` to `LE`
make the rewrite report a missing pattern that is character-for-character present (the same
behaviour as `rw` on `X.Opens`), while `exact S.homOfLE_ι _` succeeds after the
`AlgebraicGeometry.affineOpenNhdsDiagram_map` rewrite.

The index category of `AlgebraicGeometry.opensDiagram` is `Type u` with `Category.{u}`, the same
universe as the schemes — a `Category.{w}` index category does not typecheck there — so the
generic lemmas below are stated at that shape.

No `@[stacks]` attribute is attached: Tag 0E8Q's `equivalence` label has the single
`CategoryTheory.Functor.IsEquivalence` assertion as its covering set.

## References

* [Stacks Project, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q)
* [Stacks Project, Tag 0BPA](https://stacks.math.columbia.edu/tag/0BPA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The transport attached to an equality of opens is compatible with their inclusions.** -/
theorem eqToHom_toScheme_ι {X : Scheme.{u}} {U U' : X.Opens} (h : U = U') :
    eqToHom (congrArg (fun O : X.Opens ↦ (O : Scheme.{u})) h) ≫ U'.ι = U.ι := by
  subst h; simp

/-- Inside an open subscheme, cutting down an open of the ambient scheme to the subscheme is the
same as first intersecting it with the subscheme. -/
theorem preimage_inf_self {X : Scheme.{u}} (T : X.Opens) (V : X.Opens) :
    T.ι ⁻¹ᵁ (V ⊓ T) = T.ι ⁻¹ᵁ V :=
  TopologicalSpace.Opens.ext (Set.ext fun w ↦ ⟨fun h ↦ h.1, fun h ↦ ⟨h, w.2⟩⟩)

section

variable {J : Type u} [Category.{u} J] (D : J ⥤ Scheme.{u})
  [∀ {a b : J} (f : a ⟶ b), IsAffineHom (D.map f)] (i : J) (U : (D.obj i).Opens)

omit [∀ {a b : J} (f : a ⟶ b), IsAffineHom (D.map f)] in
/-- **The transitions of a punctured system commute with the inclusions of its stages.** -/
theorem opensDiagram_map_comp_ι {j k : Over i} (e : j ⟶ k) :
    (opensDiagram D i U).map e ≫ Scheme.Opens.ι (D.map k.hom ⁻¹ᵁ U) =
      Scheme.Opens.ι (D.map j.hom ⁻¹ᵁ U) ≫ D.map e.left :=
  Scheme.Hom.resLE_comp_ι _ _

omit [∀ {a b : J} (f : a ⟶ b), IsAffineHom (D.map f)] in
/-- **The legs of the limit cone of a punctured system commute with the inclusions of its
stages.** -/
theorem opensCone_π_comp_ι (c : Cone D) (j : Over i) :
    (opensCone D c i U).π.app j ≫ Scheme.Opens.ι (D.map j.hom ⁻¹ᵁ U) =
      Scheme.Opens.ι (c.π.app i ⁻¹ᵁ U) ≫ c.π.app j.left :=
  Scheme.Hom.resLE_comp_ι _ _

end

variable {S : Scheme.{u}} (V : S.Opens) (x : S)

/-- **A transition of the system of affine open neighbourhoods is the inclusion of the smaller
one.** -/
theorem affineOpenNhdsDiagram_map_comp_ι (W' : AffineOpenNhds S x) (j : Over W') :
    (affineOpenNhdsDiagram S x).map j.hom ≫ Scheme.Opens.ι (X := S) W'.obj.1 =
      Scheme.Opens.ι (X := S) j.left.obj.1 := by
  rw [affineOpenNhdsDiagram_map]
  exact S.homOfLE_ι _

/-- **The stage of the punctured system of affine open neighbourhoods at an object of the over
category is the punctured smaller neighbourhood.**  At the identity stage this is *not* a
definitional identity: the transition at `𝟙 W'` is `S.homOfLE (le_refl _)`, not the identity
morphism. -/
theorem map_preimage_affineOpenNhds (W' : AffineOpenNhds S x) (j : Over W') :
    (affineOpenNhdsDiagram S x).map j.hom ⁻¹ᵁ (Scheme.Opens.ι (X := S) W'.obj.1 ⁻¹ᵁ V) =
      Scheme.Opens.ι (X := S) j.left.obj.1 ⁻¹ᵁ V :=
  congrArg (· ⁻¹ᵁ V) (affineOpenNhdsDiagram_map_comp_ι x W' j)

end AlgebraicGeometry

end
