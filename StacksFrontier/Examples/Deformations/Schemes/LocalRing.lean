module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import StacksFrontier.Deformation.Examples.Geometric.Rings
public import StacksFrontier.Examples.Deformations.Schemes.SpecialFibre

/-!
# Local rings of scheme deformations

Taking the local ring at a point of a scheme over a field sends deformations of the scheme to
deformations of that local ring. This file builds that assignment and checks it is a functor
over the category `𝒞_Λ` of Artinian local `Λ`-algebras with residue field `k`.

On objects: a deformation `P` of `X` over a base `A` has a flat structure morphism, so the
stalk of `P.scheme` at the image of the chosen point `x` is a flat `A`-algebra, and
`special_stalk_pushout_any` says the square identifying the stalk of `X` at `x` as its special
fibre is a pushout — exactly the data of a deformation of `𝒪_{X,x}`.

On morphisms: a morphism `f : P ⟶ Q` of deformations gives a morphism of total spaces
`f.map : Q.scheme ⟶ P.scheme` carrying the special fibres to each other, hence a map of stalks.
That this map again exhibits a pushout square is where `isPushout_of_flat_of_residue` is used:
the square becomes a pushout after reducing modulo the maximal ideal of `Q`'s base, because
both deformations restrict to `𝒪_{X,x}` there, and the reduction is nilpotent because the base
is Artinian local.

## Main definitions

* `Deformation.Examples.stalkFlatAlgebra`: the stalk of a deformation, as a flat algebra over
  the Artinian base.
* `Deformation.Examples.residueBaseHom`: the morphism of `𝒞_Λ` from an object to the residue
  field.
* `Deformation.Examples.stalkDeformation`: the stalk of a deformation, as a deformation of the
  local ring of `X`.
* `Deformation.Examples.stalkMorphismRingHom`: the map of stalks induced by a morphism of
  deformations.
* `Deformation.Examples.localRingDeformationFunctor`: the resulting based functor of
  deformation categories.

## Main results

* `Deformation.Examples.localRingDeformationFunctor_fiber`,
  `Deformation.Examples.localRingDeformationFunctor_specialMap` and
  `Deformation.Examples.localRingDeformationFunctor_map` identify the underlying algebra, the
  special-fibre map and the map on morphisms of the image deformation with the stalk, the stalk
  map of the special-fibre immersion and the stalk map of the morphism.

## Implementation notes

The image of `x` under the special-fibre immersion of `P` depends on `P`, so a morphism of
deformations moves the point at which the stalk is taken; `stalkMorphismRingHom` therefore
composes the stalk map of `f.map` with the transport along the equality of points that
`special_compat` gives. The three characterization lemmas are stated as heterogeneous
equalities for the same reason: the two stalk types involved are equal, but only after that
transport, so a homogeneous equation does not typecheck.

The algebra structure on the local ring of `X` is the one induced by the structure morphism of
`X`, introduced by `letI` in each statement.

## References

* [Stacks Project, Tag 0DZM](https://stacks.math.columbia.edu/tag/0DZM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

/-- The stalk of a deformation of `X` at the image of a point of `X`, as a flat algebra over
the Artinian local base of the deformation. -/
noncomputable def stalkFlatAlgebra
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (X : Over (Spec (.of k))) (x : X.left)
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    FlatAlgebraCategory (Λ := Λ) (k := k) := by
  let y := P.specialMap x
  let : Flat P.toBase := P.flat
  letI : Algebra P.base ((Spec (.of P.base)).presheaf.stalk (P.toBase.base y)) :=
    StructureSheaf.stalkAlgebra P.base (P.toBase.base y)
  letI : Algebra P.base (P.scheme.presheaf.stalk y) :=
    ((P.toBase.stalkMap y).hom.comp (algebraMap P.base _)).toAlgebra
  exact
    { base := P.base
      fiber := P.scheme.presheaf.stalk y
      algebra := inferInstance
      flat := flat_stalk_algebra_of_flat P.toBase y }

/-- The morphism of `𝒞_Λ` from an object to the residue field: reduce modulo the maximal ideal
and transport along the chosen identification of the residue field with `k`. -/
noncomputable def residueBaseHom
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (A : ArtinianLocalAlgCat.{u, u, u} Λ k) :
    A ⟶ (residueFieldAlgebra (Λ := Λ) (k := k) k).base := by
  let r : A →ₐ[Λ] k := A.residueEquiv.toAlgHom.comp
    (IsScalarTower.toAlgHom Λ A (IsLocalRing.ResidueField A))
  have hr : Function.Surjective r := by
    intro b
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (A.residueEquiv.symm b)
    exact ⟨a, by simpa [r] using congrArg A.residueEquiv ha⟩
  refine ⟨r, IsLocalHom.of_surjective _ hr, fun a => ?_⟩
  change r a = A.residueEquiv (IsLocalRing.residue A a)
  simp [r, IsLocalRing.ResidueField.algebraMap_eq]

/-- The morphisms to the residue field are compatible with every morphism of `𝒞_Λ`. -/
theorem residueBaseHom_comp
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {A B : ArtinianLocalAlgCat.{u, u, u} Λ k} (f : A ⟶ B) :
    f ≫ residueBaseHom B = residueBaseHom A := by
  ext a
  exact f.residue_comm a

/-- The stalk of a deformation of `X` at the image of `x`, as a deformation of the local ring
of `X` at `x`: the flat algebra of `stalkFlatAlgebra` together with the pushout square of
`special_stalk_pushout_any`. -/
noncomputable def stalkDeformation
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (X : Over (Spec (.of k))) (x : X.left)
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    letI : Algebra k (X.left.presheaf.stalk x) :=
      letI : Algebra k ((Spec (.of k)).presheaf.stalk (X.hom.base x)) :=
        StructureSheaf.stalkAlgebra k (X.hom.base x)
      ((X.hom.stalkMap x).hom.comp (algebraMap k _)).toAlgebra
    ringDeformationCategory (Λ := Λ) (k := k) (X.left.presheaf.stalk x) := by
  letI : Algebra k (X.left.presheaf.stalk x) :=
    letI : Algebra k ((Spec (.of k)).presheaf.stalk (X.hom.base x)) :=
      StructureSheaf.stalkAlgebra k (X.hom.base x)
    ((X.hom.stalkMap x).hom.comp (algebraMap k _)).toAlgebra
  let Z := stalkFlatAlgebra X x P
  let h : Z ⟶ residueFieldAlgebra (Λ := Λ) (k := k) (X.left.presheaf.stalk x) :=
    { base := residueBaseHom P.base
      map := CommRingCat.ofHom (P.specialMap.stalkMap x).hom
      cartesian := special_stalk_pushout_any X x P }
  exact Over.mk h

/-- The map of stalks induced by a morphism of deformations of `X`: the stalk map of the
morphism of total spaces, composed with the transport along the equality of points that the
compatibility with the special fibres gives. -/
noncomputable def stalkMorphismRingHom
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (X : Over (Spec (.of k))) (x : X.left)
    {P Q : SchemeDeformationCategory (Λ := Λ) (k := k) X} (f : P ⟶ Q) :
    P.scheme.presheaf.stalk (P.specialMap x) →+*
      Q.scheme.presheaf.stalk (Q.specialMap x) := by
  have h : f.map (Q.specialMap x) = P.specialMap x := by
    have hw := congrArg (fun g : X.left ⟶ P.scheme => g.base x) f.special_compat
    simpa [Scheme.Hom.comp_apply] using hw
  exact (f.map.stalkMap (Q.specialMap x)).hom.comp
    (eqToHom (congrArg (fun y : P.scheme => P.scheme.presheaf.stalk y) h.symm)).hom

/-- A morphism of deformations carries the image of `x` in `Q`'s special fibre to its image in
`P`'s. -/
private theorem map_specialMap_apply
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (X : Over (Spec (.of k))) (x : X.left)
    {P Q : SchemeDeformationCategory (Λ := Λ) (k := k) X} (f : P ⟶ Q) :
    f.map (Q.specialMap x) = P.specialMap x := by
  have hw := congrArg (fun g : X.left ⟶ P.scheme => g.base x) f.special_compat
  simpa [Scheme.Hom.comp_apply] using hw

/-- The identity morphism of deformations induces the identity on stalks. -/
theorem stalkMorphismRingHom_id
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (X : Over (Spec (.of k))) (x : X.left)
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    stalkMorphismRingHom X x (𝟙 P) = RingHom.id _ := by
  ext a
  change ((𝟙 P.scheme : P.scheme ⟶ P.scheme).stalkMap (P.specialMap x)).hom a = a
  rw [Scheme.Hom.stalkMap_id]
  rfl

/-- The map on stalks induced by a composite of morphisms of deformations is the composite of
the induced maps. -/
theorem stalkMorphismRingHom_comp
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (X : Over (Spec (.of k))) (x : X.left)
    {P Q R : SchemeDeformationCategory (Λ := Λ) (k := k) X} (f : P ⟶ Q) (g : Q ⟶ R) :
    stalkMorphismRingHom X x (f ≫ g) =
      (stalkMorphismRingHom X x g).comp (stalkMorphismRingHom X x f) := by
  have hf := map_specialMap_apply X x f
  have hg := map_specialMap_apply X x g
  have hfg : (g.map ≫ f.map) (R.specialMap x) = P.specialMap x := by
    rw [Scheme.Hom.comp_apply, hg, hf]
  exact stalkMap_comp_transport f.map g.map (R.specialMap x)
    (Q.specialMap x) (P.specialMap x) hg hf hfg

/-- The stalk map of the special-fibre immersion of `P` factors through the one of `Q` along the
map of stalks induced by a morphism `P ⟶ Q`. -/
theorem stalkMorphismRingHom_special
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (X : Over (Spec (.of k))) (x : X.left)
    {P Q : SchemeDeformationCategory (Λ := Λ) (k := k) X} (f : P ⟶ Q) :
    (P.specialMap.stalkMap x).hom =
      (Q.specialMap.stalkMap x).hom.comp (stalkMorphismRingHom X x f) := by
  exact stalkMap_of_comp_eq Q.specialMap f.map P.specialMap f.special_compat x
    (map_specialMap_apply X x f)

/-- The map of stalks induced by a morphism of deformations is compatible with the structure
maps from the Artinian bases. -/
theorem stalkMorphismRingHom_base
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (X : Over (Spec (.of k))) (x : X.left)
    {P Q : SchemeDeformationCategory (Λ := Λ) (k := k) X} (f : P ⟶ Q) :
    FlatAlgebraCategory.structureMap
        (stalkFlatAlgebra X x P) ≫ CommRingCat.ofHom (stalkMorphismRingHom X x f) =
      FlatAlgebraCategory.baseMap f.base ≫
        FlatAlgebraCategory.structureMap (stalkFlatAlgebra X x Q) := by
  have hp := map_specialMap_apply X x f
  change (StructureSheaf.toStalk P.base (P.toBase (P.specialMap x)) ≫
      P.toBase.stalkMap (P.specialMap x)) ≫
      (eqToHom (congrArg P.scheme.presheaf.stalk hp.symm) ≫
        f.map.stalkMap (Q.specialMap x)) =
    CommRingCat.ofHom f.base.hom.toRingHom ≫
      StructureSheaf.toStalk Q.base (Q.toBase (Q.specialMap x)) ≫
        Q.toBase.stalkMap (Q.specialMap x)
  rw [← Category.assoc, stalkBaseMap_transport P.toBase hp.symm]
  exact stalkBaseMap_natural f.base.hom.toRingHom f.map P.toBase Q.toBase
    f.cartesian.w (Q.specialMap x)

/-- A morphism of deformations of `X` induces a morphism of the flat algebras of stalks. The
cartesian condition is the recognition criterion `isPushout_of_flat_of_residue`: the square
becomes a pushout after reducing along the residue map of `Q`'s base, whose kernel is nilpotent
because that base is Artinian local. -/
noncomputable def stalkFlatHom
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (X : Over (Spec (.of k))) (x : X.left)
    {P Q : SchemeDeformationCategory (Λ := Λ) (k := k) X} (f : P ⟶ Q) :
    stalkFlatAlgebra X x P ⟶ stalkFlatAlgebra X x Q where
  base := f.base
  map := CommRingCat.ofHom (stalkMorphismRingHom X x f)
  cartesian := by
    let : Algebra k (X.left.presheaf.stalk x) :=
      letI : Algebra k ((Spec (.of k)).presheaf.stalk (X.hom.base x)) :=
        StructureSheaf.stalkAlgebra k (X.hom.base x)
      ((X.hom.stalkMap x).hom.comp (algebraMap k _)).toAlgebra
    let DP := stalkDeformation X x P
    let DQ := stalkDeformation X x Q
    have hr : Function.Surjective (residueBaseHom Q.base).hom.toRingHom := by
      intro a
      obtain ⟨b, rfl⟩ := Q.base.residueEquiv.surjective a
      obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective b
      exact ⟨c, rfl⟩
    have hn : IsNilpotent (RingHom.ker (residueBaseHom Q.base).hom.toRingHom) := by
      change IsNilpotent (RingHom.ker (Deformation.Artin.residueMap Q.base))
      rw [residueMap_ker, ← IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal Q.base) bot_ne_top]
      exact IsArtinianRing.isNilpotent_jacobson_bot
    refine isPushout_of_flat_of_residue _ _ _ _
      (FlatAlgebraCategory.baseMap (residueBaseHom Q.base))
      (FlatAlgebraCategory.structureMap
        (residueFieldAlgebra (Λ := Λ) (k := k) (X.left.presheaf.stalk x)))
      DP.hom.map DQ.hom.map (stalkMorphismRingHom_base X x f)
      (CommRingCat.hom_ext (stalkMorphismRingHom_special X x f).symm) ?_
      DQ.hom.cartesian hr hn (stalkFlatAlgebra X x Q).flat
    have hb : CommRingCat.ofHom f.base.hom.toRingHom ≫
        CommRingCat.ofHom (residueBaseHom Q.base).hom.toRingHom =
      CommRingCat.ofHom (residueBaseHom P.base).hom.toRingHom :=
      congrArg (fun t : P.base ⟶ _ => CommRingCat.ofHom t.hom.toRingHom)
        (residueBaseHom_comp f.base)
    change IsPushout _ (CommRingCat.ofHom f.base.hom.toRingHom ≫
      CommRingCat.ofHom (residueBaseHom Q.base).hom.toRingHom) _ _
    rw [hb]
    exact DP.hom.cartesian

/-- A morphism of deformations of `X` induces a morphism of the deformations of the local ring
of `X` at `x`. -/
noncomputable def stalkDeformationHom
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (X : Over (Spec (.of k))) (x : X.left)
    {P Q : SchemeDeformationCategory (Λ := Λ) (k := k) X} (f : P ⟶ Q) :
    stalkDeformation X x P ⟶ stalkDeformation X x Q :=
  Over.homMk (stalkFlatHom X x f) <| FlatAlgebraCategory.Hom.ext (residueBaseHom_comp f.base)
    (CommRingCat.hom_ext (stalkMorphismRingHom_special X x f).symm)

/-- Composing a ring map with the transport along an equality of its source is, up to the
transport of types, the map itself. -/
theorem ringHom_comp_eqToHom_heq {A B C : CommRingCat.{u}}
    (e : A = B) (f : B ⟶ C) : HEq (f.hom.comp (eqToHom e).hom) f.hom := by
  subst B
  rfl

/-- **Stacks 0DZM.** Taking the local ring at a point of a scheme defines a functor of
deformation categories over the category of Artinian local algebras. -/
@[stacks 0DZM "the functor"]
noncomputable def localRingDeformationFunctor
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (X : Over (Spec (.of k))) (x : X.left) :
    letI : Algebra k (X.left.presheaf.stalk x) :=
      letI : Algebra k ((Spec (.of k)).presheaf.stalk (X.hom.base x)) :=
        StructureSheaf.stalkAlgebra k (X.hom.base x)
      ((X.hom.stalkMap x).hom.comp (algebraMap k _)).toAlgebra
    BasedFunctor
      (BasedCategory.ofFunctor
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X))
      (BasedCategory.ofFunctor
        (Over.forget
          (residueFieldAlgebra (Λ := Λ) (k := k) (X.left.presheaf.stalk x)) ⋙
          FlatAlgebraCategory.projection (Λ := Λ) (k := k))) := by
  letI : Algebra k (X.left.presheaf.stalk x) :=
    letI : Algebra k ((Spec (.of k)).presheaf.stalk (X.hom.base x)) :=
      StructureSheaf.stalkAlgebra k (X.hom.base x)
    ((X.hom.stalkMap x).hom.comp (algebraMap k _)).toAlgebra
  exact
    { obj := stalkDeformation X x
      map := stalkDeformationHom X x
      map_id P := Over.OverMorphism.ext <|
        FlatAlgebraCategory.Hom.ext rfl (CommRingCat.hom_ext (stalkMorphismRingHom_id X x P))
      map_comp f g := Over.OverMorphism.ext <|
        FlatAlgebraCategory.Hom.ext rfl (CommRingCat.hom_ext (stalkMorphismRingHom_comp X x f g))
      w := rfl }

/-- **Stacks 0DZM.** The underlying algebra of the image deformation is the stalk of the
deformed scheme at the image of the chosen point. -/
@[stacks 0DZM "fibers"]
theorem localRingDeformationFunctor_fiber
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (X : Over (Spec (.of k))) (x : X.left)
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    letI : Algebra k (X.left.presheaf.stalk x) :=
      letI : Algebra k ((Spec (.of k)).presheaf.stalk (X.hom.base x)) :=
        StructureSheaf.stalkAlgebra k (X.hom.base x)
      ((X.hom.stalkMap x).hom.comp (algebraMap k _)).toAlgebra
    ((localRingDeformationFunctor X x).obj P).left.fiber =
      P.scheme.presheaf.stalk (P.specialMap.base x) := rfl

/-- **Stacks 0DZM.** The special-fibre map of the image is the stalk map of the special-fibre
embedding. -/
@[stacks 0DZM "special-fiber maps"]
theorem localRingDeformationFunctor_specialMap
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (X : Over (Spec (.of k))) (x : X.left)
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    letI : Algebra k (X.left.presheaf.stalk x) :=
      letI : Algebra k ((Spec (.of k)).presheaf.stalk (X.hom.base x)) :=
        StructureSheaf.stalkAlgebra k (X.hom.base x)
      ((X.hom.stalkMap x).hom.comp (algebraMap k _)).toAlgebra
    HEq ((localRingDeformationFunctor X x).obj P).hom.map.hom
      (P.specialMap.stalkMap x).hom := by rfl

/-- **Stacks 0DZM.** On morphisms, the induced algebra map is the stalk map of the morphism
between the deformed schemes. -/
@[stacks 0DZM "morphism maps"]
theorem localRingDeformationFunctor_map
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (X : Over (Spec (.of k))) (x : X.left)
    {P Q : SchemeDeformationCategory (Λ := Λ) (k := k) X} (f : P ⟶ Q) :
    letI : Algebra k (X.left.presheaf.stalk x) :=
      letI : Algebra k ((Spec (.of k)).presheaf.stalk (X.hom.base x)) :=
        StructureSheaf.stalkAlgebra k (X.hom.base x)
      ((X.hom.stalkMap x).hom.comp (algebraMap k _)).toAlgebra
    HEq ((localRingDeformationFunctor X x).map f).left.map.hom
      (f.map.stalkMap (Q.specialMap.base x)).hom := by
  change HEq (stalkMorphismRingHom X x f)
    (f.map.stalkMap (Q.specialMap.base x)).hom
  unfold stalkMorphismRingHom
  exact ringHom_comp_eqToHom_heq _ _

end Deformation.Examples

end
