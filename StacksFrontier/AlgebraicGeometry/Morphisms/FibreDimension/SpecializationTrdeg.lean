module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Specialization
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.SpecializationTrdeg
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricFieldChange.TangentFibre

/-!
# Transcendence degree of residue fields along a specialization in a fibre

Let `f : X ⟶ S` be a morphism locally of finite type and let `x ⤳ x'` be a nontrivial
specialization of points of `X` with a common image `s` in `S`. The residue field `κ(x)` then has
strictly larger transcendence degree over `κ(s)` than `κ(x')` does.

## Main results

* `AlgebraicGeometry.nonempty_fiberResidueFieldAlgEquiv` identifies the residue field of the
  fibre `X_{f x}` at `f.asFiber x` with `κ(x)` as `κ(f x)`-algebras.
* `AlgebraicGeometry.trdeg_residueField_asFiber` compares the two `κ(f x)`-algebra structures
  under which the residue field at `x` can be read: as `κ(x)` through
  `AlgebraicGeometry.Scheme.Hom.residueFieldMap`, and as the residue field of the fibre at
  `f.asFiber x` through `AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField`. The transcendence
  degrees agree.
* `AlgebraicGeometry.trdeg_residueField_fiber_point` is the same comparison at a point of the
  fibre over an arbitrary `s` with `f x = s`.
* `AlgebraicGeometry.trdeg_residueField_fiber_lt_of_specialization` is the strict inequality of
  transcendence degrees, part (3) of Stacks 06RU. Parts (1) and (2) are
  `AlgebraicGeometry.topologicalKrullDimAt_fiber_le_of_specialization` and
  `AlgebraicGeometry.ringKrullDim_fiber_stalk_lt_of_specialization` in
  `StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Specialization`.

## Implementation notes

The engine is `AlgebraicGeometry.trdeg_residueField_lt_of_specialization` (Stacks 0A21), which
needs a base that is the spectrum of a field. It is applied to the fibre `X_s` over
`Spec κ(s)`, and the two points of the fibre are the canonical inverse images of `x` and `x'`
under `AlgebraicGeometry.Scheme.Hom.fiberHomeo`, as in parts (1) and (2).

Transporting that inequality back to `κ(x)` and `κ(x')` is the whole content of
`trdeg_residueField_asFiber`, because the two files use different conventions for the algebra
structure on a residue field: Stacks 0A21 is stated for a morphism to the spectrum of a literal
field, where the structure map is the composite of global sections with evaluation at the point
(`Scheme.ΓSpecIso` and `Scheme.Γevaluation`), while a fibre of a morphism of schemes comes with
the residue field of the image point as its base, through `Scheme.Hom.residueFieldMap`. The
identification of residue fields is `AlgebraicGeometry.fiberResidueFieldEquiv`, whose
compatibility with the two structure maps is read off
`AlgebraicGeometry.fiberResidueFieldEquiv_spec` after both are turned into morphisms of affine
schemes. The resulting `AlgEquiv` is the same one that
`AlgebraicGeometry.topologicalKrullDimAt_fiber_eq_ringKrullDim_stalk_add_trdeg` builds inside its
proof; here it is isolated so that a transcendence degree in a fibre can be rewritten without the
dimension formula.

The comparison with an arbitrary `s` is obtained from the one at `s = f x` by substitution, which
is why the base point of the fibre is written `(f.fiberHomeo s).symm ⟨x, hx⟩`: at `hx = rfl` that
is `AlgebraicGeometry.Scheme.Hom.asFiber` by definition.

## References

* [Stacks Project, Tag 06RU](https://stacks.math.columbia.edu/tag/06RU)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- **The residue field of a fibre point is the residue field of the point.** The residue field
of the fibre of `f` through `x` at `f.asFiber x` is `κ(x)` as an algebra over `κ(f x)`, the
fibre's residue field read through `f.fiberToSpecResidueField` and `κ(x)` through
`f.residueFieldMap`.

The underlying ring isomorphism is `AlgebraicGeometry.fiberResidueFieldEquiv`; what is proved
here is its compatibility with the two structure maps, read off
`AlgebraicGeometry.fiberResidueFieldEquiv_spec` after both are turned into morphisms of affine
schemes. -/
public theorem nonempty_fiberResidueFieldAlgEquiv (f : X ⟶ S) (x : X) :
    letI : Algebra (S.residueField (f x)) ((f.fiber (f x)).residueField (f.asFiber x)) :=
      ((Scheme.ΓSpecIso (.of (S.residueField (f x)))).inv ≫
        (f.fiberToSpecResidueField (f x)).appTop ≫
          (f.fiber (f x)).Γevaluation (f.asFiber x)).hom.toAlgebra
    letI : Algebra (S.residueField (f x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    Nonempty (((f.fiber (f x)).residueField (f.asFiber x) : Type u) ≃ₐ[S.residueField (f x)]
      (X.residueField x : Type u)) := by
  let k := S.residueField (f x)
  let g : f.fiber (f x) ⟶ Spec (.of k) := f.fiberToSpecResidueField (f x)
  let : Algebra k ((f.fiber (f x)).residueField (f.asFiber x)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫
      (f.fiber (f x)).Γevaluation (f.asFiber x)).hom.toAlgebra
  let : Algebra k (X.residueField x) := (f.residueFieldMap x).hom.toAlgebra
  have halg : CommRingCat.ofHom
      (algebraMap k ((f.fiber (f x)).residueField (f.asFiber x))) =
      (Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫
        (f.fiber (f x)).Γevaluation (f.asFiber x) := rfl
  have hspec : Spec.map (CommRingCat.ofHom
      (algebraMap k ((f.fiber (f x)).residueField (f.asFiber x)))) =
      (f.fiber (f x)).fromSpecResidueField (f.asFiber x) ≫ g := by
    rw [← cancel_mono (Spec (CommRingCat.of k)).isoSpec.hom]
    show _ ≫ (Spec _).toSpecΓ = _ ≫ (Spec _).toSpecΓ
    conv_rhs => rw [Category.assoc, Scheme.toSpecΓ_naturality]
    simp only [Scheme.fromSpecResidueField, Category.assoc,
      Scheme.fromSpecStalk_toSpecΓ_assoc, ← Spec.map_comp]
    rw [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Spec.map_inj, halg]
    show ((((Scheme.ΓSpecIso (CommRingCat.of k)).hom ≫
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv) ≫ g.appTop) ≫
        (f.fiber (f x)).Γevaluation (f.asFiber x)) = _
    rw [Iso.hom_inv_id, Category.id_comp]
    rfl
  refine ⟨AlgEquiv.ofRingEquiv (f := fiberResidueFieldEquiv f x) fun z => ?_⟩
  have hh : CommRingCat.ofHom ((fiberResidueFieldEquiv f x).toRingHom.comp
      (algebraMap k ((f.fiber (f x)).residueField (f.asFiber x)))) =
      CommRingCat.ofHom (algebraMap k (X.residueField x)) := by
    apply Spec.map_injective
    rw [CommRingCat.ofHom_comp, Spec.map_comp, hspec, ← Category.assoc,
      fiberResidueFieldEquiv_spec, f.asFiberHom_fiberToSpecResidueField]
    rfl
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hh) z

/-- The residue field of the fibre of `f` through `x` at `f.asFiber x`, as an algebra over
`κ(f x)` through `f.fiberToSpecResidueField`, has the same transcendence degree as `κ(x)` as an
algebra over `κ(f x)` through `f.residueFieldMap`. -/
public theorem trdeg_residueField_asFiber (f : X ⟶ S) (x : X) :
    letI : Algebra (S.residueField (f x)) ((f.fiber (f x)).residueField (f.asFiber x)) :=
      ((Scheme.ΓSpecIso (.of (S.residueField (f x)))).inv ≫
        (f.fiberToSpecResidueField (f x)).appTop ≫
          (f.fiber (f x)).Γevaluation (f.asFiber x)).hom.toAlgebra
    letI : Algebra (S.residueField (f x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    Algebra.trdeg (S.residueField (f x)) ((f.fiber (f x)).residueField (f.asFiber x)) =
      Algebra.trdeg (S.residueField (f x)) (X.residueField x) := by
  let : Algebra (S.residueField (f x)) ((f.fiber (f x)).residueField (f.asFiber x)) :=
    ((Scheme.ΓSpecIso (.of (S.residueField (f x)))).inv ≫
      (f.fiberToSpecResidueField (f x)).appTop ≫
        (f.fiber (f x)).Γevaluation (f.asFiber x)).hom.toAlgebra
  let : Algebra (S.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  exact (nonempty_fiberResidueFieldAlgEquiv f x).elim fun ex => ex.trdeg_eq

/-- The residue field of the fibre of `f` over `s` at the point corresponding to `x`, as an
algebra over `κ(s)` through `f.fiberToSpecResidueField`, has the same transcendence degree as
`κ(x)` as an algebra over `κ(s)` through `f.residueFieldMap`. -/
public theorem trdeg_residueField_fiber_point (f : X ⟶ S) {x : X} {s : S} (hx : f x = s) :
    letI : Algebra (S.residueField s)
        ((f.fiber s).residueField ((f.fiberHomeo s).symm ⟨x, hx⟩)) :=
      ((Scheme.ΓSpecIso (.of (S.residueField s))).inv ≫
        (f.fiberToSpecResidueField s).appTop ≫
          (f.fiber s).Γevaluation ((f.fiberHomeo s).symm ⟨x, hx⟩)).hom.toAlgebra
    letI : Algebra (S.residueField s) (X.residueField x) :=
      ((S.residueFieldCongr hx).inv ≫ f.residueFieldMap x).hom.toAlgebra
    Algebra.trdeg (S.residueField s)
        ((f.fiber s).residueField ((f.fiberHomeo s).symm ⟨x, hx⟩)) =
      Algebra.trdeg (S.residueField s) (X.residueField x) := by
  subst hx
  exact trdeg_residueField_asFiber f x

/-- **Stacks 06RU, part (3).** Let `f : X ⟶ S` be locally of finite type and let `x ⤳ x'` be a
nontrivial specialization of points of `X` lying over the same point `s` of `S`. Then the
transcendence degree of `κ(x)` over `κ(s)` is strictly larger than that of `κ(x')`. -/
@[stacks 06RU "part (3): the strict inequality of transcendence degrees
`trdeg_{κ(s)} κ(x) > trdeg_{κ(s)} κ(x')` along a nontrivial specialization `x ⤳ x'` inside a
fibre, for `f` locally of finite type. Each residue field is a `κ(s)`-algebra through
`AlgebraicGeometry.Scheme.Hom.residueFieldMap`, and the comparison is between Mathlib's
cardinal-valued `Algebra.trdeg`. Parts (1) and (2) are
`AlgebraicGeometry.topologicalKrullDimAt_fiber_le_of_specialization` and
`AlgebraicGeometry.ringKrullDim_fiber_stalk_lt_of_specialization`."]
public theorem trdeg_residueField_fiber_lt_of_specialization (f : X ⟶ S)
    [LocallyOfFiniteType f] {x x' : X} (hxx' : x ⤳ x') (hne : x ≠ x')
    {s : S} (hx : f x = s) (hx' : f x' = s) :
    letI : Algebra (S.residueField s) (X.residueField x) :=
      ((S.residueFieldCongr hx).inv ≫ f.residueFieldMap x).hom.toAlgebra
    letI : Algebra (S.residueField s) (X.residueField x') :=
      ((S.residueFieldCongr hx').inv ≫ f.residueFieldMap x').hom.toAlgebra
    Algebra.trdeg (S.residueField s) (X.residueField x') <
      Algebra.trdeg (S.residueField s) (X.residueField x) := by
  have hft : LocallyOfFiniteType (f.fiberToSpecResidueField s) := by
    show LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField s))
    infer_instance
  have hyy' : (f.fiberHomeo s).symm ⟨x, hx⟩ ⤳ (f.fiberHomeo s).symm ⟨x', hx'⟩ := by
    simpa only [((f.fiberHomeo s).symm.isInducing.specializes_iff), subtype_specializes_iff]
      using hxx'
  have hyne : (f.fiberHomeo s).symm ⟨x, hx⟩ ≠ (f.fiberHomeo s).symm ⟨x', hx'⟩ :=
    fun he => hne (by simpa using congrArg (f.fiberι s) he)
  have key := trdeg_residueField_lt_of_specialization (S.residueField s) (f.fiber s)
    (f.fiberToSpecResidueField s) hyy' hyne
  rwa [trdeg_residueField_fiber_point f hx, trdeg_residueField_fiber_point f hx'] at key

end AlgebraicGeometry

end
