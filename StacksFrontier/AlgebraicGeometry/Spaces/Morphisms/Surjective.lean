module

public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SurjectivePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints

/-!
# Local criteria for surjectivity of a morphism of algebraic spaces

Surjectivity of a morphism of algebraic spaces over a scheme `S` — surjectivity of the
induced map on the point sets of Stacks 03BU — can be tested after an arbitrary base change
by a scheme, after a base change by an affine scheme only, on a single surjective étale
chart of the target, or on a Zariski covering of the target. It can also be read off a
surjective étale chart of the *source*, or off a surjective morphism between étale charts
of source and target.

For a morphism which is merely representable — with no algebraic-space hypothesis on either
side — surjectivity in the relative sense is already equivalent to surjectivity of the induced
map on points; that equivalence is the second half of this file.

## Main results

* `AlgebraicGeometry.Space.isSurjective_tfae` is **Stacks 03MF**, the seven equivalent
  tests for surjectivity.
* `AlgebraicGeometry.Space.surjective_of_surjective_pointsMap_yoneda_map`: a morphism of the
  big fppf site of `S` which is surjective on the points of the represented presheaves has
  surjective underlying morphism of schemes.
* `AlgebraicGeometry.Space.surjective_iff_pointsMap_surjective_of_representable`: **Stacks
  03MD**, the equivalence of surjectivity and surjectivity on points for a representable
  morphism, with no algebraic-space hypothesis.
  `AlgebraicGeometry.Space.surjective_iff_pointsMap_surjective` is the same equivalence as the
  source states it, carrying the two `IsAlgebraicSpace` hypotheses that the argument does not
  use.

Its substantial implications are isolated as
`AlgebraicGeometry.Space.isSurjective_of_isSurjective_affine_baseChange` — testing
surjectivity on affine base changes suffices — and
`AlgebraicGeometry.Space.exists_pointsMap_eq_of_isSurjective_pullback_snd` — a point of the
base lifts through a surjective base change. The permanence facts they are assembled from are
`AlgebraicGeometry.Space.isSurjective_pullback_snd` and
`AlgebraicGeometry.Space.isSurjective_pullback_fst`, the two projections of a base change of
a surjective morphism, and `AlgebraicGeometry.Space.isEtale_pullback_fst`, the analogue for
étaleness; they are the cases of Stacks 03MH and Stacks 03FU this file needs.

## Implementation notes

The base change of `f : X ⟶ Y` along `g : Z ⟶ Y` is written `pullback.snd f g`, the
projection of the presheaf fibre product `X ×_Y Z` to `Z`; as everywhere in this directory
the fibre product is taken in presheaves on the big fppf site of `S`, and
`AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct` identifies it with the fibre
product in the category of algebraic spaces, which is what the base-change lemma
`AlgebraicGeometry.Space.isSurjective_of_isPullback` of Stacks 03MH is stated for.

Conditions (2), (3), (4) and (6) quantify over schemes in the chosen big fppf site, as
everywhere in this directory. Nothing is lost by that size cutoff: condition (3) is proved
to imply condition (1) using only the spectra of the fields of definition of the points of
`Y`, which lie in the site by construction of
`AlgebraicGeometry.Space.FieldValuedPoint`, and condition (1) implies the others by taking
an étale atlas, which the definition of an algebraic space provides inside the site.

The Zariski covering of condition (7) is a family of open subfunctors as in Stacks 02YY.
The covering produced from surjectivity is the one-member family consisting of the open
subspace cut out by all of the points of the target,
`AlgebraicGeometry.Space.openSubspaceOfPoints`, so no choice is involved.

Representability of a morphism, which is part of surjectivity in the relative sense, is the
only hypothesis the equivalence with surjectivity on points needs. Both directions reduce to a
morphism of schemes in the site, by base changing along a representable morphism — the morphism
out of a field spectrum classifying a given point of the target in one direction, the arbitrary
representable base change that has to be tested in the other. The two halves of the reduced
statement are `AlgebraicGeometry.Space.surjective_pointsMap_yoneda_map` and
`AlgebraicGeometry.Space.surjective_of_surjective_pointsMap_yoneda_map`, and transporting the
second back along the base change is Stacks 03H4,
`AlgebraicGeometry.Space.exists_point_of_isPullback_presheaf`.

For a morphism of schemes in the site, surjectivity on points follows from surjectivity by
Stacks 000R and the residue field at a point of the fibre, while the converse reads a point of
the target as the canonical field-valued point of its residue field, lifts it to a field-valued
point of the source, and takes the underlying scheme point of the lift: equality of the two
classes in the target forces that scheme point to lie over the given one, because a common
field-valued extension of two field-valued points of a scheme witnesses equality of their
image points.

## References

* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03MD](https://stacks.math.columbia.edu/tag/03MD)
* [Stacks Project, Tag 03MF](https://stacks.math.columbia.edu/tag/03MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Surjectivity and base change -/

section BaseChange

variable {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The presheaf fibre product of two morphisms of algebraic spaces, with its projections, is
cartesian in the category of algebraic spaces. -/
private theorem isPullback_homMk_pullback (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Z ⟶ Y) :
    IsPullback
      (ObjectProperty.homMk (pullback.fst f g) :
        (⟨pullback f g, isAlgebraicSpace_pullback B S hS f g hX hZ hY⟩ :
          AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩)
      (ObjectProperty.homMk (pullback.snd f g) :
        (⟨pullback f g, isAlgebraicSpace_pullback B S hS f g hX hZ hY⟩ :
          AlgebraicSpaces B S hS) ⟶ ⟨Z, hZ⟩)
      (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
      (ObjectProperty.homMk g : (⟨Z, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩) :=
  AlgebraicSpaces.isPullback_fiberProduct B S hS
    (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
    (ObjectProperty.homMk g : (⟨Z, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)

/-- A base change of a surjective morphism of algebraic spaces over `S` is surjective, in the
form used by the criteria of Stacks 03MF: the projection `X ×_Y Z ⟶ Z` of the presheaf fibre
product is surjective whenever `f : X ⟶ Y` is.

This is Stacks 03MH, `AlgebraicGeometry.Space.isSurjective_of_isPullback`, transported along
the identification of the presheaf fibre product with the fibre product of algebraic
spaces. -/
theorem isSurjective_pullback_snd (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z)
    (f : X ⟶ Y) (g : Z ⟶ Y) (hf : IsSurjective B S hS f) :
    IsSurjective B S hS (pullback.snd f g) :=
  isSurjective_of_isPullback B S hS (isPullback_homMk_pullback B S hS hX hY hZ f g) hf

/-- The other projection of the same fibre product: `X ×_Y Z ⟶ X` is surjective whenever
`g : Z ⟶ Y` is. This is Stacks 03MH applied to the flipped cartesian square. -/
theorem isSurjective_pullback_fst (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z)
    (f : X ⟶ Y) (g : Z ⟶ Y) (hg : IsSurjective B S hS g) :
    IsSurjective B S hS (pullback.fst f g) :=
  isSurjective_of_isPullback B S hS (isPullback_homMk_pullback B S hS hX hY hZ f g).flip hg

/-- A base change of an étale morphism of algebraic spaces over `S` is étale, in the form
used by the criteria of Stacks 03MF: the projection `X ×_Y Z ⟶ X` is étale whenever
`g : Z ⟶ Y` is. This is Stacks 03FU applied to the flipped cartesian square. -/
theorem isEtale_pullback_fst (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z)
    (f : X ⟶ Y) (g : Z ⟶ Y) (hg : IsEtale B S hS g) :
    IsEtale B S hS (pullback.fst f g) :=
  isEtale_of_isPullback B S hS _ _ _ _
    (isPullback_homMk_pullback B S hS hX hY hZ f g).flip hg

/-- If the base change of `f : X ⟶ Y` along `g : Z ⟶ Y` is surjective then every point of `Z`
has a point of `X` with the same image in `Y`. -/
theorem exists_pointsMap_eq_of_isSurjective_pullback_snd (f : X ⟶ Y) (g : Z ⟶ Y)
    (hp : IsSurjective B S hS (pullback.snd f g)) (z : points B S hS Z) :
    ∃ x, pointsMap B S hS X f x = pointsMap B S hS Z g z := by
  obtain ⟨w, hw⟩ := hp z
  refine ⟨pointsMap B S hS (pullback f g) (pullback.fst f g) w, ?_⟩
  calc pointsMap B S hS X f (pointsMap B S hS (pullback f g) (pullback.fst f g) w)
      = pointsMap B S hS (pullback f g) (pullback.fst f g ≫ f) w := by
        rw [pointsMap_comp]; rfl
    _ = pointsMap B S hS (pullback f g) (pullback.snd f g ≫ g) w := by
        rw [pullback.condition]
    _ = pointsMap B S hS Z g (pointsMap B S hS (pullback f g) (pullback.snd f g) w) := by
        rw [pointsMap_comp]; rfl
    _ = pointsMap B S hS Z g z := by rw [hw]

/-- **Stacks 03MF, (3) implies (1).** A morphism of presheaves on the big fppf site of `S`
whose base change along every morphism from an affine scheme in the site is surjective is
itself surjective. No algebraicity is needed. -/
theorem isSurjective_of_isSurjective_affine_baseChange (f : X ⟶ Y)
    (h : ∀ (W : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj W) →
      ∀ g : yoneda.obj W ⟶ Y, IsSurjective B S hS (pullback.snd f g)) :
    IsSurjective B S hS f := by
  intro y
  obtain ⟨p, rfl⟩ := Quot.exists_rep y
  set A : BigFppfOver B S hS := p.siteObject B S hS Y with hA
  have hAaff : IsAffine ((BigFppfOver.toScheme B S hS).obj A) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of p.carrier)))
  let q : FieldValuedPoint B S hS (yoneda.obj A) :=
    { carrier := p.carrier, field := p.field, contained := p.contained
      toBase := p.toBase, value := 𝟙 A }
  obtain ⟨x, hx⟩ := exists_pointsMap_eq_of_isSurjective_pullback_snd B S hS f
    (yonedaEquiv.symm p.value) (h A hAaff (yonedaEquiv.symm p.value))
    (q.class B S hS (yoneda.obj A))
  exact ⟨x, hx.trans (FieldValuedPoint.pointsMap_class_eq_class B S hS p q)⟩

end BaseChange

/-! ### The seven criteria -/

section Tfae

attribute [local instance] pointTopology

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- An algebraic space has a surjective étale chart `V ⟶ Y` from a scheme in the site. -/
private theorem exists_isSurjective_isEtale_yoneda (hY : IsAlgebraicSpace B S hS Y) :
    ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
      IsSurjective B S hS g ∧ IsEtale B S hS g := by
  obtain ⟨V, g, hgSurj, hgEtale⟩ := hY.exists_atlas
  exact ⟨V, g, (surjective_iff_surjective_pointsMap B S hS Y hY V g).mp hgSurj,
    isEtale_of_presheaf_etale B S hS hgEtale⟩

/-- **Stacks 03MF.** For a morphism `f : X ⟶ Y` of algebraic spaces over `S` the following
are equivalent:

1. `f` is surjective;
2. for every scheme `Z` in the site and every `Z ⟶ Y` the projection `X ×_Y Z ⟶ Z` is
   surjective;
3. the same for every affine scheme `Z` in the site;
4. there is a scheme `V` in the site and a surjective étale `V ⟶ Y` with `X ×_Y V ⟶ V`
   surjective;
5. there is a scheme `U` in the site and a surjective étale `φ : U ⟶ X` with `φ ≫ f`
   surjective;
6. there is a commuting square whose vertical arrows are surjective étale charts
   `U ⟶ X` and `V ⟶ Y` of schemes in the site and whose top arrow `U ⟶ V` is surjective;
7. there is a Zariski covering of `Y` by open subspaces `Y_i` with each `f⁻¹(Y_i) ⟶ Y_i`
   surjective. -/
@[stacks 03MF]
theorem isSurjective_tfae (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) :
    List.TFAE
      [IsSurjective B S hS f,
        ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
          IsSurjective B S hS (pullback.snd f g),
        ∀ (Z : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
          ∀ g : yoneda.obj Z ⟶ Y, IsSurjective B S hS (pullback.snd f g),
        ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
          IsSurjective B S hS g ∧ IsEtale B S hS g ∧
            IsSurjective B S hS (pullback.snd f g),
        ∃ (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X),
          IsSurjective B S hS φ ∧ IsEtale B S hS φ ∧ IsSurjective B S hS (φ ≫ f),
        ∃ (U V : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X) (ψ : yoneda.obj V ⟶ Y)
            (h : yoneda.obj U ⟶ yoneda.obj V),
          φ ≫ f = h ≫ ψ ∧ IsSurjective B S hS φ ∧ IsEtale B S hS φ ∧
            IsSurjective B S hS ψ ∧ IsEtale B S hS ψ ∧ IsSurjective B S hS h,
        ∃ (I : Type u) (U : I → Subfunctor Y), IsZariskiCover B S hS I U ∧
          ∀ i, IsSurjective B S hS (pullback.snd f (U i).ι)] := by
  classical
  tfae_have 1 → 2 := fun hf Z g ↦ isSurjective_pullback_snd B S hS hX hY
    (isAlgebraicSpace_yoneda B S hS Z) f g hf
  tfae_have 2 → 3 := fun h Z _ g ↦ h Z g
  tfae_have 3 → 1 := isSurjective_of_isSurjective_affine_baseChange B S hS f
  tfae_have 4 → 1 := by
    rintro ⟨V, g, hg, -, hp⟩ y
    obtain ⟨z, hz⟩ := hg y
    obtain ⟨x, hx⟩ := exists_pointsMap_eq_of_isSurjective_pullback_snd B S hS f g hp z
    exact ⟨x, hx.trans hz⟩
  tfae_have 1 → 4 := by
    intro hf
    obtain ⟨V, g, hg, hgE⟩ := exists_isSurjective_isEtale_yoneda B S hS hY
    exact ⟨V, g, hg, hgE,
      isSurjective_pullback_snd B S hS hX hY (isAlgebraicSpace_yoneda B S hS V) f g hf⟩
  tfae_have 5 → 1 := by
    rintro ⟨U, φ, -, -, hcomp⟩
    refine Function.Surjective.of_comp (g := pointsMap B S hS (yoneda.obj U) φ) ?_
    rwa [← pointsMap_comp]
  tfae_have 6 → 5 := by
    rintro ⟨U, V, φ, ψ, h, hcomm, hφ, hφEtale, hψ, -, hh⟩
    exact ⟨U, φ, hφ, hφEtale, by rw [hcomm]; exact isSurjective_comp B S hS hh hψ⟩
  tfae_have 1 → 6 := by
    intro hf
    obtain ⟨V, ψ, hψ, hψE⟩ := exists_isSurjective_isEtale_yoneda B S hS hY
    have hV : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
    have hP : IsAlgebraicSpace B S hS (pullback f ψ) :=
      isAlgebraicSpace_pullback B S hS f ψ hX hV hY
    obtain ⟨U, r, hr, hrE⟩ := exists_isSurjective_isEtale_yoneda B S hS hP
    refine ⟨U, V, r ≫ pullback.fst f ψ, ψ, r ≫ pullback.snd f ψ, ?_,
      isSurjective_comp B S hS hr (isSurjective_pullback_fst B S hS hX hY hV f ψ hψ),
      isEtale_comp B S hS hrE (isEtale_pullback_fst B S hS hX hY hV f ψ hψE),
      hψ, hψE,
      isSurjective_comp B S hS hr (isSurjective_pullback_snd B S hS hX hY hV f ψ hf)⟩
    rw [Category.assoc, Category.assoc, pullback.condition]
  tfae_have 7 → 1 := by
    rintro ⟨I, U, hcover, hlocal⟩ y
    obtain ⟨i, z, hz⟩ := Set.mem_iUnion.mp
      (((isZariskiCover_iff_iUnion_points B S hS Y hY I U hcover.1).mp hcover) ▸
        Set.mem_univ y)
    obtain ⟨x, hx⟩ := exists_pointsMap_eq_of_isSurjective_pullback_snd B S hS f (U i).ι
      (hlocal i) z
    exact ⟨x, hx.trans hz⟩
  tfae_have 1 → 7 := by
    intro hf
    set U : Subfunctor Y := openSubspaceOfPoints B S hS Y Set.univ with hU
    have hUopen : IsOpenSubspace B S hS U :=
      isOpenSubspace_openSubspaceOfPoints B S hS hY Set.univ isOpen_univ
    refine ⟨PUnit.{u + 1}, fun _ ↦ U, ⟨fun _ ↦ hUopen, ?_⟩, fun _ ↦
      isSurjective_pullback_snd B S hS hX hY hUopen.1 f U.ι hf⟩
    refine ((isZariskiCover_iff_iUnion_points B S hS Y hY PUnit.{u + 1} (fun _ ↦ U)
      (fun _ ↦ hUopen)).mpr ?_).2
    rw [Set.iUnion_const, hU, range_pointsMap_ι_openSubspaceOfPoints]
  tfae_finish

end Tfae

/-! ### Surjectivity of a representable morphism is surjectivity on points -/

section Representable

/-- A morphism of the big fppf site of `S` which induces a surjection on the points of the
represented presheaves has surjective underlying morphism of schemes.

This is the converse of `AlgebraicGeometry.Space.surjective_pointsMap_yoneda_map`, and the
case of a morphism of schemes of Stacks 03H5. -/
theorem surjective_of_surjective_pointsMap_yoneda_map {U V : BigFppfOver B S hS} (σ : U ⟶ V)
    (h : Function.Surjective (pointsMap B S hS (yoneda.obj U) (yoneda.map σ))) :
    Surjective ((BigFppfOver.toScheme B S hS).map σ) := by
  classical
  refine ⟨fun v ↦ ?_⟩
  obtain ⟨y, hy⟩ := h ((canonicalSiteFieldPoint B S hS V v).class B S hS (yoneda.obj V))
  induction y using Quot.ind with | _ p => ?_
  rw [pointsMap_class] at hy
  refine ⟨schemePoint B S hS U p, ?_⟩
  rw [← schemePoint_map_yoneda B S hS σ p, schemePoint_eq_of_class_eq B S hS V _ _ hy]
  exact canonicalSiteFieldPoint_point B S hS V v

/-- **Stacks 03MD.** A representable morphism of presheaves on the big fppf site of `S` is
surjective — surjective after every representable base change — if and only if the induced map
on points is surjective.

No algebraic-space hypothesis is needed: representability of the morphism, which is part of
surjectivity in the relative sense, is the only one used. -/
@[stacks 03MD]
theorem surjective_iff_pointsMap_surjective_of_representable
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hf : yoneda.relativelyRepresentable f) :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f ↔
      Function.Surjective (pointsMap B S hS F f) := by
  constructor
  · intro hsurj y
    induction y using Quot.ind with | _ q => ?_
    let A : BigFppfOver B S hS := q.siteObject B S hS G
    let g : yoneda.obj A ⟶ G := yonedaEquiv.symm q.value
    have key : FieldValuedPoint.map B S hS (yoneda.obj A) g
        ⟨q.carrier, q.contained, q.toBase, 𝟙 A⟩ = q :=
      congrArg (@FieldValuedPoint.mk B S hS G q.carrier q.field q.contained q.toBase)
        (Equiv.apply_symm_apply yonedaEquiv q.value)
    obtain ⟨x, hx⟩ := surjective_pointsMap_yoneda_map B S hS (hf.snd g)
      (hsurj.property g (hf.fst g) (hf.snd g) (hf.isPullback g))
      (FieldValuedPoint.class B S hS (yoneda.obj A)
        ⟨q.carrier, q.contained, q.toBase, 𝟙 A⟩)
    refine ⟨pointsMap B S hS (yoneda.obj (hf.pullback g)) (hf.fst g) x, ?_⟩
    rw [← pointsMap_comp_apply, (hf.isPullback g).w, pointsMap_comp_apply, hx, pointsMap_class,
      key]
  · intro hpoints
    refine ⟨hf, fun a b g fst snd hsquare ↦
      surjective_of_surjective_pointsMap_yoneda_map B S hS snd fun x ↦ ?_⟩
    obtain ⟨z, hz⟩ := hpoints (pointsMap B S hS (yoneda.obj a) g x)
    obtain ⟨w, -, hw⟩ := exists_point_of_isPullback_presheaf B S hS hsquare z x hz
    exact ⟨w, hw⟩

end Representable

end AlgebraicGeometry.Space

end
