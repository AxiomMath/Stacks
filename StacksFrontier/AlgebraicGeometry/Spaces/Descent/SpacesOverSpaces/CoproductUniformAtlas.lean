module

public import StacksFrontier.AlgebraicGeometry.Size.AtlasOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.CoproductAlgebraicityAtlas
public import Mathlib.Algebra.MvPolynomial.Cardinal

/-!
# There is no uniform size bound on the atlases of the algebraic spaces of a big fppf site

The coproduct of a family of algebraic spaces over `S` is built in
`StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.CoproductAlgebraicityAtlas` from a
choice of atlases `U i` of the members, and it is an algebraic space as soon as `∐ U i` is an
object of the site. The hypothesis actually used,
`AlgebraicGeometry.BigFppfSite.AdmitsCoproductIndex`, bounds the index type by the *cofinality*
of the size cutoff, because the size of `∐ U i` is governed by the supremum of the sizes of the
`U i` and nothing bounds those uniformly.

This file shows that nothing can: there is **no** cardinal `κ` below the cutoff, depending only
on the site, such that every algebraic space over `S` admits an atlas of size at most `κ`
(`AlgebraicGeometry.Space.not_exists_uniform_atlas_size_bound`). So the route to removing the
cofinality hypothesis by choosing uniformly small atlases, which would need only
`#I < B.cutoff` through `AlgebraicGeometry.schemeSize_coproduct_le`, is closed.

The obstruction is already visible on *representable* spaces. An atlas of `yoneda.obj T` is a
surjective étale cover of the scheme `T`, so it bounds `T` from below:
`AlgebraicGeometry.Space.size_le_two_pow_two_pow_size_of_atlas_yoneda`, an instance of
`AlgebraicGeometry.Space.size_le_two_pow_two_pow_size_of_atlas` at the identity open immersion.
The site, on the other hand, contains objects over `S` of every size below the cutoff, by
`AlgebraicGeometry.BigFppfOver.exists_size_ge`, so no fixed `κ` can bound them all.

The same obstruction applies to the coproduct itself, and this is the sharp statement:
an algebraic sheaf coproduct of a family of representables bounds the sizes of *all* its
members at once by a cardinal computed from its own atlas
(`AlgebraicGeometry.Space.Descent.exists_bound_size_of_algebraicSheafCoproduct`), because every
summand inclusion into a coproduct of sheaves is an open immersion. A family whose members have
sizes cofinal in the cutoff therefore has no algebraic sheaf coproduct at all
(`AlgebraicGeometry.Space.Descent.not_nonempty_algebraicSheafCoproduct_of_cofinal_size`),
whatever the cardinality of its index type.

## Main results

* `AlgebraicGeometry.BigFppfOver.exists_size_ge`: the site over a nonempty `S` contains objects
  of at least any prescribed size below the cutoff.
* `AlgebraicGeometry.Space.size_le_two_pow_two_pow_size_of_atlas_yoneda`: an atlas of a
  representable space bounds the represented scheme.
* `AlgebraicGeometry.Space.not_exists_uniform_atlas_size_bound`: there is no uniform bound on
  the size of an atlas.
* `AlgebraicGeometry.Space.Descent.exists_bound_size_of_algebraicSheafCoproduct`: an algebraic
  sheaf coproduct bounds the sizes of its members uniformly.
* `AlgebraicGeometry.Space.Descent.not_isAlgebraicSpace_of_isColimit_cofan_of_cofinal_size` and
  `AlgebraicGeometry.Space.Descent.not_nonempty_algebraicSheafCoproduct_of_cofinal_size`: hence
  a family of cofinal sizes has no coproduct that is an algebraic space over `S`, and no
  algebraic sheaf coproduct.

## References

* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
* [Stacks Project, Tag 0ADK](https://stacks.math.columbia.edu/tag/0ADK)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u v

namespace AlgebraicGeometry

/-- **The big fppf site over a nonempty scheme contains objects of every size below the
cutoff.** For a cardinal `ν` with `S.size ≤ ν < B.cutoff` there is an object of
`AlgebraicGeometry.BigFppfOver B S hS` whose underlying scheme has size at least `ν`, namely the
spectrum of a polynomial ring on `ν` indeterminates over the sections of an affine open of `S`,
mapping to `S` through that affine open.

The size of that spectrum is exactly `ν`: at least `ν` because the indeterminates are distinct
elements of the ring, by `MvPolynomial.X_injective` and
`AlgebraicGeometry.Scheme.size_Spec`, and at most `ν` because
`MvPolynomial.cardinalMk_le_max` bounds the ring by the maximum of `ℵ₀`, the coefficients and
the indeterminates, all of which are at most `ν`. The upper bound is what keeps the object
inside the site. -/
public theorem BigFppfOver.exists_size_ge (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hne : Nonempty S) (ν : Cardinal.{u}) (hSν : S.size ≤ ν)
    (hν : ν < B.cutoff) :
    ∃ T : BigFppfOver B S hS, ν ≤ ((BigFppfOver.toScheme B S hS).obj T).size := by
  classical
  obtain ⟨point⟩ := hne
  obtain ⟨_, ⟨affine, haffine, rfl⟩, hpoint, _⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ point) isOpen_univ
  let A : S.affineOpens := ⟨affine, haffine⟩
  let _ : IsAffine (Scheme.Opens.toScheme affine) := haffine
  let _ : Nonempty affine := ⟨⟨point, hpoint⟩⟩
  let R := Γ(S, affine)
  let P := MvPolynomial ν.out R
  have hsize : (Spec (CommRingCat.of P)).size ≤ ν := by
    rw [Scheme.size_Spec]
    refine max_le (S.aleph0_le_size.trans hSν) ?_
    refine MvPolynomial.cardinalMk_le_max.trans (sup_le (sup_le ?_ ?_) ?_)
    · exact (S.mk_sections_le_size A).trans hSν
    · exact (Cardinal.mk_out ν).le
    · exact S.aleph0_le_size.trans hSν
  have hP : B.Contains (Spec (CommRingCat.of P)) := hsize.trans_lt hν
  let base : Spec (CommRingCat.of P) ⟶ S :=
    Spec.map (CommRingCat.ofHom MvPolynomial.C) ≫
      Spec.map (Scheme.Opens.topIso affine).hom ≫
        (Scheme.Opens.toScheme affine).isoSpec.inv ≫ Scheme.Opens.ι affine
  refine ⟨Over.mk (ObjectProperty.homMk base : B.obj hP ⟶ B.obj hS), ?_⟩
  change ν ≤ (Spec (CommRingCat.of P)).size
  rw [Scheme.size_Spec]
  exact ((Cardinal.mk_out ν).symm.le.trans
    (Cardinal.mk_le_of_injective (MvPolynomial.X_injective (R := R) (σ := ν.out)))).trans
      (le_max_right _ _)

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An atlas of a representable space bounds the represented scheme.** If
`a : yoneda.obj U ⟶ yoneda.obj T` is surjective and étale after every representable base change
then `size T ≤ 2 ^ 2 ^ size U`.

This is `AlgebraicGeometry.Space.size_le_two_pow_two_pow_size_of_atlas` applied to the identity
of `yoneda.obj T`, which is an open immersion because it is an isomorphism. Concretely, `U`
covers `T` by a surjective flat morphism, so it cannot be smaller than `T` by more than the
double exponential that `AlgebraicGeometry.Scheme.size_le_of_flat_of_surjective` loses. -/
public theorem size_le_two_pow_two_pow_size_of_atlas_yoneda
    {T U : BigFppfOver B S hS} {a : yoneda.obj U ⟶ yoneda.obj T}
    (hsurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hetale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    ((BigFppfOver.toScheme B S hS).obj T).size ≤
      (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^
        ((BigFppfOver.toScheme B S hS).obj U).size :=
  size_le_two_pow_two_pow_size_of_atlas B S hS hsurj hetale
    (g := 𝟙 (yoneda.obj T)) (isOpenImmersion_of_isIso B S hS _)

/-- **A cardinal below the cutoff has its double exponential below the cutoff.** The cutoff is a
strong prelimit, so it is closed under the power operation, twice. -/
public theorem two_pow_two_pow_lt_cutoff {κ : Cardinal.{u}} (hκ : κ < B.cutoff) :
    (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ κ < B.cutoff :=
  B.cutoff_isStrongPrelimit (B.cutoff_isStrongPrelimit hκ)

/-- The double exponential `2 ^ 2 ^ κ` is monotone in `κ`. -/
private theorem two_pow_two_pow_le_two_pow_two_pow {a b : Cardinal.{u}} (h : a ≤ b) :
    (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ a ≤ (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ b :=
  Cardinal.power_le_power_left two_ne_zero (Cardinal.power_le_power_left two_ne_zero h)

/-- **There is no uniform bound on the size of an atlas of an algebraic space over `S`.**

Suppose `κ < B.cutoff` were such that every algebraic space over `S` had an atlas of size at
most `κ`. The spaces represented by objects of the site are algebraic, by
`AlgebraicGeometry.isAlgebraicSpace_yoneda`, and an atlas of `yoneda.obj T` bounds `size T` by
`2 ^ 2 ^ κ`, by `AlgebraicGeometry.Space.size_le_two_pow_two_pow_size_of_atlas_yoneda`. That
bound is itself below the cutoff, the cutoff being a strong prelimit, so
`AlgebraicGeometry.BigFppfOver.exists_size_ge` produces an object of the site strictly larger
than it — a contradiction.

This is the precise sense in which the atlases of a family of algebraic spaces cannot be chosen
with a size bound independent of the member: the sizes of the members themselves are unbounded
below the cutoff, and an atlas is never much smaller than what it covers. -/
public theorem not_exists_uniform_atlas_size_bound (hne : Nonempty S) :
    ¬ ∃ κ : Cardinal.{u}, κ < B.cutoff ∧
      ∀ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS X →
        ∃ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X),
          (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS)).presheaf a ∧
          (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS)).presheaf a ∧
          ((BigFppfOver.toScheme B S hS).obj U).size ≤ κ := by
  rintro ⟨κ, hκ, hbound⟩
  -- the successor of a cardinal below the cutoff, above both `2 ^ 2 ^ κ` and the size of `S`
  have hmax : max κ S.size < B.cutoff := max_lt hκ hS
  have hbig : (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ max κ S.size < B.cutoff :=
    two_pow_two_pow_lt_cutoff B hmax
  have hκbig := two_pow_two_pow_le_two_pow_two_pow (le_max_left κ S.size)
  have hSbig : S.size ≤ (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ max κ S.size :=
    ((le_max_right κ S.size).trans (Cardinal.cantor _).le).trans
      (Cardinal.power_le_power_left two_ne_zero (Cardinal.cantor _).le)
  have hν : Order.succ ((2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ max κ S.size) < B.cutoff :=
    B.cutoff_isStrongPrelimit.isSuccPrelimit.succ_lt hbig
  obtain ⟨T, hT⟩ := BigFppfOver.exists_size_ge B S hS hne _
    (hSbig.trans (Order.le_succ _)) hν
  obtain ⟨U, a, hsurj, hetale, hU⟩ :=
    hbound (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)
  have hTU : ((BigFppfOver.toScheme B S hS).obj T).size ≤
      (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ κ :=
    (size_le_two_pow_two_pow_size_of_atlas_yoneda B S hS hsurj hetale).trans
      (two_pow_two_pow_le_two_pow_two_pow hU)
  exact absurd (hT.trans (hTU.trans hκbig)) (not_le.2 (Order.lt_succ _))

end Space

namespace Space.Descent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **An algebraic sheaf coproduct bounds the sizes of all its members at once.** If a family of
representable spaces `yoneda.obj (T i)` has an algebraic sheaf coproduct `Y`, then the sizes of
the schemes `T i` are all at most `2 ^ 2 ^ size U`, where `U` is an atlas of `Y`; in particular
they are bounded by a single cardinal below the cutoff.

Each summand inclusion `Y.ι i` into a coproduct of sheaves is an open immersion, by
`AlgebraicGeometry.Space.isOpenImmersion_coproductInj`, which holds for an index type of any
size whatever; so `AlgebraicGeometry.Space.size_le_two_pow_two_pow_size_of_atlas` applies to it
with the atlas of `Y`. -/
public theorem exists_bound_size_of_algebraicSheafCoproduct {I : Type v}
    (T : I → BigFppfOver B S hS)
    (Y : AlgebraicSheafCoproduct (fun i => yoneda.obj (T i))
      (fun i => isAlgebraicSpace_yoneda B S hS (T i))) :
    ∃ κ : Cardinal.{u}, κ < B.cutoff ∧
      ∀ i, ((BigFppfOver.toScheme B S hS).obj (T i)).size ≤ κ := by
  obtain ⟨U, g, hsurj, hetale⟩ := Y.exists_atlas
  refine ⟨(2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^
    ((BigFppfOver.toScheme B S hS).obj U).size,
    Space.two_pow_two_pow_lt_cutoff B U.left.property, fun i => ?_⟩
  exact Space.size_le_two_pow_two_pow_size_of_atlas B S hS hsurj hetale
    (g := (Y.ι i).hom)
    (Space.isOpenImmersion_coproductInj B S hS I _ Y.sheaf Y.ι Y.isColimit i)

/-- **A coproduct in sheaves of a family of representable algebraic spaces whose sizes are
cofinal in the cutoff is not an algebraic space over `S`.** However the coproduct is formed, an
atlas of it would be an object of the site covering every member, hence bounding the size of
every member by `2 ^ 2 ^` its own size — a single cardinal below the cutoff, the cutoff being a
strong prelimit — while the hypothesis provides a member above any such cardinal.

This is the statement that the cofinality bound
`AlgebraicGeometry.BigFppfSite.AdmitsCoproductIndex` is there to avoid, and it uses no bound on
the index type at all: `AlgebraicGeometry.Space.isOpenImmersion_coproductInj` holds for a family
of any size. -/
public theorem not_isAlgebraicSpace_of_isColimit_cofan_of_cofinal_size {I : Type v}
    (T : I → BigFppfOver B S hS)
    (hcof : ∀ κ : Cardinal.{u}, κ < B.cutoff →
      ∃ i, κ < ((BigFppfOver.toScheme B S hS).obj (T i)).size)
    {G : Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (ι : ∀ i, spaceSheaf (yoneda.obj (T i)) (isAlgebraicSpace_yoneda B S hS (T i)) ⟶ G)
    (hG : IsColimit (Cofan.mk G ι)) : ¬ IsAlgebraicSpace B S hS G.obj := by
  intro hA
  obtain ⟨κ, hκ, hbound⟩ :=
    exists_bound_size_of_algebraicSheafCoproduct T ⟨G, ι, hG, hA.exists_atlas⟩
  obtain ⟨i, hi⟩ := hcof κ hκ
  exact absurd (hbound i) (not_le.2 hi)

/-- **A family of representable algebraic spaces whose sizes are cofinal in the cutoff has no
algebraic sheaf coproduct.** No restriction on the index type is involved: whatever its
cardinality, an atlas of the coproduct would bound every member by one cardinal below the
cutoff, by `AlgebraicGeometry.Space.Descent.exists_bound_size_of_algebraicSheafCoproduct`,
while the hypothesis provides a member above any such cardinal.

This is the obstruction that the cofinality bound
`AlgebraicGeometry.BigFppfSite.AdmitsCoproductIndex` avoids: an index type of cardinality below
the cutoff but at least its cofinality can carry a family of objects of the site whose sizes are
cofinal in the cutoff, and then the coproduct of the family in sheaves is not an algebraic space
over `S`. -/
public theorem not_nonempty_algebraicSheafCoproduct_of_cofinal_size {I : Type v}
    (T : I → BigFppfOver B S hS)
    (hcof : ∀ κ : Cardinal.{u}, κ < B.cutoff →
      ∃ i, κ < ((BigFppfOver.toScheme B S hS).obj (T i)).size) :
    ¬ Nonempty (AlgebraicSheafCoproduct (fun i => yoneda.obj (T i))
      (fun i => isAlgebraicSpace_yoneda B S hS (T i))) := by
  rintro ⟨Y⟩
  obtain ⟨κ, hκ, hbound⟩ := exists_bound_size_of_algebraicSheafCoproduct T Y
  obtain ⟨i, hi⟩ := hcof κ hκ
  exact absurd (hbound i) (not_le.2 hi)

end Space.Descent

end AlgebraicGeometry

end
