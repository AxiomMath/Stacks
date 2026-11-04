module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.PowerMatrixTwoTransitive
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.GeneralLinearTwoPowerContraction
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.SliceRationalPoints

/-!
# The rational points of `(ℙ¹_k)^m` read in the slice category over `Spec k`

The contraction step of [Stacks, Tag 0AEM] runs in two vocabularies which have to be matched.
The group-theoretic exercise of that step, that the `m`-th power of the general linear group
carries a pair of distinct rational points of `(ℙ¹_K)^m` to every pair with the same coincidence
pattern, is `AlgebraicGeometry.exists_comp_powerMatrixAut_hom_eq_and_eq`, stated with rational
points read as morphisms `Over.mk (𝟙 (Spec K)) ⟶ (ℙ¹_K)^m` of the slice category over `Spec K` —
that is where `(ℙ¹_K)^m` is a product, so a rational point of it is a family of rational points
of the factors.  The induction and the density statements, on the other hand, are phrased with
`AlgebraicGeometry.Space.projectiveLinePower`, the `m`-fold power of the restricted functor of
points of `ℙ¹_k` on the big fppf site, whose rational points are the morphisms out of the
terminal presheaf `AlgebraicGeometry.Space.baseFunctor`.

This file is the transport between the two, and the two compatibilities that make it usable.
The route is the Yoneda lemma on the restricted functor of points
(`AlgebraicGeometry.bigFppfRestrictedRationalPointEquiv`) composed with the identification
`AlgebraicGeometry.Space.projectiveSpacePowerRestrictedYonedaIso` of the restricted functor of
points of `AlgebraicGeometry.projectiveSpacePowerOver` with
`AlgebraicGeometry.Space.projectiveLinePower`, which is an instance of
`CategoryTheory.Limits.PreservesProduct.iso` and therefore commutes with the coordinate
projections by `CategoryTheory.Limits.piComparison_comp_π`.  Compatibility with the matrix
automorphisms needs one further step, because
`AlgebraicGeometry.Space.projectiveLinePowerFunctorMatrixAut` is built from
`AlgebraicGeometry.Space.projectiveSpacePowerYonedaIso`, which routes through the functor of
points of the site object; the two routes are compared by the naturality of
`AlgebraicGeometry.bigFppfOverRestrictedYonedaIso`.

## Main definitions

* `AlgebraicGeometry.Space.projectiveLineSlicePointEquiv`: **the rational points of the
  restricted functor of points of `ℙ¹_k` are the rational points of `ℙ¹_k` over `Spec k`.**
* `AlgebraicGeometry.Space.projectiveLinePowerSlicePointEquiv`: **the rational points of
  `AlgebraicGeometry.Space.projectiveLinePower` are the rational points of
  `AlgebraicGeometry.projectiveSpacePowerOver` in the slice category over `Spec k`.**

## Main results

* `AlgebraicGeometry.Space.projectiveLinePowerSlicePointEquiv_comp_pi`: the transport commutes
  with the coordinate projections of the power.
* `AlgebraicGeometry.Space.projectiveLinePowerSlicePointEquiv_comp_matrixAut`: the transport
  carries the automorphism `AlgebraicGeometry.Space.projectiveLinePowerFunctorMatrixAut` attached
  to an `m`-tuple of invertible two-by-two matrices to the automorphism
  `AlgebraicGeometry.projectiveSpacePowerMatrixAut` attached to the same tuple.
* `AlgebraicGeometry.Space.comp_coordinateProjection_eq_iff`: two morphisms into
  `AlgebraicGeometry.Space.projectiveLinePower` agree after
  `AlgebraicGeometry.Space.coordinateProjection` exactly when they agree in each coordinate of
  the subset projected onto.
* `AlgebraicGeometry.Space.exists_comp_projectiveLinePowerFunctorMatrixAut_hom_eq_and_eq`:
  **the exercise of [Stacks, Tag 0AEM] in the functor-of-points vocabulary** — given two distinct
  rational points `x ≠ y` of `AlgebraicGeometry.Space.projectiveLinePower` over an algebraically
  closed field, and a pair `p, q` of rational points whose coordinates coincide exactly where
  those of `x` and `y` do, one `m`-tuple of invertible two-by-two matrices carries `x` to `p` and
  `y` to `q`.

## Implementation notes

The rearrangements of composites are stated over an abstract category with every morphism a
variable, because `CategoryTheory.Category.assoc` does not rewrite reliably in the presheaf
category on the big fppf site: the two spellings `BigFppfOver B S hS` and `Over (B.obj hS)` of
the site make `rw` refuse one side of a goal containing both.  For the same reason every
identity extracted from a definition — the components of
`AlgebraicGeometry.Space.projectiveSpacePowerYonedaIso` and of
`AlgebraicGeometry.Space.projectiveLinePowerFunctorMatrixAut` — is isolated as its own `rfl`
lemma rather than reached by rewriting with the definition.

## References

* [Stacks Project, Tag 0AEM](https://stacks.math.columbia.edu/tag/0AEM)
* [Stacks Project, Tag 0B2U](https://stacks.math.columbia.edu/tag/0B2U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### Rearrangements of composites, stated over an abstract category -/

/-- Cancelling a two-sided inverse in the middle of a composite. -/
private theorem comp_inv_comp_hom_comp {C : Type*} [Category* C] {W P A T : C}
    (ξ : W ⟶ P) {ei : P ⟶ A} {eh : A ⟶ P} (π : P ⟶ T) (h : ei ≫ eh = 𝟙 P) :
    (ξ ≫ ei) ≫ eh ≫ π = ξ ≫ π := by
  rw [Category.assoc, ← Category.assoc ei eh π, h, Category.id_comp]

/-- Moving an endomorphism of the source across a morphism it intertwines. -/
private theorem comp_comp_eq_comp_comp {C : Type*} [Category* C] {W P A : C}
    (ξ : W ⟶ P) {a : P ⟶ P} {ei : P ⟶ A} {n : A ⟶ A} (h : a ≫ ei = ei ≫ n) :
    (ξ ≫ a) ≫ ei = (ξ ≫ ei) ≫ n := by
  rw [Category.assoc, h, ← Category.assoc]

/-- Contracting the last two morphisms of a three-fold composite. -/
private theorem comp_comp_eq_of_comp_eq {C : Type*} [Category* C] {W P Q T : C}
    (ξ : W ⟶ P) {cp : P ⟶ Q} {pj : Q ⟶ T} {pi : P ⟶ T} (h : cp ≫ pj = pi) :
    (ξ ≫ cp) ≫ pj = ξ ≫ pi := by
  rw [Category.assoc, h]

/-- The conjugation of an endomorphism `c` through a pair of isomorphisms, read as an
intertwining relation for the endomorphism `n` that `c` corresponds to.  This is the shape of the
compatibility of the transport of rational points with the matrix automorphisms: `a` and `f` are
the two directions of the comparison with the restricted functor of points, `b` and `d` the two
directions of the comparison with the functor of points of the site object. -/
private theorem conjugate_rearrange {C : Type*} [Category* C] {P A Y : C}
    (a : P ⟶ A) (b : A ⟶ Y) (c : Y ⟶ Y) (d : Y ⟶ A) (f : A ⟶ P) (n : A ⟶ A)
    (hnat : c ≫ d = d ≫ n) (hbd : b ≫ d = 𝟙 A) (hfa : f ≫ a = 𝟙 A) :
    ((a ≫ b) ≫ c ≫ d ≫ f) ≫ a = a ≫ n := by
  have h1 : ((a ≫ b) ≫ c ≫ d ≫ f) ≫ a = a ≫ b ≫ (c ≫ d) ≫ f ≫ a := by
    simp only [Category.assoc]
  rw [h1, hnat, hfa, Category.comp_id, ← Category.assoc b d n, hbd, Category.id_comp]

variable (k : Type u) [Field k] (B : BigFppfSite.{u})
  (hk : B.Contains (Spec (CommRingCat.of k))) (m : ℕ)

/-! ### The transport -/

/-- **The rational points of the restricted functor of points of `ℙ¹_k` are the rational points
of `ℙ¹_k` as a scheme over `Spec k`**, by the Yoneda lemma on the big fppf site over `Spec k`. -/
def projectiveLineSlicePointEquiv :
    (baseFunctor k B hk ⟶ projectiveLineFunctor k B hk) ≃
      (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
        (projectiveSpaceOverRing 1 (CommRingCat.of k)).asOver (Spec (CommRingCat.of k))) :=
  bigFppfRestrictedRationalPointEquiv B (Spec (CommRingCat.of k)) hk _

/-- **The rational points of `AlgebraicGeometry.Space.projectiveLinePower` are the rational
points of the `m`-fold self-product of `ℙ¹_k` over `Spec k`, read in the slice category.** The
power of the functor of points is the restricted functor of points of that self-product by
`AlgebraicGeometry.Space.projectiveSpacePowerRestrictedYonedaIso`, and the rational points of a
restricted functor of points are the morphisms out of `Over.mk (𝟙 (Spec k))` by
`AlgebraicGeometry.bigFppfRestrictedRationalPointEquiv`.

This is the bijection that lets the exercise of [Stacks, Tag 0AEM], proved in the slice category,
be applied to the rational points the induction and the density statements provide. -/
def projectiveLinePowerSlicePointEquiv :
    (baseFunctor k B hk ⟶ projectiveLinePower k B hk (Fin m)) ≃
      (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ projectiveSpacePowerOver k 1 m) :=
  ((projectiveSpacePowerRestrictedYonedaIso k B hk m).symm.homToEquiv
      (Z := baseFunctor k B hk)).trans
    (bigFppfRestrictedRationalPointEquiv B (Spec (CommRingCat.of k)) hk
      (projectiveSpacePowerOver k 1 m))

/-- The transport of a rational point of `AlgebraicGeometry.Space.projectiveLinePower`, unfolded:
read the point in the restricted functor of points of the self-product, then apply the Yoneda
bijection. -/
theorem projectiveLinePowerSlicePointEquiv_apply
    (ξ : baseFunctor k B hk ⟶ projectiveLinePower k B hk (Fin m)) :
    projectiveLinePowerSlicePointEquiv k B hk m ξ =
      bigFppfRestrictedRationalPointEquiv B (Spec (CommRingCat.of k)) hk
        (projectiveSpacePowerOver k 1 m)
        (ξ ≫ (projectiveSpacePowerRestrictedYonedaIso k B hk m).inv) :=
  rfl

/-! ### The identities extracted from the comparison isomorphisms -/

/-- The comparison of the restricted functor of points of the self-product with the power of the
functor of points commutes with the coordinate projections: it is the product comparison morphism
of a functor preserving the product. -/
private theorem restrictedYonedaIso_hom_comp_pi (i : Fin m) :
    (projectiveSpacePowerRestrictedYonedaIso k B hk m).hom ≫
        Pi.π (fun _ : Fin m => projectiveLineFunctor k B hk) i =
      (bigFppfRestrictedYoneda B (Spec (CommRingCat.of k)) hk).map
        (Pi.π (fun _ : Fin m =>
          (projectiveSpaceOverRing 1 (CommRingCat.of k)).asOver (Spec (CommRingCat.of k))) i) :=
  piComparison_comp_π _ _ i

/-- The forward morphism of `AlgebraicGeometry.Space.projectiveSpacePowerYonedaIso` factors
through the restricted functor of points of the self-product. -/
private theorem yonedaIso_hom_eq :
    (projectiveSpacePowerYonedaIso k B hk m).hom =
      (bigFppfOverRestrictedYonedaIso B (Spec (CommRingCat.of k)) hk
          (projectiveSpacePowerSiteObject k B hk m)).inv ≫
        (projectiveSpacePowerRestrictedYonedaIso k B hk m).hom :=
  rfl

/-- The inverse morphism of `AlgebraicGeometry.Space.projectiveSpacePowerYonedaIso` factors
through the restricted functor of points of the self-product. -/
private theorem yonedaIso_inv_eq :
    (projectiveSpacePowerYonedaIso k B hk m).inv =
      (projectiveSpacePowerRestrictedYonedaIso k B hk m).inv ≫
        (bigFppfOverRestrictedYonedaIso B (Spec (CommRingCat.of k)) hk
          (projectiveSpacePowerSiteObject k B hk m)).hom :=
  rfl

/-- The automorphism of `AlgebraicGeometry.Space.projectiveLinePower` attached to a tuple of
matrices is the automorphism of the functor of points of the site object conjugated by
`AlgebraicGeometry.Space.projectiveSpacePowerYonedaIso`. -/
private theorem matrixAut_hom_eq (M : Fin m → Matrix.GeneralLinearGroup (Fin 2) k) :
    (projectiveLinePowerFunctorMatrixAut k B hk m M).hom =
      (projectiveSpacePowerYonedaIso k B hk m).inv ≫
        yoneda.map (projectiveSpacePowerSiteMatrixAut k B hk m M).hom ≫
          (projectiveSpacePowerYonedaIso k B hk m).hom :=
  rfl

/-- The comparison functor to schemes over `Spec k` carries the automorphism of the site object
of `(ℙ¹_k)^m` attached to a tuple of matrices to the automorphism of the self-product attached to
the same tuple, the site automorphism being its preimage. -/
private theorem post_map_siteMatrixAut (M : Fin m → Matrix.GeneralLinearGroup (Fin 2) k) :
    (Over.post (X := B.obj hk) B.inclusion).map
        (projectiveSpacePowerSiteMatrixAut k B hk m M).hom =
      (projectiveSpacePowerMatrixAut k 1 m M).hom := by
  rw [projectiveSpacePowerSiteMatrixAut_hom, Functor.FullyFaithful.map_preimage]
  rfl

/-! ### The two compatibilities -/

/-- **The transport of rational points commutes with the coordinate projections.** The `i`-th
coordinate of the slice rational point attached to a rational point `ξ` of
`AlgebraicGeometry.Space.projectiveLinePower` is the slice rational point of `ℙ¹_k` attached to
the `i`-th coordinate of `ξ`.

This is the clause that lets a coincidence pattern of rational points of
`AlgebraicGeometry.Space.projectiveLinePower` be read as a coincidence pattern of rational points
of the self-product, which is how `AlgebraicGeometry.exists_comp_powerMatrixAut_hom_eq_and_eq`
states its hypothesis. -/
theorem projectiveLinePowerSlicePointEquiv_comp_pi
    (ξ : baseFunctor k B hk ⟶ projectiveLinePower k B hk (Fin m)) (i : Fin m) :
    projectiveLinePowerSlicePointEquiv k B hk m ξ ≫
        Pi.π (fun _ : Fin m =>
          (projectiveSpaceOverRing 1 (CommRingCat.of k)).asOver (Spec (CommRingCat.of k))) i =
      projectiveLineSlicePointEquiv k B hk
        (ξ ≫ Pi.π (fun _ : Fin m => projectiveLineFunctor k B hk) i) := by
  have harg : (ξ ≫ (projectiveSpacePowerRestrictedYonedaIso k B hk m).inv) ≫
      (bigFppfRestrictedYoneda B (Spec (CommRingCat.of k)) hk).map
        (Pi.π (fun _ : Fin m =>
          (projectiveSpaceOverRing 1 (CommRingCat.of k)).asOver (Spec (CommRingCat.of k))) i) =
    ξ ≫ Pi.π (fun _ : Fin m => projectiveLineFunctor k B hk) i := by
    rw [← restrictedYonedaIso_hom_comp_pi k B hk m i]
    exact comp_inv_comp_hom_comp ξ _
      (projectiveSpacePowerRestrictedYonedaIso k B hk m).inv_hom_id
  rw [projectiveLinePowerSlicePointEquiv_apply, ← bigFppfRestrictedRationalPointEquiv_comp,
    harg]
  rfl

/-- **The transport of rational points carries the automorphism of
`AlgebraicGeometry.Space.projectiveLinePower` attached to an `m`-tuple `M` of invertible
two-by-two matrices to the automorphism of the self-product attached to `M`.**

Both automorphisms come from the automorphism of the site object of `(ℙ¹_k)^m` that `M` gives:
the one on the functor of points by conjugating with
`AlgebraicGeometry.Space.projectiveSpacePowerYonedaIso`, the one on the self-product by applying
the comparison functor to schemes over `Spec k`.  The two are matched by the naturality of
`AlgebraicGeometry.bigFppfOverRestrictedYonedaIso` in the site object. -/
theorem projectiveLinePowerSlicePointEquiv_comp_matrixAut
    (ξ : baseFunctor k B hk ⟶ projectiveLinePower k B hk (Fin m))
    (M : Fin m → Matrix.GeneralLinearGroup (Fin 2) k) :
    projectiveLinePowerSlicePointEquiv k B hk m
        (ξ ≫ (projectiveLinePowerFunctorMatrixAut k B hk m M).hom) =
      projectiveLinePowerSlicePointEquiv k B hk m ξ ≫
        (projectiveSpacePowerMatrixAut k 1 m M).hom := by
  have hkey : (projectiveLinePowerFunctorMatrixAut k B hk m M).hom ≫
        (projectiveSpacePowerRestrictedYonedaIso k B hk m).inv =
      (projectiveSpacePowerRestrictedYonedaIso k B hk m).inv ≫
        (bigFppfRestrictedYoneda B (Spec (CommRingCat.of k)) hk).map
          (projectiveSpacePowerMatrixAut k 1 m M).hom := by
    rw [matrixAut_hom_eq, yonedaIso_inv_eq, yonedaIso_hom_eq]
    refine conjugate_rearrange _ _ _ _ _ _ ?_ ?_ ?_
    · rw [← post_map_siteMatrixAut k B hk m M]
      exact yoneda_map_comp_bigFppfOverRestrictedYonedaIso_inv B (Spec (CommRingCat.of k)) hk _
    · exact (bigFppfOverRestrictedYonedaIso B (Spec (CommRingCat.of k)) hk
        (projectiveSpacePowerSiteObject k B hk m)).hom_inv_id
    · exact (projectiveSpacePowerRestrictedYonedaIso k B hk m).hom_inv_id
  rw [projectiveLinePowerSlicePointEquiv_apply, projectiveLinePowerSlicePointEquiv_apply,
    comp_comp_eq_comp_comp ξ hkey]
  exact bigFppfRestrictedRationalPointEquiv_comp B (Spec (CommRingCat.of k)) hk _ _

/-! ### Agreement after a coordinate projection -/

/-- The coordinate projection onto a finite subset followed by the projection to one of its
coordinates is the projection to that coordinate of the whole power. -/
private theorem coordinateProjection_comp_pi (n : ℕ) (I : Finset (Fin n)) (j : I) :
    coordinateProjection k B hk n I ≫
        Pi.π (fun _ : I => projectiveLineFunctor k B hk) j =
      Pi.π (fun _ : Fin n => projectiveLineFunctor k B hk) (j : Fin n) :=
  (Pi.map'_comp_π _ _ j).trans (Category.comp_id _)

/-- **Two morphisms into `(ℙ¹_k)^n` agree after the coordinate projection onto a finite subset
`I` exactly when they agree in each coordinate belonging to `I`.** This is what turns a
hypothesis stated with `AlgebraicGeometry.Space.coordinateProjection`, the shape the fibre
products of the contraction step of [Stacks, Tag 0AEM] are formed with, into the coordinatewise
coincidence pattern that the orbit statement consumes. -/
theorem comp_coordinateProjection_eq_iff (n : ℕ) (I : Finset (Fin n))
    {W : (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤ Type u}
    (ξ η : W ⟶ projectiveLinePower k B hk (Fin n)) :
    ξ ≫ coordinateProjection k B hk n I = η ≫ coordinateProjection k B hk n I ↔
      ∀ i ∈ I, ξ ≫ Pi.π (fun _ : Fin n => projectiveLineFunctor k B hk) i =
        η ≫ Pi.π (fun _ : Fin n => projectiveLineFunctor k B hk) i := by
  refine ⟨fun h i hi ↦ ?_, fun h ↦ Pi.hom_ext _ _ fun j ↦ ?_⟩
  · exact (comp_comp_eq_of_comp_eq ξ
        (coordinateProjection_comp_pi k B hk n I ⟨i, hi⟩)).symm.trans
      ((congrArg (fun α ↦ α ≫ Pi.π (fun _ : I => projectiveLineFunctor k B hk) ⟨i, hi⟩) h).trans
        (comp_comp_eq_of_comp_eq η (coordinateProjection_comp_pi k B hk n I ⟨i, hi⟩)))
  · exact (comp_comp_eq_of_comp_eq ξ (coordinateProjection_comp_pi k B hk n I j)).trans
      ((h j.1 j.2).trans
        (comp_comp_eq_of_comp_eq η (coordinateProjection_comp_pi k B hk n I j)).symm)

/-! ### The orbit statement in the functor-of-points vocabulary -/

/-- **The `m`-th power of the general linear group carries a pair of distinct rational points of
`AlgebraicGeometry.Space.projectiveLinePower` to every pair with the same coincidence pattern.**

This is `AlgebraicGeometry.exists_comp_powerMatrixAut_hom_eq_and_eq` transported along
`AlgebraicGeometry.Space.projectiveLinePowerSlicePointEquiv`: the hypothesis moves across by the
compatibility with the coordinate projections and the conclusion by the compatibility with the
matrix automorphisms, both directions using that the transport is a bijection.

It is the form the induction of [Stacks, Tag 0AEM] needs, the automorphism being the
`AlgebraicGeometry.Space.projectiveLinePowerFunctorMatrixAut` that the contraction step's
conclusion is stated with. -/
theorem exists_comp_projectiveLinePowerFunctorMatrixAut_hom_eq_and_eq
    (K : Type u) [Field K] [IsAlgClosed K] (B : BigFppfSite.{u})
    (hK : B.Contains (Spec (CommRingCat.of K))) (m : ℕ)
    (x y p q : baseFunctor K B hK ⟶ projectiveLinePower K B hK (Fin m)) (hxy : x ≠ y)
    (hpat : ∀ i : Fin m,
      x ≫ Pi.π (fun _ : Fin m => projectiveLineFunctor K B hK) i =
          y ≫ Pi.π (fun _ : Fin m => projectiveLineFunctor K B hK) i ↔
        p ≫ Pi.π (fun _ : Fin m => projectiveLineFunctor K B hK) i =
          q ≫ Pi.π (fun _ : Fin m => projectiveLineFunctor K B hK) i) :
    ∃ M : Fin m → Matrix.GeneralLinearGroup (Fin 2) K,
      x ≫ (projectiveLinePowerFunctorMatrixAut K B hK m M).hom = p ∧
        y ≫ (projectiveLinePowerFunctorMatrixAut K B hK m M).hom = q := by
  obtain ⟨M, h₁, h₂⟩ := exists_comp_powerMatrixAut_hom_eq_and_eq K 1 m
    (projectiveLinePowerSlicePointEquiv K B hK m x)
    (projectiveLinePowerSlicePointEquiv K B hK m y)
    (projectiveLinePowerSlicePointEquiv K B hK m p)
    (projectiveLinePowerSlicePointEquiv K B hK m q)
    ((projectiveLinePowerSlicePointEquiv K B hK m).injective.ne hxy)
    (fun i ↦ by
      simpa only [projectiveLinePowerSlicePointEquiv_comp_pi, Equiv.apply_eq_iff_eq] using hpat i)
  exact ⟨M,
    (projectiveLinePowerSlicePointEquiv K B hK m).injective
      ((projectiveLinePowerSlicePointEquiv_comp_matrixAut K B hK m x M).trans h₁),
    (projectiveLinePowerSlicePointEquiv K B hK m).injective
      ((projectiveLinePowerSlicePointEquiv_comp_matrixAut K B hK m y M).trans h₂)⟩

end AlgebraicGeometry.Space

end
