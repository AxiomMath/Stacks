module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePushforwardSplitCounit
public import StacksFrontier.AlgebraicGeometry.Spaces.ExcisionCoveringOverSubspace

/-!
# The agreement locus of two morphisms to an étale object, and the covering it generates

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S`, let `iY : Z ⟶ Y`
be a closed subspace whose inverse image `iX : W ⟶ X` is carried isomorphically onto it by
`k : W ⟶ Z` — the hypothesis of **Stacks 0A4P** — and let `V` be an algebraic space étale over
`Y`.  Two morphisms `g₁, g₂ : V ⟶ X` over `Y` need not be equal, and the excision step of
Stacks 0A4P has to know that they *restrict a section supported on `Z` in the same way*.

This file supplies the geometry behind that.  The *agreement locus* of `g₁` and `g₂` is the base
change of the relative diagonal of `f` along the morphism `(g₁, g₂) : V ⟶ X ×_Y X`.  It is
étale over `V`, the two morphisms become equal on it, and — this is where the hypothesis on `k`
enters — together with the base change to `V` of the open complement of `Z` it *covers* `V` in
the spaces-étale topology: everything of `V` lying over `Z` factors through the agreement locus,
by `AlgebraicGeometry.Space.eq_of_comp_eq_of_factorsThrough_subspace`, and the rest is accounted
for by the complement.

The conclusion drawn from that covering is
`AlgebraicGeometry.Space.map_eq_of_hom_etaleObject`: for a sheaf on the spaces-étale site of `Y`
which vanishes on every object missing `Z`, restriction along `g₁` and along `g₂` is the *same*
map.  That is the only compatibility the excision amalgamation of Stacks 0A4P has to check which
is not a vanishing.

## Main definitions

* `AlgebraicGeometry.Space.agreementPair`: the morphism `(g₁, g₂) : V ⟶ X ×_Y X`.
* `AlgebraicGeometry.Space.agreementLocus`, `AlgebraicGeometry.Space.agreementProj` and
  `AlgebraicGeometry.Space.agreementObj`: the agreement locus, its projection to `V`, and
  itself as an object of the spaces-étale site of `Y`.
* `AlgebraicGeometry.Space.complementBaseObj`: the base change to `V` of the open complement of
  `Z`, as an object of the spaces-étale site of `Y`.
* `AlgebraicGeometry.Space.agreementCover`: the two-element family
  `{agreement locus ⟶ V, V ∖ Z ⟶ V}`.

## Main results

* `AlgebraicGeometry.Space.agreementProj_comp_eq`: the two morphisms agree on the agreement
  locus.
* `AlgebraicGeometry.Space.agreementFactor_comp_agreementProj`: anything over `V` on which the
  two morphisms agree factors through the agreement locus.
* `AlgebraicGeometry.Space.isCovering_agreementCover` and
  `AlgebraicGeometry.Space.generate_agreementCover_mem_topology`: the two-element family is a
  covering family of the spaces-étale site, and the sieve it generates is a covering sieve.
* `AlgebraicGeometry.Space.map_eq_of_hom_etaleObject`: **a sheaf vanishing away from `Z`
  restricts along `g₁` and along `g₂` by the same map.**

## Implementation notes

The agreement locus is a base change of the relative diagonal, so it is étale by Stacks 03FU
together with étaleness of the diagonal of an étale morphism,
`AlgebraicGeometry.Space.isEtale_selfFibreDiagonal`; no point-lifting and no separatedness of
`f` is used.  That the two morphisms become equal on it is the diagonal being a section of both
projections of the fibre square.

The second member of the covering is the base change of
`AlgebraicGeometry.Space.complementObj` along the structure morphism of `V`, not the complement
of a closed subspace of `V`: that way only closedness of `Z` in `Y` is needed, and no stability
of closed immersions under base change.  Its image in `Y` lies in the image of the complement of
`Z`, which is what makes the vanishing hypothesis apply to it.

The final statement is proved at an arbitrary coefficient category: it is
`CategoryTheory.Presheaf.IsSheaf.hom_ext_ofArrows` for the two-element covering, whose two cases
are the agreement on the first member and the vanishing on the second.  No zero morphisms are
needed — `CategoryTheory.Limits.IsZero.eq_of_tgt` says any two morphisms into a zero object are
equal.

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03FU](https://stacks.math.columbia.edu/tag/03FU)
* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 0A4P](https://stacks.math.columbia.edu/tag/0A4P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The agreement locus of two morphisms over the base -/

section AgreementLocus

variable {V X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) {a₁ a₂ : V ⟶ X}

/-- The morphism `(a₁, a₂) : V ⟶ X ×_Y X` determined by two morphisms into `X` whose
composites with `f` agree. -/
def agreementPair (h : a₁ ≫ f = a₂ ≫ f) : V ⟶ selfFibreSquare B S hS f :=
  (isPullback_selfFibreSquare B S hS f).lift a₁ a₂ h

/-- The first component of `AlgebraicGeometry.Space.agreementPair` is the first morphism. -/
@[simp] theorem agreementPair_comp_fst (h : a₁ ≫ f = a₂ ≫ f) :
    agreementPair B S hS f h ≫ selfFibreFst B S hS f = a₁ :=
  (isPullback_selfFibreSquare B S hS f).lift_fst a₁ a₂ h

/-- The second component of `AlgebraicGeometry.Space.agreementPair` is the second morphism. -/
@[simp] theorem agreementPair_comp_snd (h : a₁ ≫ f = a₂ ≫ f) :
    agreementPair B S hS f h ≫ selfFibreSnd B S hS f = a₂ :=
  (isPullback_selfFibreSquare B S hS f).lift_snd a₁ a₂ h

/-- **The agreement locus of two morphisms into `X` over `Y`**: the base change of the relative
diagonal of `f` along `(a₁, a₂)`.  It is the largest part of `V` on which the two morphisms
coincide. -/
def agreementLocus (h : a₁ ≫ f = a₂ ≫ f) : AlgebraicSpaces B S hS :=
  AlgebraicSpaces.fiberProduct B S hS (agreementPair B S hS f h)
    (selfFibreDiagonal B S hS f)

/-- The projection of the agreement locus to `V`. -/
def agreementProj (h : a₁ ≫ f = a₂ ≫ f) : agreementLocus B S hS f h ⟶ V :=
  ObjectProperty.homMk (pullback.fst (agreementPair B S hS f h).hom
    (selfFibreDiagonal B S hS f).hom)

/-- The common value of the two morphisms on the agreement locus. -/
def agreementLift (h : a₁ ≫ f = a₂ ≫ f) : agreementLocus B S hS f h ⟶ X :=
  ObjectProperty.homMk (pullback.snd (agreementPair B S hS f h).hom
    (selfFibreDiagonal B S hS f).hom)

/-- The agreement locus is the base change of the relative diagonal along `(a₁, a₂)`. -/
theorem isPullback_agreementLocus (h : a₁ ≫ f = a₂ ≫ f) :
    IsPullback (agreementProj B S hS f h) (agreementLift B S hS f h)
      (agreementPair B S hS f h) (selfFibreDiagonal B S hS f) :=
  AlgebraicSpaces.isPullback_fiberProduct B S hS _ _

/-- The projection of the agreement locus to `V` is étale: it is a base change of the relative
diagonal of `f`, which is étale because `f` is. -/
theorem isEtale_agreementProj (hf : IsEtale B S hS f.hom) (h : a₁ ≫ f = a₂ ≫ f) :
    IsEtale B S hS (agreementProj B S hS f h).hom :=
  isEtale_of_isPullback B S hS (agreementLift B S hS f h) (agreementProj B S hS f h)
    (selfFibreDiagonal B S hS f) (agreementPair B S hS f h)
    (isPullback_agreementLocus B S hS f h).flip (isEtale_selfFibreDiagonal B S hS f hf)

/-- Either projection of the fibre square, restricted to the agreement locus, computes the
common value: the diagonal is a section of it.

The two morphisms `a₁` and `a₂` occur in the type of `h`, so they cannot be rewritten; the
statement is therefore phrased with the relevant composite as a hypothesis. -/
private theorem agreementProj_comp_aux (h : a₁ ≫ f = a₂ ≫ f)
    {p : selfFibreSquare B S hS f ⟶ X}
    (hp : selfFibreDiagonal B S hS f ≫ p = 𝟙 X) {a : V ⟶ X}
    (ha : agreementPair B S hS f h ≫ p = a) :
    agreementProj B S hS f h ≫ a = agreementLift B S hS f h := by
  rw [← ha, ← Category.assoc, (isPullback_agreementLocus B S hS f h).w, Category.assoc, hp,
    Category.comp_id]

/-- On the agreement locus the first morphism is the common value. -/
theorem agreementProj_comp_left (h : a₁ ≫ f = a₂ ≫ f) :
    agreementProj B S hS f h ≫ a₁ = agreementLift B S hS f h :=
  agreementProj_comp_aux B S hS f h (selfFibreDiagonal_comp_fst B S hS f)
    (agreementPair_comp_fst B S hS f h)

/-- On the agreement locus the second morphism is the common value. -/
theorem agreementProj_comp_right (h : a₁ ≫ f = a₂ ≫ f) :
    agreementProj B S hS f h ≫ a₂ = agreementLift B S hS f h :=
  agreementProj_comp_aux B S hS f h (selfFibreDiagonal_comp_snd B S hS f)
    (agreementPair_comp_snd B S hS f h)

/-- **The two morphisms agree on the agreement locus.** -/
theorem agreementProj_comp_eq (h : a₁ ≫ f = a₂ ≫ f) :
    agreementProj B S hS f h ≫ a₁ = agreementProj B S hS f h ≫ a₂ :=
  (agreementProj_comp_left B S hS f h).trans (agreementProj_comp_right B S hS f h).symm

/-- A morphism to `V` on which the two morphisms agree factors through the agreement locus. -/
def agreementFactor (h : a₁ ≫ f = a₂ ≫ f) {A : AlgebraicSpaces B S hS} (c : A ⟶ V)
    (hc : c ≫ a₁ = c ≫ a₂) : A ⟶ agreementLocus B S hS f h :=
  (isPullback_agreementLocus B S hS f h).lift c (c ≫ a₁)
    ((isPullback_selfFibreSquare B S hS f).hom_ext
      (by rw [Category.assoc, agreementPair_comp_fst, Category.assoc,
        selfFibreDiagonal_comp_fst, Category.comp_id])
      (by rw [Category.assoc, agreementPair_comp_snd, Category.assoc,
        selfFibreDiagonal_comp_snd, Category.comp_id, hc]))

/-- The factorization through the agreement locus, followed by its projection to `V`, is the
given morphism. -/
@[simp] theorem agreementFactor_comp_agreementProj (h : a₁ ≫ f = a₂ ≫ f)
    {A : AlgebraicSpaces B S hS} (c : A ⟶ V) (hc : c ≫ a₁ = c ≫ a₂) :
    agreementFactor B S hS f h c hc ≫ agreementProj B S hS f h = c :=
  (isPullback_agreementLocus B S hS f h).lift_fst _ _ _

end AgreementLocus

/-! ### The two-element covering of an object of the spaces-étale site -/

section Covering

attribute [local instance] pointTopology

variable {W X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (iY : Z ⟶ Y) (hiY : IsClosedImmersion B S hS iY.hom)

/-- The structure morphism of an object of the spaces-étale site of `Y` is the composite of a
morphism of the site into `X` with `f`: that is what being a morphism over `Y` says. -/
theorem toSpaces_map_comp_eq {V : SpacesEtale B S hS Y}
    (g : V ⟶ etaleObject B S hS f hf) :
    (SpacesEtale.toSpaces B S hS Y).map g ≫ f = V.1.hom :=
  Over.w ((SpacesEtale.inclusion B S hS Y).map g)

/-- Two morphisms of the spaces-étale site of `Y` into `X` have the same composite with `f`,
namely the structure morphism of their common source. -/
theorem toSpaces_map_comp_eq_comp {V : SpacesEtale B S hS Y}
    (g₁ g₂ : V ⟶ etaleObject B S hS f hf) :
    (SpacesEtale.toSpaces B S hS Y).map g₁ ≫ f =
      (SpacesEtale.toSpaces B S hS Y).map g₂ ≫ f :=
  (toSpaces_map_comp_eq B S hS f hf g₁).trans (toSpaces_map_comp_eq B S hS f hf g₂).symm

variable (V : SpacesEtale B S hS Y) (g₁ g₂ : V ⟶ etaleObject B S hS f hf)

/-- The agreement locus of two morphisms of the spaces-étale site of `Y` into `X`, as an object
of the spaces-étale site of `Y`: it is étale over `V`, which is étale over `Y`. -/
def agreementObj : SpacesEtale B S hS Y :=
  ⟨Over.mk (agreementProj B S hS f (toSpaces_map_comp_eq_comp B S hS f hf g₁ g₂) ≫ V.1.hom),
    isEtale_comp B S hS
      (isEtale_agreementProj B S hS f hf (toSpaces_map_comp_eq_comp B S hS f hf g₁ g₂))
      V.property⟩

/-- The projection of the agreement locus, as a morphism of the spaces-étale site of `Y`. -/
def agreementObjHom : agreementObj B S hS f hf V g₁ g₂ ⟶ V :=
  ObjectProperty.homMk (Over.homMk
    (agreementProj B S hS f (toSpaces_map_comp_eq_comp B S hS f hf g₁ g₂)) rfl)

/-- **The two morphisms of the site agree after restriction to the agreement locus.** -/
theorem agreementObjHom_comp_eq :
    agreementObjHom B S hS f hf V g₁ g₂ ≫ g₁ = agreementObjHom B S hS f hf V g₁ g₂ ≫ g₂ :=
  ObjectProperty.hom_ext _ (Over.OverMorphism.ext
    (agreementProj_comp_eq B S hS f (toSpaces_map_comp_eq_comp B S hS f hf g₁ g₂)))

/-- The base change to `V` of the open complement of `Z`. -/
def complementBase : AlgebraicSpaces B S hS :=
  AlgebraicSpaces.fiberProduct B S hS V.1.hom (complementHom B S hS iY hiY)

/-- The projection of the base change of the complement to `V`. -/
def complementBaseProj : complementBase B S hS iY hiY V ⟶ V.1.left :=
  ObjectProperty.homMk (pullback.fst V.1.hom.hom (complementHom B S hS iY hiY).hom)

/-- The projection of the base change of the complement to the complement. -/
def complementBaseLift :
    complementBase B S hS iY hiY V ⟶ complementSpace B S hS iY hiY :=
  ObjectProperty.homMk (pullback.snd V.1.hom.hom (complementHom B S hS iY hiY).hom)

/-- The base change of the complement is a fibre product. -/
theorem isPullback_complementBase :
    IsPullback (complementBaseProj B S hS iY hiY V) (complementBaseLift B S hS iY hiY V)
      V.1.hom (complementHom B S hS iY hiY) :=
  AlgebraicSpaces.isPullback_fiberProduct B S hS _ _

/-- The projection of the base change of the complement to `V` is étale, being a base change of
the open immersion of the complement. -/
theorem isEtale_complementBaseProj :
    IsEtale B S hS (complementBaseProj B S hS iY hiY V).hom :=
  isEtale_of_isPullback B S hS (complementBaseLift B S hS iY hiY V)
    (complementBaseProj B S hS iY hiY V) (complementHom B S hS iY hiY) V.1.hom
    (isPullback_complementBase B S hS iY hiY V).flip
    (isEtale_complementHom B S hS iY hiY)

/-- The base change to `V` of the open complement of `Z`, as an object of the spaces-étale site
of `Y`. -/
def complementBaseObj : SpacesEtale B S hS Y :=
  ⟨Over.mk (complementBaseProj B S hS iY hiY V ≫ V.1.hom),
    isEtale_comp B S hS (isEtale_complementBaseProj B S hS iY hiY V) V.property⟩

/-- The projection of the base change of the complement, as a morphism of the spaces-étale site
of `Y`. -/
def complementBaseObjHom : complementBaseObj B S hS iY hiY V ⟶ V :=
  ObjectProperty.homMk (Over.homMk (complementBaseProj B S hS iY hiY V) rfl)

/-- If `p ≫ q = r`, then `q` maps the image under `p` of a point to its image under `r`. -/
private theorem pointsMap_comp_eq_apply {A A' A'' : AlgebraicSpaces B S hS}
    (p : A ⟶ A') (q : A' ⟶ A'') (r : A ⟶ A'') (h : p ≫ q = r) (y : points B S hS A.1) :
    pointsMap B S hS A'.1 q.hom (pointsMap B S hS A.1 p.hom y) = pointsMap B S hS A.1 r.hom y :=
  (pointsMap_comp_apply B S hS _ _ y).symm.trans (congrArg (fun t => pointsMap B S hS _ t.hom y) h)

/-- **The base change of the complement misses `Z`.**  Its structure morphism to `Y` factors
through the inclusion of the open complement of `Z`, whose image is the complement of the image
of `Z` by Stacks 03BZ. -/
theorem range_pointsMap_complementBaseObj :
    Set.range (pointsMap B S hS
        ((SpacesEtale.toSpaces B S hS Y).obj (complementBaseObj B S hS iY hiY V)).1
        (complementBaseObj B S hS iY hiY V).1.hom.hom) ⊆
      (Set.range (pointsMap B S hS Z.1 iY.hom))ᶜ := by
  rintro x ⟨y, rfl⟩
  rw [← range_pointsMap_complementHom B S hS iY hiY]
  refine ⟨pointsMap B S hS _ (complementBaseLift B S hS iY hiY V).hom y, ?_⟩
  exact pointsMap_comp_eq_apply B S hS _ _ _ (isPullback_complementBase B S hS iY hiY V).w.symm y

/-- **The excision covering of an object of the spaces-étale site**: the two-element family
consisting of the agreement locus of `g₁` and `g₂` and of the base change to `V` of the open
complement of `Z`.

The index type is `ULift.{u + 1} Bool` because the spaces-étale precoverage quantifies over
families indexed at that universe. -/
abbrev agreementCover : PreZeroHypercover.{u + 1} V where
  I₀ := ULift.{u + 1} Bool
  X i := Bool.rec (complementBaseObj B S hS iY hiY V) (agreementObj B S hS f hf V g₁ g₂) i.down
  f i := Bool.rec (motive := fun b =>
      (Bool.rec (complementBaseObj B S hS iY hiY V) (agreementObj B S hS f hf V g₁ g₂) b :
        SpacesEtale B S hS Y) ⟶ V)
    (complementBaseObjHom B S hS iY hiY V) (agreementObjHom B S hS f hf V g₁ g₂) i.down

/-- The base change to `V` of the closed subspace `Z`. -/
def subspaceBase : AlgebraicSpaces B S hS :=
  AlgebraicSpaces.fiberProduct B S hS V.1.hom iY

/-- The projection of the base change of the subspace to `V`. -/
def subspaceBaseProj : subspaceBase B S hS iY V ⟶ V.1.left :=
  ObjectProperty.homMk (pullback.fst V.1.hom.hom iY.hom)

/-- The projection of the base change of the subspace to `Z`. -/
def subspaceBaseLift : subspaceBase B S hS iY V ⟶ Z :=
  ObjectProperty.homMk (pullback.snd V.1.hom.hom iY.hom)

/-- The base change of the subspace is a fibre product. -/
theorem isPullback_subspaceBase :
    IsPullback (subspaceBaseProj B S hS iY V) (subspaceBaseLift B S hS iY V) V.1.hom iY :=
  AlgebraicSpaces.isPullback_fiberProduct B S hS _ _

/-- The base change of the subspace is a fibre product of the underlying presheaves. -/
theorem isPullback_hom_subspaceBase :
    IsPullback (subspaceBaseProj B S hS iY V).hom (subspaceBaseLift B S hS iY V).hom
      V.1.hom.hom iY.hom :=
  IsPullback.of_hasPullback _ _

/-- **The image of the base change of the subspace is the part of `V` lying over `Z`**, by
Stacks 03H4. -/
theorem range_pointsMap_subspaceBaseProj :
    Set.range (pointsMap B S hS (subspaceBase B S hS iY V).1
        (subspaceBaseProj B S hS iY V).hom) =
      pointsMap B S hS ((SpacesEtale.toSpaces B S hS Y).obj V).1 V.1.hom.hom ⁻¹'
        Set.range (pointsMap B S hS Z.1 iY.hom) := by
  simpa [Set.image_univ] using (preimage_image_pointsMap_of_isPullback B S hS
    (isPullback_hom_subspaceBase B S hS iY V).flip Set.univ).symm

variable {iX : W ⟶ X} {k : W ⟶ Z} [IsIso k]

/-- **The two morphisms agree after base change to `Z`.**  Their composites with `f` are both
the structure morphism of `V`, which over the base change factors through `Z`, so
`AlgebraicGeometry.Space.eq_of_comp_eq_of_factorsThrough_subspace` applies: this is the first
of the two uses the excision argument makes of the hypothesis that `f` is an isomorphism over
`Z`. -/
theorem subspaceBaseProj_comp_eq (hk : IsPullback k.hom iX.hom iY.hom f.hom) :
    subspaceBaseProj B S hS iY V ≫ (SpacesEtale.toSpaces B S hS Y).map g₁ =
      subspaceBaseProj B S hS iY V ≫ (SpacesEtale.toSpaces B S hS Y).map g₂ := by
  have hA : ∀ a : V.1.left ⟶ X, a ≫ f = V.1.hom →
      (subspaceBaseProj B S hS iY V ≫ a).hom ≫ f.hom =
        (subspaceBaseLift B S hS iY V).hom ≫ iY.hom := by
    intro a hafa
    exact congrArg (fun q : subspaceBase B S hS iY V ⟶ Y => q.hom)
      ((congrArg (subspaceBaseProj B S hS iY V ≫ ·) hafa).trans
        (isPullback_subspaceBase B S hS iY V).w)
  exact ObjectProperty.hom_ext _ (eq_of_comp_eq_of_factorsThrough_subspace B S hS hk
    (subspaceBaseProj B S hS iY V ≫ (SpacesEtale.toSpaces B S hS Y).map g₁).hom
    (subspaceBaseProj B S hS iY V ≫ (SpacesEtale.toSpaces B S hS Y).map g₂).hom
    (subspaceBaseLift B S hS iY V).hom
    (hA _ (toSpaces_map_comp_eq B S hS f hf g₁))
    (hA _ (toSpaces_map_comp_eq B S hS f hf g₂)))

/-- **Everything of `V` lying over `Z` factors through the agreement locus.**  The two
morphisms `g₁` and `g₂` agree after base change to `V ×_Y Z`, so that base change factors
through the agreement locus; its image on points is the part of `V` lying over `Z`. -/
theorem preimage_subset_range_pointsMap_agreementProj
    (hk : IsPullback k.hom iX.hom iY.hom f.hom) :
    pointsMap B S hS ((SpacesEtale.toSpaces B S hS Y).obj V).1 V.1.hom.hom ⁻¹'
        Set.range (pointsMap B S hS Z.1 iY.hom) ⊆
      Set.range (pointsMap B S hS (agreementLocus B S hS f
        (toSpaces_map_comp_eq_comp B S hS f hf g₁ g₂)).1
        (agreementProj B S hS f (toSpaces_map_comp_eq_comp B S hS f hf g₁ g₂)).hom) := by
  rw [← range_pointsMap_subspaceBaseProj B S hS iY V]
  rintro x ⟨y, rfl⟩
  refine ⟨pointsMap B S hS _ (agreementFactor B S hS f
    (toSpaces_map_comp_eq_comp B S hS f hf g₁ g₂) (subspaceBaseProj B S hS iY V)
    (subspaceBaseProj_comp_eq B S hS f hf iY V g₁ g₂ hk)).hom y, ?_⟩
  exact pointsMap_comp_eq_apply B S hS _ _ _
    (agreementFactor_comp_agreementProj B S hS f _ _ _) y

/-- **The agreement family is a covering family.**  A point of `V` over `Z` lifts to the
agreement locus by
`AlgebraicGeometry.Space.preimage_subset_range_pointsMap_agreementProj`, and a point of `V`
outside `Z` lifts to the base change of the open complement by Stacks 03H4. -/
theorem isCovering_agreementCover (hk : IsPullback k.hom iX.hom iY.hom f.hom) :
    SpacesEtale.IsCovering B S hS Y
      ⟨V, agreementCover B S hS f hf iY hiY V g₁ g₂⟩ := by
  intro x
  by_cases hx : pointsMap B S hS ((SpacesEtale.toSpaces B S hS Y).obj V).1 V.1.hom.hom x ∈
      Set.range (pointsMap B S hS Z.1 iY.hom)
  · obtain ⟨y, hy⟩ := preimage_subset_range_pointsMap_agreementProj B S hS f hf iY V g₁ g₂
      hk hx
    exact ⟨ULift.up true, y, hy⟩
  · obtain ⟨c, hc⟩ := (range_pointsMap_complementHom B S hS iY hiY).ge hx
    obtain ⟨v, hv, -⟩ := exists_point_of_isPullback B S hS
      (isPullback_complementBase B S hS iY hiY V) x c hc.symm
    exact ⟨ULift.up false, v, hv⟩

/-- The sieve generated by the agreement family is a covering sieve of the spaces-étale
topology. -/
theorem generate_agreementCover_mem_topology
    (hk : IsPullback k.hom iX.hom iY.hom f.hom) :
    Sieve.generate (agreementCover B S hS f hf iY hiY V g₁ g₂).presieve₀ ∈
      SpacesEtale.topology B S hS Y V :=
  Precoverage.generate_mem_toGrothendieck
    ⟨_, rfl, isCovering_agreementCover B S hS f hf iY hiY V g₁ g₂ hk⟩

include hiY in
/-- **A sheaf vanishing away from `Z` restricts along two morphisms over `Y` by the same map.**
Let `Q` be a sheaf on the spaces-étale site of `Y`, with values in an arbitrary category, which
vanishes on every object of the site whose image misses `Z`, and let `g₁, g₂ : V ⟶ X` be two
morphisms of the site.  Then restriction along `g₁` and restriction along `g₂` are the same
morphism `Q(X) ⟶ Q(V)`.

This is the sheaf condition for the two-element covering
`AlgebraicGeometry.Space.agreementCover`: on the agreement locus the two morphisms are equal,
and the other member of the covering misses `Z`, so `Q` vanishes there. -/
theorem map_eq_of_hom_etaleObject {A : Type w} [Category.{w'} A]
    (Q : Sheaf (SpacesEtale.topology B S hS Y) A)
    (hzero : ∀ V' : SpacesEtale B S hS Y,
      Set.range (pointsMap B S hS ((SpacesEtale.toSpaces B S hS Y).obj V').1 V'.1.hom.hom) ⊆
          (Set.range (pointsMap B S hS Z.1 iY.hom))ᶜ →
        IsZero (Q.obj.obj (op V')))
    (hk : IsPullback k.hom iX.hom iY.hom f.hom) :
    Q.obj.map g₁.op = Q.obj.map g₂.op := by
  refine Q.property.hom_ext_ofArrows (agreementCover B S hS f hf iY hiY V g₁ g₂).f
    (generate_agreementCover_mem_topology B S hS f hf iY hiY V g₁ g₂ hk) ?_
  rintro ⟨i⟩
  cases i with
  | false =>
      exact (hzero (complementBaseObj B S hS iY hiY V)
        (range_pointsMap_complementBaseObj B S hS iY hiY V)).eq_of_tgt _ _
  | true =>
      rw [← Q.obj.map_comp, ← Q.obj.map_comp, ← op_comp, ← op_comp,
        agreementObjHom_comp_eq B S hS f hf V g₁ g₂]

end Covering

end AlgebraicGeometry.Space

end
