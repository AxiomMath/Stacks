module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.CoordinateProjection
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.GeneralLinearTwoPowerAction
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProperCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFiniteImageNearFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# The contraction step of Stacks 0AEM: applying 0AEJ to the action of `(GL₂)^m`

The proof of [Stacks, Tag 0AEM] contracts a morphism `f : (ℙ¹_k)^m ⟶ Z` by the following step.
Let `G = (GL_{2,k})^m`, acting on `(ℙ¹_k)^m`, and let `C ⊆ (ℙ¹_k)^m` be a closed subspace which
`f` maps to a single point. Apply [Stacks, Tag 0AEJ] to the triangle

```
G × C --(g, c) ↦ (g, f(g · c))--> G × Z
    \                             /
     \      projections to G     /
      \                         /
             G
```

over `G`. The conclusion is that `b`, the `k`-rational point of `|G|` given by the `m`-tuple of
identity matrices, has an open neighbourhood `U ⊆ G` over which `(G × C)|_U ⟶ (G × Z)|_U` factors
through a closed subspace of `(G × Z)|_U` which is *finite over `U`*. That is the statement the
induction of 0AEM consumes: at each `k`-point `M ∈ U(k)` of the group it says that the translate
`M · C` is again carried by `f` into a finite closed subspace of `Z`, which is what makes the
source's "`g(C)` is mapped to a point for `g ∈ G(k)` lying in a Zariski open `U ⊂ G`" available.

The three hypotheses 0AEJ asks for are supplied as follows. The first projection `G × C ⟶ G` is
proper because `C` is proper over `Spec k`: it is a closed subspace of `(ℙ¹_k)^m`, whose structure
morphism is proper by
`AlgebraicGeometry.Space.isProper_projectiveSpacePowerOver`, an induction on `m` over the slice
category. The first projection `G × Z ⟶ G` is separated and locally of finite type because `Z` is,
both being base changes along `G ⟶ Spec k`. The finiteness hypothesis is verified at the identity
point: the fibre of `G × C ⟶ G` there is `C`, the action is trivial there — this is
`AlgebraicGeometry.Space.projectiveLinePowerPointSection_comp_generalLinearTwoPowerAction` at the
identity tuple — and `f` is constant on `C` by assumption, so the whole fibre is carried to a
single point of `|G × Z|`, and `Spec k` has one point.

## Main definitions

* `AlgebraicGeometry.Space.generalLinearTwoPowerSitePoint`: the `k`-point of `(GL₂)^m` named by an
  `m`-tuple of invertible two-by-two matrices, as a morphism of the big fppf site.
* `AlgebraicGeometry.Space.generalLinearTwoPowerFieldValuedPoint`: that `k`-point as a
  field-valued point of the functor of points of `(GL₂)^m`, whose class is the point of
  `|(GL₂)^m|` that 0AEJ is applied at.
* `AlgebraicGeometry.Space.projectiveLinePowerPointSection`: the fibre of
  `(GL₂)^m ×_{Spec k} (ℙ¹_k)^m` over that `k`-point, as a morphism of functors of points.
* `AlgebraicGeometry.Space.generalLinearTwoPowerSubspaceInclusion` and
  `AlgebraicGeometry.Space.generalLinearTwoPowerOrbitGraph`: the inclusion of `G × C` in
  `G × (ℙ¹_k)^m` and the morphism `(g, c) ↦ (g, f(g · c))` over `G` built from it.
* `AlgebraicGeometry.Space.generalLinearTwoPowerSubspacePointSection`: the fibre of `G × C` over
  the `k`-point of `G` named by `M`.

## Main results

* `AlgebraicGeometry.Space.isProper_projectiveSpacePowerOver` and
  `AlgebraicGeometry.Space.isProper_projectiveLinePowerToBase`: the `m`-fold self-product of
  `ℙ¹_k` over `Spec k` is proper over `Spec k`, as a scheme and as an algebraic space.
* `AlgebraicGeometry.Space.projectiveLinePowerPointSection_comp_generalLinearTwoPowerAction`: the
  action restricted to the fibre over the `k`-point named by `M` is the automorphism `x ↦ M · x`;
  at the identity tuple it is the identity
  (`AlgebraicGeometry.Space.projectiveLinePowerPointSection_one_comp_generalLinearTwoPowerAction`).
* `AlgebraicGeometry.Space.comp_generalLinearTwoPowerOrbitGraph_comp_snd_of_comp_fst_eq`: **the
  orbit map** — over the `k`-point `M` of the group, the component in `Z` of
  `(g, c) ↦ (g, f(g · c))` is `c ↦ f(M · c)`.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_isFinite_generalLinearTwoPowerOrbitGraph`: **the
  contraction step** — the application of [Stacks, Tag 0AEJ] to the action described above.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_forall_isFinite_comp_eq_orbitMap`: the same
  conclusion read at the `k`-points of the open neighbourhood — for every `k`-point `M` of `G`
  factoring through `U`, the orbit map `c ↦ f(M · c)` on `C` factors through an algebraic space
  finite over `Spec k`. This is the form the induction of 0AEM consumes.

## References

* [Stacks Project, Tag 0AEJ](https://stacks.math.columbia.edu/tag/0AEJ)
* [Stacks Project, Tag 0AEM](https://stacks.math.columbia.edu/tag/0AEM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (k : Type u) [Field k] (B : BigFppfSite.{u})
  (hk : B.Contains (Spec (CommRingCat.of k))) (m : ℕ)

/-! ### Properness of a finite power of the projective line -/

/-- A binary product in a slice category of two objects proper over the base is proper over the
base: one projection is the base change of the other factor's structure morphism. -/
private theorem isProper_overProd {S : Scheme.{u}} (X Y : Over S) [HasBinaryProduct X Y]
    (hX : _root_.AlgebraicGeometry.IsProper X.hom)
    (hY : _root_.AlgebraicGeometry.IsProper Y.hom) :
    _root_.AlgebraicGeometry.IsProper (X ⨯ Y).hom := by
  have hpb := Over.isPullback_of_binaryFan_isLimit _ (prodIsProd X Y)
  have hfst : _root_.AlgebraicGeometry.IsProper (prod.fst : X ⨯ Y ⟶ X).left :=
    MorphismProperty.of_isPullback hpb.flip hY
  rw [show (X ⨯ Y).hom = (prod.fst : X ⨯ Y ⟶ X).left ≫ X.hom from (Over.w _).symm]
  infer_instance

/-- Properness over the base of an object of a slice category is invariant under isomorphism. -/
private theorem isProper_overIso {S : Scheme.{u}} {X Y : Over S} (e : X ≅ Y)
    (hY : _root_.AlgebraicGeometry.IsProper Y.hom) :
    _root_.AlgebraicGeometry.IsProper X.hom := by
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  rw [show X.hom = e.hom.left ≫ Y.hom from (Over.w e.hom).symm]
  infer_instance

/-- **The `m`-fold self-product of `ℙ¹_k` over `Spec k` is proper over `Spec k`.** The empty
product is the base itself, and a product with one more factor is a binary product of a proper
object with `ℙ¹_k`, which is proper over `Spec k`. -/
theorem isProper_projectiveSpacePowerOver :
    _root_.AlgebraicGeometry.IsProper (projectiveSpacePowerOver k 1 m).hom := by
  induction m with
  | zero =>
    refine isProper_overIso (S := Spec (CommRingCat.of k))
      (IsTerminal.uniqueUpToIso ?_ Over.mkIdTerminal) ?_
    · exact IsTerminal.ofUniqueHom (fun _ => Pi.lift fun i => Fin.elim0 i)
        (fun _ _ => Pi.hom_ext _ _ fun i => Fin.elim0 i)
    · change _root_.AlgebraicGeometry.IsProper (𝟙 (Spec (CommRingCat.of k)))
      infer_instance
  | succ n ih =>
    refine isProper_overIso (piFinSuccIso _ n) (isProper_overProd _ _ ih ?_)
    exact (inferInstance : _root_.AlgebraicGeometry.IsProper
      (projectiveSpaceOverRing 1 (CommRingCat.of k) ↘ Spec (CommRingCat.of k)))

/-- The structure morphism of the site object of `(ℙ¹_k)^m`, as a morphism to the terminal object
of the big fppf site over `Spec k`. -/
def projectiveSpacePowerSiteStructure :
    projectiveSpacePowerSiteObject k B hk m ⟶
      (Over.mk (𝟙 (B.obj hk)) : BigFppfOver B (Spec (CommRingCat.of k)) hk) :=
  Over.homMk (projectiveSpacePowerSiteObject k B hk m).hom

/-- **`(ℙ¹_k)^m` is proper over `Spec k`** as an algebraic space over `Spec k`: its functor of
points is that of an object of the site whose structure morphism is proper. -/
theorem isProper_projectiveLinePowerToBase :
    IsProper B (Spec (CommRingCat.of k)) hk
      (projectiveLinePowerToBase k B hk (Fin m)) := by
  have hmap : IsProper B (Spec (CommRingCat.of k)) hk
      (yoneda.map (projectiveSpacePowerSiteStructure k B hk m)) :=
    isProper_yoneda_map B (Spec (CommRingCat.of k)) hk _
      (isProper_projectiveSpacePowerOver k m)
  have he : projectiveLinePowerToBase k B hk (Fin m) =
      (projectiveSpacePowerYonedaIso k B hk m).inv ≫
        yoneda.map (projectiveSpacePowerSiteStructure k B hk m) :=
    (base_isTerminal k B hk).hom_ext _ _
  rw [he]
  exact (isProper_isIso_comp_iff B (Spec (CommRingCat.of k)) hk
    (projectiveSpacePowerYonedaIso k B hk m).inv _).2 hmap

/-! ### The identity tuple acts trivially -/

/-- **The `m`-tuple of identity matrices acts on `(ℙ¹_k)^m` by the identity**: the construction of
the automorphism attached to a matrix is multiplicative, so it carries the identity matrix to the
identity automorphism in each coordinate. -/
theorem projectiveSpacePowerMatrixAut_one_hom :
    (projectiveSpacePowerMatrixAut k 1 m 1).asIso.hom = 𝟙 (projectiveSpacePowerOver k 1 m) := by
  refine Pi.hom_ext _ _ fun i => ?_
  rw [projectiveSpacePowerMatrixAut_hom_π,
    show ((1 : Fin m → Matrix.GeneralLinearGroup (Fin 2) k) i) = 1 from rfl, map_one]
  change Pi.π _ i ≫ 𝟙 _ = _
  simp

/-- The automorphism of the site object of `(ℙ¹_k)^m` attached to the `m`-tuple of identity
matrices is the identity. -/
theorem projectiveSpacePowerSiteMatrixAut_one_hom :
    (projectiveSpacePowerSiteMatrixAut k B hk m 1).hom =
      𝟙 (projectiveSpacePowerSiteObject k B hk m) := by
  rw [projectiveSpacePowerSiteMatrixAut_hom,
    show projectiveSpacePowerMatrixAutOver k B hk m 1 =
      𝟙 ((Over.post (X := B.obj hk) B.inclusion).obj
        (projectiveSpacePowerSiteObject k B hk m)) from
      projectiveSpacePowerMatrixAut_one_hom k m]
  exact (fullyFaithful_overPost_bigFppfInclusion B (Spec (CommRingCat.of k)) hk).preimage_id

/-- The automorphism of `AlgebraicGeometry.Space.projectiveLinePower` attached to the `m`-tuple of
identity matrices is the identity. -/
theorem projectiveLinePowerFunctorMatrixAut_one_hom :
    (projectiveLinePowerFunctorMatrixAut k B hk m 1).hom =
      𝟙 (projectiveLinePower k B hk (Fin m)) := by
  rw [projectiveLinePowerFunctorMatrixAut, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, projectiveSpacePowerSiteMatrixAut_one_hom,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]

/-! ### The `k`-point of `(GL₂)^m` named by a tuple of matrices -/

section Point

variable (M : Fin m → Matrix.GeneralLinearGroup (Fin 2) k)

/-- **The `k`-point of `(GL₂)^m` named by an `m`-tuple `M` of invertible two-by-two matrices**, as
a morphism of the big fppf site over `Spec k` from the terminal object: the spectrum of the
`k`-algebra map `AlgebraicGeometry.generalLinearTwoPowerPoint` evaluating the coordinates at the
entries of `M`. -/
def generalLinearTwoPowerSitePoint :
    (Over.mk (𝟙 (B.obj hk)) : BigFppfOver B (Spec (CommRingCat.of k)) hk) ⟶
      generalLinearTwoPowerSiteObject k B hk m :=
  Over.homMk (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom (generalLinearTwoPowerPoint k m M)))) (by
    apply ObjectProperty.hom_ext
    exact specMap_comp_specMap_eq_id k (algebraMap k (generalLinearTwoPowerCoordinateRing k m))
      (generalLinearTwoPowerPoint k m M)
      (generalLinearTwoPowerPoint_comp_algebraMap k m M))

/-- **The `k`-point of `(GL₂)^m` named by `M`, as a field-valued point of the functor of points of
`(GL₂)^m`.** Its field of definition is `k` itself and its structure morphism to the base is the
identity, so the object of the site it is defined on is the terminal one. -/
def generalLinearTwoPowerFieldValuedPoint :
    FieldValuedPoint B (Spec (CommRingCat.of k)) hk
      (yoneda.obj (generalLinearTwoPowerSiteObject k B hk m)) where
  carrier := k
  contained := hk
  toBase := 𝟙 _
  value := generalLinearTwoPowerSitePoint k B hk m M

/-- The object of the site on which the `k`-point named by `M` is defined is the terminal one. -/
theorem generalLinearTwoPowerFieldValuedPoint_siteObject :
    (generalLinearTwoPowerFieldValuedPoint k B hk m M).siteObject =
      (Over.mk (𝟙 (B.obj hk)) : BigFppfOver B (Spec (CommRingCat.of k)) hk) :=
  rfl

/-- The morphism of functors of points presented by the `k`-point named by `M` is the Yoneda image
of that `k`-point. -/
theorem fieldMorphism_generalLinearTwoPowerFieldValuedPoint :
    fieldMorphism B (Spec (CommRingCat.of k)) hk _
        (generalLinearTwoPowerFieldValuedPoint k B hk m M) =
      yoneda.map (generalLinearTwoPowerSitePoint k B hk m M) :=
  rfl

/-! ### The two components of the fibre over a `k`-point of the group -/

/-- A composite of two morphisms of the big fppf site, each given as the preimage of a morphism of
schemes over `Spec k`, equals `w` as soon as the composite of the two morphisms of schemes equals
the image of `w`. -/
private theorem preimage_comp_preimage_eq {X Y Z : BigFppfOver B (Spec (CommRingCat.of k)) hk}
    (a : (Over.post (X := B.obj hk) B.inclusion).obj X ⟶
      (Over.post (X := B.obj hk) B.inclusion).obj Y)
    (b : (Over.post (X := B.obj hk) B.inclusion).obj Y ⟶
      (Over.post (X := B.obj hk) B.inclusion).obj Z) (w : X ⟶ Z)
    (h : a ≫ b = (Over.post (X := B.obj hk) B.inclusion).map w) :
    (fullyFaithful_overPost_bigFppfInclusion B (Spec (CommRingCat.of k)) hk).preimage a ≫
        (fullyFaithful_overPost_bigFppfInclusion B (Spec (CommRingCat.of k)) hk).preimage b =
      w := by
  apply (fullyFaithful_overPost_bigFppfInclusion B (Spec (CommRingCat.of k)) hk).map_injective
  rw [Functor.map_comp, Functor.FullyFaithful.map_preimage, Functor.FullyFaithful.map_preimage]
  exact h

/-- The fibre of `(GL₂)^m ×_{Spec k} (ℙ¹_k)^m` over the `k`-point named by `M` is a section of the
projection to `(ℙ¹_k)^m`, in the big fppf site. -/
theorem generalLinearTwoPowerPointSection_comp_projectiveSpacePowerProjection :
    generalLinearTwoPowerPointSection k B hk m M ≫ projectiveSpacePowerProjection k B hk m =
      𝟙 _ := by
  refine preimage_comp_preimage_eq k B hk (generalLinearTwoPowerPointSectionOver k B hk m M)
    (projectiveSpacePowerProjectionOver k B hk m) _ ?_
  rw [CategoryTheory.Functor.map_id]
  apply Over.OverMorphism.ext
  change generalLinearTwoPowerPointSectionHom k m M ≫
      pullback.fst (projectiveSpacePowerOver k 1 m).hom
        (Spec.map (generalLinearTwoPowerStructureMap k m)) = 𝟙 _
  exact pullbackSectionOfRetraction_comp_fst _ _ _ _

/-- The fibre of `(GL₂)^m ×_{Spec k} (ℙ¹_k)^m` over the `k`-point named by `M` lies over that
point: its composite with the projection to `(GL₂)^m` is the structure morphism of `(ℙ¹_k)^m`
followed by the `k`-point. -/
theorem generalLinearTwoPowerPointSection_comp_generalLinearTwoPowerProjection :
    generalLinearTwoPowerPointSection k B hk m M ≫ generalLinearTwoPowerProjection k B hk m =
      projectiveSpacePowerSiteStructure k B hk m ≫
        generalLinearTwoPowerSitePoint k B hk m M :=
  preimage_comp_preimage_eq k B hk (generalLinearTwoPowerPointSectionOver k B hk m M)
    (generalLinearTwoPowerProjectionOver k B hk m) _
    (Over.OverMorphism.ext (generalLinearTwoPowerPointSectionHom_comp_snd k m M))

/-! ### The fibre of the action over a `k`-point of the group -/

/-- **The fibre of `(GL₂)^m ×_{Spec k} (ℙ¹_k)^m` over the `k`-point of `(GL₂)^m` named by `M`**, as
a morphism of functors of points: the section
`AlgebraicGeometry.Space.generalLinearTwoPowerPointSection` read through the identification of the
functor of points of the site object of `(ℙ¹_k)^m` with
`AlgebraicGeometry.Space.projectiveLinePower`. -/
def projectiveLinePowerPointSection :
    projectiveLinePower k B hk (Fin m) ⟶
      yoneda.obj (generalLinearTwoPowerProjectiveLinePowerSiteObject k B hk m) :=
  (projectiveSpacePowerYonedaIso k B hk m).inv ≫
    yoneda.map (generalLinearTwoPowerPointSection k B hk m M)

/-- The fibre over a `k`-point of the group is a section of the projection to `(ℙ¹_k)^m`. -/
theorem projectiveLinePowerPointSection_comp_projectiveLinePowerFunctorProjection :
    projectiveLinePowerPointSection k B hk m M ≫
        projectiveLinePowerFunctorProjection k B hk m =
      𝟙 (projectiveLinePower k B hk (Fin m)) := by
  rw [projectiveLinePowerPointSection, projectiveLinePowerFunctorProjection, Category.assoc,
    ← Category.assoc (yoneda.map (generalLinearTwoPowerPointSection k B hk m M)),
    ← Functor.map_comp,
    generalLinearTwoPowerPointSection_comp_projectiveSpacePowerProjection k B hk m M,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]

/-- The fibre over the `k`-point named by `M` lies over that point: its composite with the
projection to `(GL₂)^m` is the constant morphism at `M`. -/
theorem projectiveLinePowerPointSection_comp_generalLinearTwoPowerFunctorProjection :
    projectiveLinePowerPointSection k B hk m M ≫
        generalLinearTwoPowerFunctorProjection k B hk m =
      (base_isTerminal k B hk).from (projectiveLinePower k B hk (Fin m)) ≫
        yoneda.map (generalLinearTwoPowerSitePoint k B hk m M) := by
  rw [projectiveLinePowerPointSection, generalLinearTwoPowerFunctorProjection, Category.assoc,
    ← Functor.map_comp,
    generalLinearTwoPowerPointSection_comp_generalLinearTwoPowerProjection k B hk m M,
    Functor.map_comp, ← Category.assoc]
  exact (base_isTerminal k B hk).hom_ext _ _ =≫ _

/-- **The action restricted to the fibre over the `k`-point named by `M` is the automorphism
`x ↦ M · x`.** -/
theorem projectiveLinePowerPointSection_comp_generalLinearTwoPowerAction :
    projectiveLinePowerPointSection k B hk m M ≫ generalLinearTwoPowerAction k B hk m =
      (projectiveLinePowerFunctorMatrixAut k B hk m M).hom := by
  rw [projectiveLinePowerPointSection, Category.assoc,
    generalLinearTwoPowerPointSection_comp_action k B hk m M, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp]

end Point


/-- **The action restricted to the fibre over the identity of `(GL₂)^m` is the identity.** This is
the one place where the contraction step of [Stacks, Tag 0AEM] needs a concrete `k`-point of the
group: it is the point at which the finiteness hypothesis of [Stacks, Tag 0AEJ] can be checked. -/
theorem projectiveLinePowerPointSection_one_comp_generalLinearTwoPowerAction :
    projectiveLinePowerPointSection k B hk m 1 ≫ generalLinearTwoPowerAction k B hk m =
      𝟙 (projectiveLinePower k B hk (Fin m)) := by
  rw [projectiveLinePowerPointSection_comp_generalLinearTwoPowerAction,
    projectiveLinePowerFunctorMatrixAut_one_hom]

/-! ### The triangle over the group that Stacks 0AEJ is applied to -/

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of presheaves on the big fppf site is deep (see the docstring)
/-- Pullbacks of presheaves on the big fppf site over `Spec k` (instance search times out
without this shortcut). -/
local instance hasPullbacks_presheaf_GeneralLinearTwoPowerContraction :
    HasPullbacks ((BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤ Type u) := inferInstance

/-- Pullbacks of presheaves on the big fppf site over `Spec k` exist (instance search times out
without this shortcut). -/
local instance (priority := high) hasPullback_presheaf_GeneralLinearTwoPowerContraction
    {X Y Z : (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

section Contraction

/-- The terminal presheaf on the big fppf site over `Spec k`: the functor of points of the base
itself. -/
abbrev baseFunctor : (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤ Type u :=
  yoneda.obj (Over.mk (𝟙 (B.obj hk)))

/-- The structure morphism to the base of a presheaf on the big fppf site over `Spec k`. -/
abbrev toBaseFunctor (W : (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤ Type u) :
    W ⟶ baseFunctor k B hk :=
  (base_isTerminal k B hk).from W

/-- The functor of points of `(GL₂)^m`. -/
abbrev generalLinearTwoPowerFunctor : (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤ Type u :=
  yoneda.obj (generalLinearTwoPowerSiteObject k B hk m)

/-- The structure morphism of `(GL₂)^m` to the base. -/
abbrev generalLinearTwoPowerToBase :
    generalLinearTwoPowerFunctor k B hk m ⟶ baseFunctor k B hk :=
  toBaseFunctor k B hk (generalLinearTwoPowerFunctor k B hk m)

variable {Z : (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤ Type u}
  (z : Z ⟶ baseFunctor k B hk)
  (f : projectiveLinePower k B hk (Fin m) ⟶ Z)
  (C : Subfunctor (projectiveLinePower k B hk (Fin m)))

/-- **The inclusion of `(GL₂)^m × C` into `(GL₂)^m × (ℙ¹_k)^m`**, for a subfunctor `C` of
`(ℙ¹_k)^m`: the pair of the projection to `(GL₂)^m` and the projection to `C` followed by its
inclusion, taken through the product decomposition
`AlgebraicGeometry.Space.isLimitBinaryFanFunctorProjections`. -/
def generalLinearTwoPowerSubspaceInclusion :
    pullback (generalLinearTwoPowerToBase k B hk m) (toBaseFunctor k B hk C.toFunctor) ⟶
      yoneda.obj (generalLinearTwoPowerProjectiveLinePowerSiteObject k B hk m) :=
  (isLimitBinaryFanFunctorProjections k B hk m).lift
    (BinaryFan.mk
      (pullback.fst (generalLinearTwoPowerToBase k B hk m)
        (toBaseFunctor k B hk C.toFunctor))
      (pullback.snd (generalLinearTwoPowerToBase k B hk m)
          (toBaseFunctor k B hk C.toFunctor) ≫ C.ι))

/-- The inclusion of `(GL₂)^m × C` into `(GL₂)^m × (ℙ¹_k)^m` followed by the projection to
`(GL₂)^m` is the first projection of `(GL₂)^m × C`. -/
@[reassoc]
theorem generalLinearTwoPowerSubspaceInclusion_comp_generalLinearTwoPowerFunctorProjection :
    generalLinearTwoPowerSubspaceInclusion k B hk m C ≫
        generalLinearTwoPowerFunctorProjection k B hk m =
      pullback.fst (generalLinearTwoPowerToBase k B hk m)
        (toBaseFunctor k B hk C.toFunctor) :=
  (isLimitBinaryFanFunctorProjections k B hk m).fac _ ⟨WalkingPair.left⟩

/-- The inclusion of `(GL₂)^m × C` into `(GL₂)^m × (ℙ¹_k)^m` followed by the projection to
`(ℙ¹_k)^m` is the second projection of `(GL₂)^m × C` followed by the inclusion of `C`. -/
@[reassoc]
theorem generalLinearTwoPowerSubspaceInclusion_comp_projectiveLinePowerFunctorProjection :
    generalLinearTwoPowerSubspaceInclusion k B hk m C ≫
        projectiveLinePowerFunctorProjection k B hk m =
      pullback.snd (generalLinearTwoPowerToBase k B hk m)
        (toBaseFunctor k B hk C.toFunctor) ≫ C.ι :=
  (isLimitBinaryFanFunctorProjections k B hk m).fac _ ⟨WalkingPair.right⟩

/-- **The morphism `(g, c) ↦ (g, f(g · c))` from `(GL₂)^m × C` to `(GL₂)^m × Z`**, the morphism
over `(GL₂)^m` that the contraction step of [Stacks, Tag 0AEM] applies [Stacks, Tag 0AEJ] to. -/
def generalLinearTwoPowerOrbitGraph :
    pullback (generalLinearTwoPowerToBase k B hk m) (toBaseFunctor k B hk C.toFunctor) ⟶
      pullback (generalLinearTwoPowerToBase k B hk m) z :=
  pullback.lift
    (pullback.fst (generalLinearTwoPowerToBase k B hk m)
      (toBaseFunctor k B hk C.toFunctor))
    (generalLinearTwoPowerSubspaceInclusion k B hk m C ≫
      generalLinearTwoPowerAction k B hk m ≫ f)
    ((base_isTerminal k B hk).hom_ext _ _)

/-- **`(g, c) ↦ (g, f(g · c))` lies over `(GL₂)^m`.** -/
@[reassoc]
theorem generalLinearTwoPowerOrbitGraph_comp_fst :
    generalLinearTwoPowerOrbitGraph k B hk m z f C ≫
        pullback.fst (generalLinearTwoPowerToBase k B hk m) z =
      pullback.fst (generalLinearTwoPowerToBase k B hk m)
        (toBaseFunctor k B hk C.toFunctor) :=
  pullback.lift_fst _ _ _

/-- **The component of `(g, c) ↦ (g, f(g · c))` in `Z` is `f` after the action.** -/
@[reassoc]
theorem generalLinearTwoPowerOrbitGraph_comp_snd :
    generalLinearTwoPowerOrbitGraph k B hk m z f C ≫
        pullback.snd (generalLinearTwoPowerToBase k B hk m) z =
      generalLinearTwoPowerSubspaceInclusion k B hk m C ≫
        generalLinearTwoPowerAction k B hk m ≫ f :=
  pullback.lift_snd _ _ _

/-! ### The fibre of the triangle over a `k`-point of the group -/

variable {V : (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤ Type u}
  (v : V ⟶ pullback (generalLinearTwoPowerToBase k B hk m) (toBaseFunctor k B hk C.toFunctor))
  (M : Fin m → Matrix.GeneralLinearGroup (Fin 2) k)

/-- **Over a `k`-point `M` of `(GL₂)^m`, the inclusion of `(GL₂)^m × C` into
`(GL₂)^m × (ℙ¹_k)^m` is the inclusion of `C` followed by the fibre of `(GL₂)^m × (ℙ¹_k)^m` over
that point.** The hypothesis says that `v` lands in the fibre over `M`. -/
theorem comp_generalLinearTwoPowerSubspaceInclusion_of_comp_fst_eq
    (hv : v ≫ pullback.fst (generalLinearTwoPowerToBase k B hk m)
        (toBaseFunctor k B hk C.toFunctor) =
      toBaseFunctor k B hk V ≫ yoneda.map (generalLinearTwoPowerSitePoint k B hk m M)) :
    v ≫ generalLinearTwoPowerSubspaceInclusion k B hk m C =
      (v ≫ pullback.snd (generalLinearTwoPowerToBase k B hk m)
          (toBaseFunctor k B hk C.toFunctor) ≫ C.ι) ≫
        projectiveLinePowerPointSection k B hk m M := by
  refine BinaryFan.IsLimit.hom_ext (isLimitBinaryFanFunctorProjections k B hk m) ?_ ?_
  · change v ≫ generalLinearTwoPowerSubspaceInclusion k B hk m C ≫
        generalLinearTwoPowerFunctorProjection k B hk m = _
    rw [generalLinearTwoPowerSubspaceInclusion_comp_generalLinearTwoPowerFunctorProjection, hv]
    change _ = (_ ≫ projectiveLinePowerPointSection k B hk m M) ≫
      generalLinearTwoPowerFunctorProjection k B hk m
    rw [Category.assoc,
      projectiveLinePowerPointSection_comp_generalLinearTwoPowerFunctorProjection,
      ← Category.assoc]
    exact (base_isTerminal k B hk).hom_ext _ _ =≫ _
  · change v ≫ generalLinearTwoPowerSubspaceInclusion k B hk m C ≫
        projectiveLinePowerFunctorProjection k B hk m = _
    rw [generalLinearTwoPowerSubspaceInclusion_comp_projectiveLinePowerFunctorProjection]
    change _ = (_ ≫ projectiveLinePowerPointSection k B hk m M) ≫
      projectiveLinePowerFunctorProjection k B hk m
    rw [Category.assoc,
      projectiveLinePowerPointSection_comp_projectiveLinePowerFunctorProjection,
      Category.comp_id]

/-- **The orbit map.** Over the `k`-point `M` of `(GL₂)^m`, the action restricted to
`(GL₂)^m × C` is the inclusion of `C` followed by the automorphism `x ↦ M · x` of `(ℙ¹_k)^m`. -/
@[reassoc]
theorem comp_generalLinearTwoPowerSubspaceInclusion_comp_action_of_comp_fst_eq
    (hv : v ≫ pullback.fst (generalLinearTwoPowerToBase k B hk m)
        (toBaseFunctor k B hk C.toFunctor) =
      toBaseFunctor k B hk V ≫ yoneda.map (generalLinearTwoPowerSitePoint k B hk m M)) :
    v ≫ generalLinearTwoPowerSubspaceInclusion k B hk m C ≫
        generalLinearTwoPowerAction k B hk m =
      (v ≫ pullback.snd (generalLinearTwoPowerToBase k B hk m)
          (toBaseFunctor k B hk C.toFunctor) ≫ C.ι) ≫
        (projectiveLinePowerFunctorMatrixAut k B hk m M).hom := by
  rw [← Category.assoc,
    comp_generalLinearTwoPowerSubspaceInclusion_of_comp_fst_eq k B hk m C v M hv,
    Category.assoc, projectiveLinePowerPointSection_comp_generalLinearTwoPowerAction]

/-- **The orbit map is what the fibre of `(g, c) ↦ (g, f(g · c))` over a `k`-point `M` of the
group computes**: on the part of `(GL₂)^m × C` lying over `M`, the component in `Z` of that
morphism is `c ↦ f(M · c)`.

This is the form in which the induction of [Stacks, Tag 0AEM] consumes the conclusion of
[Stacks, Tag 0AEJ]: a statement about the morphism over an open subset of the group becomes, at
each `k`-point `M` of that open subset, a statement about the single morphism
`C ↪ (ℙ¹_k)^m --M·--> (ℙ¹_k)^m --f--> Z`. -/
@[reassoc]
theorem comp_generalLinearTwoPowerOrbitGraph_comp_snd_of_comp_fst_eq
    (hv : v ≫ pullback.fst (generalLinearTwoPowerToBase k B hk m)
        (toBaseFunctor k B hk C.toFunctor) =
      toBaseFunctor k B hk V ≫ yoneda.map (generalLinearTwoPowerSitePoint k B hk m M)) :
    v ≫ generalLinearTwoPowerOrbitGraph k B hk m z f C ≫
        pullback.snd (generalLinearTwoPowerToBase k B hk m) z =
      (v ≫ pullback.snd (generalLinearTwoPowerToBase k B hk m)
          (toBaseFunctor k B hk C.toFunctor) ≫ C.ι) ≫
        (projectiveLinePowerFunctorMatrixAut k B hk m M).hom ≫ f := by
  rw [generalLinearTwoPowerOrbitGraph_comp_snd,
    comp_generalLinearTwoPowerSubspaceInclusion_comp_action_of_comp_fst_eq_assoc k B hk m C v M
      hv f]
  simp only [Category.assoc]

/-- **Over the identity of `(GL₂)^m` the action is trivial**: on the part of `(GL₂)^m × C` lying
over the identity `k`-point of the group, the action is the projection to `C`. This is the one
`k`-point of the group at which the finiteness hypothesis of [Stacks, Tag 0AEJ] can be read off a
constancy hypothesis on `f`. -/
@[reassoc]
theorem comp_generalLinearTwoPowerSubspaceInclusion_comp_action_of_comp_fst_eq_one
    (hv : v ≫ pullback.fst (generalLinearTwoPowerToBase k B hk m)
        (toBaseFunctor k B hk C.toFunctor) =
      toBaseFunctor k B hk V ≫ yoneda.map (generalLinearTwoPowerSitePoint k B hk m 1)) :
    v ≫ generalLinearTwoPowerSubspaceInclusion k B hk m C ≫
        generalLinearTwoPowerAction k B hk m =
      v ≫ pullback.snd (generalLinearTwoPowerToBase k B hk m)
        (toBaseFunctor k B hk C.toFunctor) ≫ C.ι := by
  rw [comp_generalLinearTwoPowerSubspaceInclusion_comp_action_of_comp_fst_eq k B hk m C v 1 hv,
    projectiveLinePowerFunctorMatrixAut_one_hom, Category.comp_id]

/-! ### The contraction step -/

section Apply

attribute [local instance] pointTopology

variable (ζ : baseFunctor k B hk ⟶ Z)

/-- Two composites into the base agree, so they still agree after one further morphism out of
the base. Stated over the presheaf category to keep the rearrangement away from the concrete
fibre products it is used on. -/
private theorem comp_comp_comp_comp_eq_comp_comp
    {W X Y X' R : (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤ Type u}
    (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ baseFunctor k B hk)
    (a' : W ⟶ X') (c' : X' ⟶ baseFunctor k B hk) (e : baseFunctor k B hk ⟶ R) :
    a ≫ b ≫ c ≫ e = a' ≫ c' ≫ e := by
  simpa only [Category.assoc] using (base_isTerminal k B hk).hom_ext (a ≫ b ≫ c) (a' ≫ c') =≫ e

/-- The section of `(GL₂)^m × Z ⟶ (GL₂)^m` over the identity `k`-point of the group whose
component in `Z` is the point `ζ`. -/
private def identityPointConstantSection :
    yoneda.obj (generalLinearTwoPowerFieldValuedPoint k B hk m 1).siteObject ⟶
      pullback (generalLinearTwoPowerToBase k B hk m) z :=
  pullback.lift
    (fieldMorphism B (Spec (CommRingCat.of k)) hk (generalLinearTwoPowerFunctor k B hk m)
      (generalLinearTwoPowerFieldValuedPoint k B hk m 1))
    (toBaseFunctor k B hk
        (yoneda.obj (generalLinearTwoPowerFieldValuedPoint k B hk m 1).siteObject) ≫ ζ)
    ((base_isTerminal k B hk).hom_ext _ _)

@[reassoc]
private theorem identityPointConstantSection_comp_fst :
    identityPointConstantSection k B hk m z ζ ≫
        pullback.fst (generalLinearTwoPowerToBase k B hk m) z =
      fieldMorphism B (Spec (CommRingCat.of k)) hk (generalLinearTwoPowerFunctor k B hk m)
        (generalLinearTwoPowerFieldValuedPoint k B hk m 1) :=
  pullback.lift_fst _ _ _

@[reassoc]
private theorem identityPointConstantSection_comp_snd :
    identityPointConstantSection k B hk m z ζ ≫
        pullback.snd (generalLinearTwoPowerToBase k B hk m) z =
      toBaseFunctor k B hk
          (yoneda.obj (generalLinearTwoPowerFieldValuedPoint k B hk m 1).siteObject) ≫ ζ :=
  pullback.lift_snd _ _ _

/-- The same section, read in the fibre of `(GL₂)^m × Z` over the identity `k`-point of the
group. -/
private def identityFibreConstantSection :
    yoneda.obj (generalLinearTwoPowerFieldValuedPoint k B hk m 1).siteObject ⟶
      pullback (pullback.fst (generalLinearTwoPowerToBase k B hk m) z)
        (fieldMorphism B (Spec (CommRingCat.of k)) hk (generalLinearTwoPowerFunctor k B hk m)
          (generalLinearTwoPowerFieldValuedPoint k B hk m 1)) :=
  pullback.lift (identityPointConstantSection k B hk m z ζ) (𝟙 _) (by
    rw [Category.id_comp]
    exact identityPointConstantSection_comp_fst k B hk m z ζ)

@[reassoc]
private theorem identityFibreConstantSection_comp_fst :
    identityFibreConstantSection k B hk m z ζ ≫
        pullback.fst (pullback.fst (generalLinearTwoPowerToBase k B hk m) z)
          (fieldMorphism B (Spec (CommRingCat.of k)) hk (generalLinearTwoPowerFunctor k B hk m)
            (generalLinearTwoPowerFieldValuedPoint k B hk m 1)) =
      identityPointConstantSection k B hk m z ζ :=
  pullback.lift_fst _ _ _

@[reassoc]
private theorem identityFibreConstantSection_comp_snd :
    identityFibreConstantSection k B hk m z ζ ≫
        pullback.snd (pullback.fst (generalLinearTwoPowerToBase k B hk m) z)
          (fieldMorphism B (Spec (CommRingCat.of k)) hk (generalLinearTwoPowerFunctor k B hk m)
            (generalLinearTwoPowerFieldValuedPoint k B hk m 1)) =
      𝟙 _ :=
  pullback.lift_snd _ _ _

/-- The part of `(GL₂)^m × C` lying over the identity `k`-point of the group does lie over that
point, in the form the triviality of the action over that point asks for: the morphism presented
by the point is the Yoneda image of the point, and the field of definition of the point is `k`
itself, so the fibre is a presheaf over the base. -/
private theorem fst_comp_fst_eq_identityPoint :
    pullback.fst
        (pullback.fst (generalLinearTwoPowerToBase k B hk m)
          (toBaseFunctor k B hk C.toFunctor))
        (fieldMorphism B (Spec (CommRingCat.of k)) hk (generalLinearTwoPowerFunctor k B hk m)
          (generalLinearTwoPowerFieldValuedPoint k B hk m 1)) ≫
      pullback.fst (generalLinearTwoPowerToBase k B hk m)
        (toBaseFunctor k B hk C.toFunctor) =
    toBaseFunctor k B hk
        (pullback
          (pullback.fst (generalLinearTwoPowerToBase k B hk m)
            (toBaseFunctor k B hk C.toFunctor))
          (fieldMorphism B (Spec (CommRingCat.of k)) hk (generalLinearTwoPowerFunctor k B hk m)
            (generalLinearTwoPowerFieldValuedPoint k B hk m 1))) ≫
      yoneda.map (generalLinearTwoPowerSitePoint k B hk m 1) := by
  rw [pullback.condition, ← fieldMorphism_generalLinearTwoPowerFieldValuedPoint k B hk m 1]
  exact (base_isTerminal k B hk).hom_ext _ _ =≫ _

/-- **The fibre of `(g, c) ↦ (g, f(g · c))` over the identity `k`-point of `(GL₂)^m` is
constant**: over the identity the action is trivial, and `f` is constant on `C`, so that fibre is
the constant section at `ζ`. -/
private theorem fst_comp_generalLinearTwoPowerOrbitGraph_eq
    (hconst : C.ι ≫ f = toBaseFunctor k B hk C.toFunctor ≫ ζ) :
    pullback.fst
          (pullback.fst (generalLinearTwoPowerToBase k B hk m)
            (toBaseFunctor k B hk C.toFunctor))
          (fieldMorphism B (Spec (CommRingCat.of k)) hk (generalLinearTwoPowerFunctor k B hk m)
            (generalLinearTwoPowerFieldValuedPoint k B hk m 1)) ≫
        generalLinearTwoPowerOrbitGraph k B hk m z f C =
      pullback.snd
          (pullback.fst (generalLinearTwoPowerToBase k B hk m)
            (toBaseFunctor k B hk C.toFunctor))
          (fieldMorphism B (Spec (CommRingCat.of k)) hk (generalLinearTwoPowerFunctor k B hk m)
            (generalLinearTwoPowerFieldValuedPoint k B hk m 1)) ≫
        identityPointConstantSection k B hk m z ζ := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, generalLinearTwoPowerOrbitGraph_comp_fst, Category.assoc,
      identityPointConstantSection_comp_fst]
    exact pullback.condition
  · rw [Category.assoc, generalLinearTwoPowerOrbitGraph_comp_snd, Category.assoc,
      identityPointConstantSection_comp_snd,
      comp_generalLinearTwoPowerSubspaceInclusion_comp_action_of_comp_fst_eq_one_assoc k B hk m C _
        (fst_comp_fst_eq_identityPoint k B hk m C) f, hconst]
    exact comp_comp_comp_comp_eq_comp_comp k B hk _ _ _ _ _ ζ

/-- The image on points of the fibre of `(g, c) ↦ (g, f(g · c))` over the identity `k`-point of
`(GL₂)^m` is finite: that fibre is constant, so the whole of it is carried to the single point of
`Spec k` sitting over the identity. This is the finiteness hypothesis of [Stacks, Tag 0AEJ]. -/
private theorem finite_range_pointsMap_of_isConstant
    (hconst : C.ι ≫ f = toBaseFunctor k B hk C.toFunctor ≫ ζ)
    (xy : pullback
          (pullback.fst (generalLinearTwoPowerToBase k B hk m)
            (toBaseFunctor k B hk C.toFunctor))
          (fieldMorphism B (Spec (CommRingCat.of k)) hk (generalLinearTwoPowerFunctor k B hk m)
            (generalLinearTwoPowerFieldValuedPoint k B hk m 1)) ⟶
        pullback (pullback.fst (generalLinearTwoPowerToBase k B hk m) z)
          (fieldMorphism B (Spec (CommRingCat.of k)) hk (generalLinearTwoPowerFunctor k B hk m)
            (generalLinearTwoPowerFieldValuedPoint k B hk m 1)))
    (h₁ : xy ≫ pullback.fst (pullback.fst (generalLinearTwoPowerToBase k B hk m) z)
          (fieldMorphism B (Spec (CommRingCat.of k)) hk (generalLinearTwoPowerFunctor k B hk m)
            (generalLinearTwoPowerFieldValuedPoint k B hk m 1)) =
      pullback.fst
          (pullback.fst (generalLinearTwoPowerToBase k B hk m)
            (toBaseFunctor k B hk C.toFunctor))
          (fieldMorphism B (Spec (CommRingCat.of k)) hk (generalLinearTwoPowerFunctor k B hk m)
            (generalLinearTwoPowerFieldValuedPoint k B hk m 1)) ≫
        generalLinearTwoPowerOrbitGraph k B hk m z f C)
    (h₂ : xy ≫ pullback.snd (pullback.fst (generalLinearTwoPowerToBase k B hk m) z)
          (fieldMorphism B (Spec (CommRingCat.of k)) hk (generalLinearTwoPowerFunctor k B hk m)
            (generalLinearTwoPowerFieldValuedPoint k B hk m 1)) =
      pullback.snd
          (pullback.fst (generalLinearTwoPowerToBase k B hk m)
            (toBaseFunctor k B hk C.toFunctor))
          (fieldMorphism B (Spec (CommRingCat.of k)) hk (generalLinearTwoPowerFunctor k B hk m)
            (generalLinearTwoPowerFieldValuedPoint k B hk m 1))) :
    Set.Finite (Set.range (pointsMap B (Spec (CommRingCat.of k)) hk _ xy)) := by
  have hxy : xy = pullback.snd
        (pullback.fst (generalLinearTwoPowerToBase k B hk m)
          (toBaseFunctor k B hk C.toFunctor))
        (fieldMorphism B (Spec (CommRingCat.of k)) hk (generalLinearTwoPowerFunctor k B hk m)
          (generalLinearTwoPowerFieldValuedPoint k B hk m 1)) ≫
      identityFibreConstantSection k B hk m z ζ := by
    refine pullback.hom_ext ?_ ?_
    · rw [h₁, Category.assoc, identityFibreConstantSection_comp_fst]
      exact fst_comp_generalLinearTwoPowerOrbitGraph_eq k B hk m z f C ζ hconst
    · rw [h₂, Category.assoc, identityFibreConstantSection_comp_snd, Category.comp_id]
  have : Finite (points B (Spec (CommRingCat.of k)) hk
      (yoneda.obj (generalLinearTwoPowerFieldValuedPoint k B hk m 1).siteObject)) :=
    @Finite.of_subsingleton _
      (subsingleton_points_yoneda_siteObject B (Spec (CommRingCat.of k)) hk
        (generalLinearTwoPowerFieldValuedPoint k B hk m 1))
  rw [hxy, pointsMap_comp]
  exact (Set.finite_range (pointsMap B (Spec (CommRingCat.of k)) hk _
    (identityFibreConstantSection k B hk m z ζ))).subset
    (Set.range_comp_subset_range _ _)

/-- **The contraction step of [Stacks, Tag 0AEM]**: the application of [Stacks, Tag 0AEJ] to the
action of `(GL₂)^m` on `(ℙ¹_k)^m`.

Let `Z` be an algebraic space over `k`, separated and locally of finite type over `Spec k`, let
`f : (ℙ¹_k)^m ⟶ Z`, and let `C` be a closed subspace of `(ℙ¹_k)^m` which `f` carries to a single
point `ζ` of `Z`. Then the `k`-point of `(GL₂)^m` given by the `m`-tuple of identity matrices has
an open neighbourhood `U ⊆ (GL₂)^m`, and there is a closed subspace `W` of
`((GL₂)^m × Z) ×_{(GL₂)^m} U`, *finite over `U`*, through which the restriction of
`(g, c) ↦ (g, f(g · c))` to `((GL₂)^m × C) ×_{(GL₂)^m} U` factors.

This is the step from which the source draws "`g(C)` is mapped to a point for `g ∈ G(k)` lying in
a Zariski open `U ⊂ G`": at a `k`-point of `U` the fibre of `W` is a closed subspace of `Z` finite
over `Spec k`, and the translate of `C` by that point is carried into it. -/
theorem exists_isOpenSubspace_isFinite_generalLinearTwoPowerOrbitGraph
    (hZ : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk Z)
    (hz_sep : IsSeparated B (Spec (CommRingCat.of k)) hk z)
    (hz_lft : IsLocallyOfFiniteType B (Spec (CommRingCat.of k)) hk z)
    (hC : IsClosedSubspace B (Spec (CommRingCat.of k)) hk C)
    (hconst : C.ι ≫ f = toBaseFunctor k B hk C.toFunctor ≫ ζ) :
    ∃ U : Subfunctor (generalLinearTwoPowerFunctor k B hk m),
      IsOpenSubspace B (Spec (CommRingCat.of k)) hk U ∧
      (generalLinearTwoPowerFieldValuedPoint k B hk m 1).class B (Spec (CommRingCat.of k)) hk
          (generalLinearTwoPowerFunctor k B hk m) ∈
        Set.range (pointsMap B (Spec (CommRingCat.of k)) hk U.toFunctor U.ι) ∧
      ∃ W : Subfunctor
          (pullback (pullback.fst (generalLinearTwoPowerToBase k B hk m) z) U.ι),
        IsClosedSubspace B (Spec (CommRingCat.of k)) hk W ∧
        (∃ r : pullback
              (pullback.fst (generalLinearTwoPowerToBase k B hk m)
                (toBaseFunctor k B hk C.toFunctor)) U.ι ⟶ W.toFunctor,
          r ≫ W.ι =
            pullback.map
              (pullback.fst (generalLinearTwoPowerToBase k B hk m)
                (toBaseFunctor k B hk C.toFunctor)) U.ι
              (pullback.fst (generalLinearTwoPowerToBase k B hk m) z) U.ι
              (generalLinearTwoPowerOrbitGraph k B hk m z f C) (𝟙 _) (𝟙 _)
              (by rw [Category.comp_id, generalLinearTwoPowerOrbitGraph_comp_fst])
              (by simp)) ∧
        IsFinite B (Spec (CommRingCat.of k)) hk
          (W.ι ≫ pullback.snd (pullback.fst (generalLinearTwoPowerToBase k B hk m) z) U.ι) := by
  have hT0 : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk (baseFunctor k B hk) :=
    isAlgebraicSpace_yoneda B (Spec (CommRingCat.of k)) hk _
  have hGG : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk
      (generalLinearTwoPowerFunctor k B hk m) :=
    isAlgebraicSpace_yoneda B (Spec (CommRingCat.of k)) hk _
  have hCfun : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk C.toFunctor := hC.1
  have hP : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk
      (projectiveLinePower k B hk (Fin m)) :=
    isAlgebraicSpace_projectiveLinePowerFin k B hk m
  -- `C` is proper over `Spec k`, being a closed subspace of the proper `(ℙ¹_k)^m`
  have hcT : IsProper B (Spec (CommRingCat.of k)) hk (toBaseFunctor k B hk C.toFunctor) := by
    rw [show toBaseFunctor k B hk C.toFunctor =
        C.ι ≫ projectiveLinePowerToBase k B hk (Fin m) from
      (base_isTerminal k B hk).hom_ext _ _]
    exact isProper_comp' B (Spec (CommRingCat.of k)) hk C.ι _ hP hT0
      (isProper_of_isClosedImmersion B (Spec (CommRingCat.of k)) hk hCfun hP C.ι hC.2)
      (isProper_projectiveLinePowerToBase k B hk m)
  exact exists_isOpenSubspace_isClosedSubspace_isFinite_of_isProper B
    (Spec (CommRingCat.of k)) hk
    (isAlgebraicSpace_pullback B (Spec (CommRingCat.of k)) hk _ _ hGG hCfun hT0)
    (isAlgebraicSpace_pullback B (Spec (CommRingCat.of k)) hk _ _ hGG hZ hT0) hGG
    (generalLinearTwoPowerOrbitGraph k B hk m z f C)
    (pullback.fst (generalLinearTwoPowerToBase k B hk m)
      (toBaseFunctor k B hk C.toFunctor))
    (pullback.fst (generalLinearTwoPowerToBase k B hk m) z)
    (generalLinearTwoPowerOrbitGraph_comp_fst k B hk m z f C) _
    (generalLinearTwoPowerFieldValuedPoint k B hk m 1) rfl
    (isProper_pullback_fst B (Spec (CommRingCat.of k)) hk hCfun hT0 hGG
      (toBaseFunctor k B hk C.toFunctor) (generalLinearTwoPowerToBase k B hk m) hcT)
    (isSeparated_pullback_fst_of_snd B (Spec (CommRingCat.of k)) hk z
      (generalLinearTwoPowerToBase k B hk m)
      (isSeparated_pullbackSnd B (Spec (CommRingCat.of k)) hk
        (generalLinearTwoPowerToBase k B hk m) hz_sep))
    (isLocallyOfFiniteType_pullback_fst' B (Spec (CommRingCat.of k)) hk hZ hT0 hGG z
      (generalLinearTwoPowerToBase k B hk m) hz_lft)
    (Or.inl (finite_range_pointsMap_of_isConstant k B hk m z f C ζ hconst _
      (pullback.lift_fst _ _ _) ((pullback.lift_snd _ _ _).trans (Category.comp_id _))))


/-! ### The consequence at a `k`-point of the open neighbourhood -/

/-- **The fibre of `(GL₂)^m × C` over the `k`-point `M` of the group**: the section of the
projection to `C` which lands over `M`. -/
def generalLinearTwoPowerSubspacePointSection
    (M : Fin m → Matrix.GeneralLinearGroup (Fin 2) k) :
    C.toFunctor ⟶
      pullback (generalLinearTwoPowerToBase k B hk m) (toBaseFunctor k B hk C.toFunctor) :=
  pullback.lift
    (toBaseFunctor k B hk C.toFunctor ≫ yoneda.map (generalLinearTwoPowerSitePoint k B hk m M))
    (𝟙 _) ((base_isTerminal k B hk).hom_ext _ _)

/-- The section of `(GL₂)^m × C` over the `k`-point `M`, followed by the projection to `(GL₂)^m`,
is the constant morphism at `M`. -/
@[reassoc]
theorem generalLinearTwoPowerSubspacePointSection_comp_fst
    (M : Fin m → Matrix.GeneralLinearGroup (Fin 2) k) :
    generalLinearTwoPowerSubspacePointSection k B hk m C M ≫
        pullback.fst (generalLinearTwoPowerToBase k B hk m)
          (toBaseFunctor k B hk C.toFunctor) =
      toBaseFunctor k B hk C.toFunctor ≫
        yoneda.map (generalLinearTwoPowerSitePoint k B hk m M) :=
  pullback.lift_fst _ _ _

/-- The section of `(GL₂)^m × C` over the `k`-point `M`, followed by the projection to `C`, is
the identity. -/
@[reassoc]
theorem generalLinearTwoPowerSubspacePointSection_comp_snd
    (M : Fin m → Matrix.GeneralLinearGroup (Fin 2) k) :
    generalLinearTwoPowerSubspacePointSection k B hk m C M ≫
        pullback.snd (generalLinearTwoPowerToBase k B hk m)
          (toBaseFunctor k B hk C.toFunctor) = 𝟙 _ :=
  pullback.lift_snd _ _ _

section Point

variable (M : Fin m → Matrix.GeneralLinearGroup (Fin 2) k)
  (U : Subfunctor (generalLinearTwoPowerFunctor k B hk m))

/-- The same section, read over the open subspace `U ⊆ (GL₂)^m` through which the `k`-point `M`
factors. -/
private def generalLinearTwoPowerSubspacePointSectionOver
    (s : baseFunctor k B hk ⟶ U.toFunctor)
    (hs : s ≫ U.ι = yoneda.map (generalLinearTwoPowerSitePoint k B hk m M)) :
    C.toFunctor ⟶
      pullback (pullback.fst (generalLinearTwoPowerToBase k B hk m)
        (toBaseFunctor k B hk C.toFunctor)) U.ι :=
  pullback.lift (generalLinearTwoPowerSubspacePointSection k B hk m C M)
    (toBaseFunctor k B hk C.toFunctor ≫ s) (by
      rw [generalLinearTwoPowerSubspacePointSection_comp_fst, Category.assoc, hs])

@[reassoc]
private theorem generalLinearTwoPowerSubspacePointSectionOver_comp_fst
    (s : baseFunctor k B hk ⟶ U.toFunctor)
    (hs : s ≫ U.ι = yoneda.map (generalLinearTwoPowerSitePoint k B hk m M)) :
    generalLinearTwoPowerSubspacePointSectionOver k B hk m C M U s hs ≫
        pullback.fst (pullback.fst (generalLinearTwoPowerToBase k B hk m)
          (toBaseFunctor k B hk C.toFunctor)) U.ι =
      generalLinearTwoPowerSubspacePointSection k B hk m C M :=
  pullback.lift_fst _ _ _

@[reassoc]
private theorem generalLinearTwoPowerSubspacePointSectionOver_comp_snd
    (s : baseFunctor k B hk ⟶ U.toFunctor)
    (hs : s ≫ U.ι = yoneda.map (generalLinearTwoPowerSitePoint k B hk m M)) :
    generalLinearTwoPowerSubspacePointSectionOver k B hk m C M U s hs ≫
        pullback.snd (pullback.fst (generalLinearTwoPowerToBase k B hk m)
          (toBaseFunctor k B hk C.toFunctor)) U.ι =
      toBaseFunctor k B hk C.toFunctor ≫ s :=
  pullback.lift_snd _ _ _

/-- **At a `k`-point `M` of the open subspace produced by the contraction step, the orbit map
`c ↦ f(M · c)` on `C` factors through an algebraic space finite over `Spec k`.**

The datum is exactly the conclusion of [Stacks, Tag 0AEJ] at the point `M`: a closed subspace `W`
of `((GL₂)^m × Z) ×_{(GL₂)^m} U` finite over `U`, through which the restriction of
`(g, c) ↦ (g, f(g · c))` factors. Its fibre over `M` is finite over `Spec k`, and the fibre of the
factorization over `M` is the orbit map, by
`AlgebraicGeometry.Space.comp_generalLinearTwoPowerOrbitGraph_comp_snd_of_comp_fst_eq`. -/
theorem exists_isFinite_comp_eq_orbitMap
    (s : baseFunctor k B hk ⟶ U.toFunctor)
    (hs : s ≫ U.ι = yoneda.map (generalLinearTwoPowerSitePoint k B hk m M))
    (W : Subfunctor (pullback (pullback.fst (generalLinearTwoPowerToBase k B hk m) z) U.ι))
    (r : pullback (pullback.fst (generalLinearTwoPowerToBase k B hk m)
        (toBaseFunctor k B hk C.toFunctor)) U.ι ⟶ W.toFunctor)
    (hr : r ≫ W.ι =
      pullback.map
        (pullback.fst (generalLinearTwoPowerToBase k B hk m)
          (toBaseFunctor k B hk C.toFunctor)) U.ι
        (pullback.fst (generalLinearTwoPowerToBase k B hk m) z) U.ι
        (generalLinearTwoPowerOrbitGraph k B hk m z f C) (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id, generalLinearTwoPowerOrbitGraph_comp_fst]) (by simp))
    (hfin : IsFinite B (Spec (CommRingCat.of k)) hk
      (W.ι ≫ pullback.snd (pullback.fst (generalLinearTwoPowerToBase k B hk m) z) U.ι)) :
    ∃ (F : (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤ Type u)
      (q : F ⟶ baseFunctor k B hk) (i : F ⟶ Z) (t : C.toFunctor ⟶ F),
      IsFinite B (Spec (CommRingCat.of k)) hk q ∧
        C.ι ≫ (projectiveLinePowerFunctorMatrixAut k B hk m M).hom ≫ f = t ≫ i := by
  have hsnd : (generalLinearTwoPowerSubspacePointSectionOver k B hk m C M U s hs ≫ r) ≫
      W.ι ≫ pullback.snd (pullback.fst (generalLinearTwoPowerToBase k B hk m) z) U.ι =
    toBaseFunctor k B hk C.toFunctor ≫ s := by
    rw [Category.assoc, ← Category.assoc r W.ι, hr, pullback.lift_snd, Category.comp_id]
    exact generalLinearTwoPowerSubspacePointSectionOver_comp_snd k B hk m C M U s hs
  refine ⟨pullback (W.ι ≫ pullback.snd
      (pullback.fst (generalLinearTwoPowerToBase k B hk m) z) U.ι) s,
    pullback.snd _ s,
    pullback.fst _ s ≫ W.ι ≫
      pullback.fst (pullback.fst (generalLinearTwoPowerToBase k B hk m) z) U.ι ≫
        pullback.snd (generalLinearTwoPowerToBase k B hk m) z,
    pullback.lift (generalLinearTwoPowerSubspacePointSectionOver k B hk m C M U s hs ≫ r)
      (toBaseFunctor k B hk C.toFunctor) hsnd,
    isFinite_pullback_snd B (Spec (CommRingCat.of k)) hk _ s hfin, ?_⟩
  symm
  rw [pullback.lift_fst_assoc]
  simp only [Category.assoc]
  rw [← Category.assoc r W.ι, hr]
  rw [pullback.lift_fst_assoc]
  simp only [Category.assoc]
  rw [generalLinearTwoPowerSubspacePointSectionOver_comp_fst_assoc,
    comp_generalLinearTwoPowerOrbitGraph_comp_snd_of_comp_fst_eq k B hk m z f C
      (generalLinearTwoPowerSubspacePointSection k B hk m C M) M
      (generalLinearTwoPowerSubspacePointSection_comp_fst k B hk m C M),
    generalLinearTwoPowerSubspacePointSection_comp_snd_assoc]

end Point

/-- **The contraction step of [Stacks, Tag 0AEM], in the form its induction consumes.**

Let `Z` be an algebraic space over `k`, separated and locally of finite type over `Spec k`, let
`f : (ℙ¹_k)^m ⟶ Z`, and let `C` be a closed subspace of `(ℙ¹_k)^m` which `f` carries to a single
point `ζ` of `Z`. Then there is an open subspace `U ⊆ (GL₂)^m` whose point set contains the
`k`-point given by the `m`-tuple of identity matrices, such that for *every* `k`-point `M` of
`(GL₂)^m` factoring through `U` the orbit map

```
C ↪ (ℙ¹_k)^m --M·--> (ℙ¹_k)^m --f--> Z
```

factors through an algebraic space finite over `Spec k`.

This is the source's "`g(C)` is mapped to a point for `g ∈ G(k)` lying in a Zariski open
`U ⊂ G`", with "a point" read as what [Stacks, Tag 0AEJ] actually delivers: a closed subspace
finite over the base. -/
theorem exists_isOpenSubspace_forall_isFinite_comp_eq_orbitMap
    (hZ : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk Z)
    (hz_sep : IsSeparated B (Spec (CommRingCat.of k)) hk z)
    (hz_lft : IsLocallyOfFiniteType B (Spec (CommRingCat.of k)) hk z)
    (hC : IsClosedSubspace B (Spec (CommRingCat.of k)) hk C)
    (hconst : C.ι ≫ f = toBaseFunctor k B hk C.toFunctor ≫ ζ) :
    ∃ U : Subfunctor (generalLinearTwoPowerFunctor k B hk m),
      IsOpenSubspace B (Spec (CommRingCat.of k)) hk U ∧
      (generalLinearTwoPowerFieldValuedPoint k B hk m 1).class B (Spec (CommRingCat.of k)) hk
          (generalLinearTwoPowerFunctor k B hk m) ∈
        Set.range (pointsMap B (Spec (CommRingCat.of k)) hk U.toFunctor U.ι) ∧
      ∀ (M : Fin m → Matrix.GeneralLinearGroup (Fin 2) k)
          (s : baseFunctor k B hk ⟶ U.toFunctor),
        s ≫ U.ι = yoneda.map (generalLinearTwoPowerSitePoint k B hk m M) →
        ∃ (F : (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤ Type u)
          (q : F ⟶ baseFunctor k B hk) (i : F ⟶ Z) (t : C.toFunctor ⟶ F),
          IsFinite B (Spec (CommRingCat.of k)) hk q ∧
            C.ι ≫ (projectiveLinePowerFunctorMatrixAut k B hk m M).hom ≫ f = t ≫ i := by
  obtain ⟨U, hU, hb, W, hW, ⟨r, hr⟩, hfin⟩ :=
    exists_isOpenSubspace_isFinite_generalLinearTwoPowerOrbitGraph k B hk m z f C ζ hZ hz_sep
      hz_lft hC hconst
  exact ⟨U, hU, hb, fun M s hs ↦
    exists_isFinite_comp_eq_orbitMap k B hk m z f C M U s hs W r hr hfin⟩

end Apply

end Contraction

end AlgebraicGeometry.Space

end
