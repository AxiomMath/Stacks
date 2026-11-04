module

public import Mathlib.GroupTheory.Perm.Sign
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.Complex
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenPointSetDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleZeroLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleStructureSheaf
public import StacksFrontier.CategoryTheory.Sites.CharacterTwist

/-!
# The complement of the diagonals in a self-product on the spaces-étale site

Let `f : U → X` be an étale and separated morphism of algebraic spaces over a scheme `S`.  For
`n ≥ 0` the `n`-fold self-product `U^n = U ×_X ⋯ ×_X U` is an object of the spaces-étale site
of `X`, the symmetric group `S_n` acts on it over `X` by permuting the factors, and the
complement `W` of all the diagonals is an open and closed subspace of `U^n` on which that
action is free.  With `n = p + 1` this is the space `W_p` of Stacks 0726, and the `(p+1)`-st
exterior power `K^p` of the extension by zero of `ℤ` from `U` receives a canonical map from the
sign twist `ℤ(sign)` of `W_p`, whence a map from `Hom(K^p, ℱ)` to the `S_{p+1}`-anti-invariant
sections of `ℱ` over `W_p`, functorially in `ℱ`.

## Main definitions

* `CategoryTheory.Limits.permProd` permutes the factors of an `n`-fold self-product in any
  category, and `CategoryTheory.Limits.permProdAut` is the resulting action of the symmetric
  group by automorphisms.
* `AlgebraicGeometry.Space.SpacesEtale.selfProd` is `U^n`, the `n`-fold self-product of an
  object of the spaces-étale site of `X`, and
  `AlgebraicGeometry.Space.SpacesEtale.prodTwo` is `U ×_X U`, with its diagonal
  `AlgebraicGeometry.Space.SpacesEtale.diagTwo` and the pairs of projections
  `AlgebraicGeometry.Space.SpacesEtale.projPair` of `U^n` onto it.
* `AlgebraicGeometry.Space.SpacesEtale.collisionPoints` is the locus in `U^n` where two
  prescribed factors agree and
  `AlgebraicGeometry.Space.SpacesEtale.diagonalComplementPoints` the complement of all of
  them.
* `AlgebraicGeometry.Space.SpacesEtale.diagonalComplement` is `W`, that complement read as an
  object of the spaces-étale site of `X`, with inclusion
  `AlgebraicGeometry.Space.SpacesEtale.diagonalComplementι` and the universal property
  `AlgebraicGeometry.Space.SpacesEtale.diagonalComplementLift`.
* `AlgebraicGeometry.Space.SpacesEtale.diagonalComplementAut` is the action of the symmetric
  group on `W` by permuting the factors.
* `AlgebraicGeometry.Space.SpacesEtale.signTwist` is the twist `ℤ(sign)` of the integers by the
  sign character of that action, and
  `AlgebraicGeometry.Space.SpacesEtale.signTwistToKoszul` is its canonical map to `K^p`.
* `AlgebraicGeometry.Space.SpacesEtale.koszulHomToSignSections` is the resulting map from
  `Hom(K^p, ℱ)` to the `S_{p+1}`-anti-invariant sections of `ℱ` over `W_p`.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.isOpen_diagonalComplementPoints` and
  `AlgebraicGeometry.Space.SpacesEtale.isClosed_diagonalComplementPoints`: `W` is open and
  closed in `U^n`, the first clause using separatedness of `f` and the second its étaleness.
* `AlgebraicGeometry.Space.SpacesEtale.eq_one_of_comp_diagonalComplementAut` and
  `AlgebraicGeometry.Space.SpacesEtale.isEmpty_points_of_comp_diagonalComplementAut` are
  **Stacks 0726**, first half: the action of `S_n` on `W` is free.
* `AlgebraicGeometry.Space.SpacesEtale.koszulHomToSignSections_naturality`: the map from
  `Hom(K^p, ℱ)` to the anti-invariant sections over `W_p` is functorial in `ℱ`.

## Implementation notes

The spaces-étale site has a final object and fibre products, hence all finite limits; its
final object is the identity of `X`, so products in it are fibre products over `X`, which is
what makes `AlgebraicGeometry.Space.SpacesEtale.selfProd` the self-product over `X` of the
source and makes the action of the symmetric group on it an action over `X`.

The locus where the factors of index `i` and `j` of `U^n` agree is defined as the preimage,
under the pair of projections `U^n ⟶ U ×_X U`, of the point set of the diagonal of `U ×_X U`.
That point set is open because every morphism of the spaces-étale site is étale, hence open on
points, and closed because `f` is separated: separatedness is by definition the statement that
the relative diagonal is a closed immersion, and a closed immersion has closed point set.  The
complement of the finitely many loci is therefore open and closed, and an open subspace of an
object of the site is again an object of the site.

Freeness of the action is stated in the shape it has on a site: a morphism `φ : V ⟶ W` fixed
by `σ` forces `σ = 1` unless the empty sieve covers `V`.  That escape is necessary — over an
object with no points, which the empty family covers, every group fixes every morphism — and
it is the clause `CategoryTheory.IsTorsorObject.eq_one_of_comp_act` of the site-theoretic
notion of a torsor.

The canonical map `ℤ(sign) ⟶ K^p` sends the class of a morphism `φ : V ⟶ W_p` to the wedge of
its `p + 1` components `V ⟶ U`; the relations imposed by the sign character are killed because
permuting the factors of `U^{p+1}` permutes those components and the wedge is alternating.
Stacks 0726 asserts moreover that the induced map from `Hom(K^p, ℱ)` to the anti-invariant
sections of `ℱ` over `W_p` is *bijective*, which is a computation on the stalks at the
geometric points of `X` and is not proved here; only the map and its functoriality in `ℱ` are.

Surjectivity of `f`, which Stacks 0726 also assumes, is not used here: it is what makes the
Koszul complex a resolution, not what makes `W` a space with a free action.

## References

* [Stacks Project, Tag 0726](https://stacks.math.columbia.edu/tag/0726)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] (U : C) (n : ℕ) [HasProduct fun _ : Fin n => U]

/-- The endomorphism of the `n`-fold self-product of an object permuting its factors: the
factor of index `i` of the image is the factor of index `σ⁻¹ i` of the argument. -/
def permProd (σ : Equiv.Perm (Fin n)) : (∏ᶜ fun _ : Fin n => U) ⟶ ∏ᶜ fun _ : Fin n => U :=
  Pi.lift fun i => Pi.π (fun _ : Fin n => U) (σ⁻¹ i)

/-- The factor of index `i` of `permProd U n σ` is the factor of index `σ⁻¹ i`. -/
@[simp]
theorem permProd_π (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permProd U n σ ≫ Pi.π (fun _ : Fin n => U) i = Pi.π (fun _ : Fin n => U) (σ⁻¹ i) :=
  Pi.lift_π _ i

/-- The identity permutation acts as the identity. -/
@[simp]
theorem permProd_one : permProd U n 1 = 𝟙 _ := by
  refine Pi.hom_ext _ _ fun i => ?_
  simp

/-- Permuting the factors by `σ` and then by `τ` permutes them by `τ * σ`. -/
theorem permProd_comp (σ τ : Equiv.Perm (Fin n)) :
    permProd U n σ ≫ permProd U n τ = permProd U n (τ * σ) := by
  refine Pi.hom_ext _ _ fun i => ?_
  rw [Category.assoc, permProd_π, permProd_π, permProd_π]
  congr 1

/-- The action of the symmetric group on `n` letters on the `n`-fold self-product of an object
by permuting the factors. -/
@[sga "3 VIIA 4.2" "partial", sga "3 VIIA 6.3" "partial"]
def permProdAut : Equiv.Perm (Fin n) →* Aut (∏ᶜ fun _ : Fin n => U) where
  toFun σ :=
    { hom := permProd U n σ
      inv := permProd U n σ⁻¹
      hom_inv_id := by rw [permProd_comp, inv_mul_cancel, permProd_one]
      inv_hom_id := by rw [permProd_comp, mul_inv_cancel, permProd_one] }
  map_one' := Iso.ext (permProd_one U n)
  map_mul' σ τ := Iso.ext (permProd_comp U n τ σ).symm

/-- The automorphism `permProdAut U n σ` has `permProd U n σ` as its underlying morphism. -/
@[simp]
theorem permProdAut_hom (σ : Equiv.Perm (Fin n)) :
    (permProdAut U n σ).hom = permProd U n σ :=
  rfl

end CategoryTheory.Limits

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- The image of a closed set of points under an isomorphism of presheaves on the big fppf
site of `S` is closed: an isomorphism induces a bijection on points whose inverse is
continuous. -/
theorem isClosed_image_pointsMap_of_iso {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G)
    {Z : Set (points B S hS F)} (hZ : IsClosed Z) :
    IsClosed (pointsMap B S hS F e.hom '' Z) := by
  have h₁ : Function.LeftInverse (pointsMap B S hS G e.inv) (pointsMap B S hS F e.hom) :=
    fun x => by rw [← pointsMap_comp_apply, e.hom_inv_id, pointsMap_id, id_eq]
  have h₂ : Function.RightInverse (pointsMap B S hS G e.inv) (pointsMap B S hS F e.hom) :=
    fun x => by rw [← pointsMap_comp_apply, e.inv_hom_id, pointsMap_id, id_eq]
  rw [Set.image_eq_preimage_of_inverse h₁ h₂]
  exact hZ.preimage (continuous_pointsMap B S hS e.inv)

/-- A morphism of presheaves on the big fppf site of `S` all of whose points land in a set `T`
of points of its target has image inside the subfunctor that `T` cuts out. -/
theorem range_le_openSubspaceOfPoints {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : G ⟶ F)
    (T : Set (points B S hS F)) (h : ∀ y, pointsMap B S hS G g y ∈ T) :
    Subfunctor.range g ≤ openSubspaceOfPoints B S hS F T := by
  rw [Subfunctor.le_def]
  rintro A z ⟨y, rfl⟩
  rw [mem_openSubspaceOfPoints_iff]
  have he : yonedaEquiv.symm (g.app A y) = yonedaEquiv.symm y ≫ g := by
    apply yonedaEquiv.injective
    rw [Equiv.apply_symm_apply, yonedaEquiv_comp, Equiv.apply_symm_apply]
  rw [he, pointsMap_comp]
  rintro w ⟨q, rfl⟩
  exact h _

namespace SpacesEtale

/-! ### Self-products on the spaces-étale site -/

/-- The spaces-étale site of `X` has finite limits: it has a final object and fibre
products. -/
instance hasFiniteLimits : HasFiniteLimits (SpacesEtale B S hS X) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- The compatibility of a morphism of the spaces-étale site of `X` with the structure
morphisms, read on presheaves. -/
theorem hom_toSpaces_map_comp_structure {V U : SpacesEtale B S hS X} (f : V ⟶ U) :
    ((toSpaces B S hS X).map f).hom ≫ U.1.hom.hom = V.1.hom.hom :=
  congrArg (fun k : underlying B S hS X V ⟶ X => k.hom)
    (toSpaces_map_comp_structure B S hS X f)

/-- The presheaf morphism underlying a composite of morphisms of the spaces-étale site of `X`
is the composite of the presheaf morphisms. -/
theorem hom_toSpaces_map_comp {V W Z : SpacesEtale B S hS X} (f : V ⟶ W) (g : W ⟶ Z) :
    ((toSpaces B S hS X).map (f ≫ g)).hom =
      ((toSpaces B S hS X).map f).hom ≫ ((toSpaces B S hS X).map g).hom := by
  rw [CategoryTheory.Functor.map_comp]
  simp

/-- The map on points of a composite of morphisms of the spaces-étale site of `X`. -/
theorem pointsMap_toSpaces_map_comp {V W Z : SpacesEtale B S hS X} (f : V ⟶ W) (g : W ⟶ Z)
    (y : points B S hS (underlying B S hS X V).1) :
    pointsMap B S hS (underlying B S hS X V).1 ((toSpaces B S hS X).map (f ≫ g)).hom y =
      pointsMap B S hS (underlying B S hS X W).1 ((toSpaces B S hS X).map g).hom
        (pointsMap B S hS (underlying B S hS X V).1 ((toSpaces B S hS X).map f).hom y) := by
  rw [hom_toSpaces_map_comp, pointsMap_comp_apply]

/-- The morphism of algebraic spaces underlying the unique morphism to the final object of the
spaces-étale site of `X` is the structure morphism: the final object is the identity of `X`. -/
theorem toSpaces_map_to_final (U : SpacesEtale B S hS X) (t : U ⟶ final B S hS X) :
    (toSpaces B S hS X).map t = U.1.hom :=
  (Category.comp_id _).symm.trans (Over.w ((inclusion B S hS X).map t))

/-- The `n`-fold self-product `U^n = U ×_X ⋯ ×_X U` of an object of the spaces-étale site of
`X`: products in that site are fibre products over `X`, because the identity of `X` is its
final object. -/
abbrev selfProd (U : SpacesEtale B S hS X) (n : ℕ) : SpacesEtale B S hS X :=
  ∏ᶜ fun _ : Fin n => U

/-- The fibre square `U ×_X U` of an object of the spaces-étale site of `X`, as the fibre
product over the final object of that site. -/
abbrev prodTwo (U : SpacesEtale B S hS X) : SpacesEtale B S hS X :=
  pullback (toFinal B S hS U) (toFinal B S hS U)

/-- The diagonal `U ⟶ U ×_X U`. -/
def diagTwo (U : SpacesEtale B S hS X) : U ⟶ prodTwo B S hS X U :=
  pullback.lift (𝟙 U) (𝟙 U) rfl

/-- The diagonal followed by the first projection of `U ×_X U` is the identity. -/
@[simp]
theorem diagTwo_comp_fst (U : SpacesEtale B S hS X) :
    diagTwo B S hS X U ≫ pullback.fst (toFinal B S hS U) (toFinal B S hS U) = 𝟙 U :=
  pullback.lift_fst _ _ _

/-- The diagonal followed by the second projection of `U ×_X U` is the identity. -/
@[simp]
theorem diagTwo_comp_snd (U : SpacesEtale B S hS X) :
    diagTwo B S hS X U ≫ pullback.snd (toFinal B S hS U) (toFinal B S hS U) = 𝟙 U :=
  pullback.lift_snd _ _ _

/-- The pair of projections `(π i, π j) : U^n ⟶ U ×_X U` onto the factors of index `i` and
`j`. -/
def projPair (U : SpacesEtale B S hS X) (n : ℕ) (i j : Fin n) :
    selfProd B S hS X U n ⟶ prodTwo B S hS X U :=
  pullback.lift (Pi.π (fun _ : Fin n => U) i) (Pi.π (fun _ : Fin n => U) j)
    ((final_isTerminal B S hS X).hom_ext _ _)

/-- The first component of `projPair U n i j` is the projection onto the factor of index `i`. -/
@[simp]
theorem projPair_comp_fst (U : SpacesEtale B S hS X) (n : ℕ) (i j : Fin n) :
    projPair B S hS X U n i j ≫ pullback.fst (toFinal B S hS U) (toFinal B S hS U) =
      Pi.π (fun _ : Fin n => U) i :=
  pullback.lift_fst _ _ _

/-- The second component of `projPair U n i j` is the projection onto the factor of index `j`. -/
@[simp]
theorem projPair_comp_snd (U : SpacesEtale B S hS X) (n : ℕ) (i j : Fin n) :
    projPair B S hS X U n i j ≫ pullback.snd (toFinal B S hS U) (toFinal B S hS U) =
      Pi.π (fun _ : Fin n => U) j :=
  pullback.lift_snd _ _ _

/-- Permuting the factors of `U^n` by `σ` and then projecting onto the factors of index `i`
and `j` is projecting onto the factors of index `σ⁻¹ i` and `σ⁻¹ j`. -/
theorem permProd_comp_projPair (U : SpacesEtale B S hS X) (n : ℕ) (σ : Equiv.Perm (Fin n))
    (i j : Fin n) :
    permProd U n σ ≫ projPair B S hS X U n i j =
      projPair B S hS X U n (σ⁻¹ i) (σ⁻¹ j) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, projPair_comp_fst, projPair_comp_fst, permProd_π]
  · rw [Category.assoc, projPair_comp_snd, projPair_comp_snd, permProd_π]

/-- A morphism into `U^n` whose two prescribed components agree factors through the diagonal of
`U ×_X U`. -/
theorem comp_projPair_eq (U : SpacesEtale B S hS X) (n : ℕ) {V : SpacesEtale B S hS X}
    (ψ : V ⟶ selfProd B S hS X U n) (i j : Fin n)
    (h : ψ ≫ Pi.π (fun _ : Fin n => U) i = ψ ≫ Pi.π (fun _ : Fin n => U) j) :
    ψ ≫ projPair B S hS X U n i j =
      (ψ ≫ Pi.π (fun _ : Fin n => U) i) ≫ diagTwo B S hS X U := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, projPair_comp_fst, Category.assoc, diagTwo_comp_fst, Category.comp_id]
  · rw [Category.assoc, projPair_comp_snd, Category.assoc, diagTwo_comp_snd, Category.comp_id]
    exact h.symm

/-! ### The point set of the diagonal of `U ×_X U` -/

/-- The fibre square `U ×_X U` of an object of the spaces-étale site of `X`, as the chosen
fibre product of algebraic spaces over `S`. -/
abbrev fibreSquare (U : SpacesEtale B S hS X) : AlgebraicSpaces B S hS :=
  AlgebraicSpaces.fiberProduct B S hS U.1.hom U.1.hom

/-- The relative diagonal of the structure morphism of an object of the spaces-étale site of
`X`, read as a morphism of algebraic spaces over `S` into the chosen fibre square. -/
def diagMk (U : SpacesEtale B S hS X) :
    underlying B S hS X U ⟶ fibreSquare B S hS X U :=
  ObjectProperty.homMk (pullback.diagonal U.1.hom.hom)

/-- The relative diagonal followed by the first projection of the fibre square is the
identity. -/
@[simp]
theorem diagMk_comp_fst (U : SpacesEtale B S hS X) :
    diagMk B S hS X U ≫ (ObjectProperty.homMk (pullback.fst U.1.hom.hom U.1.hom.hom) :
      fibreSquare B S hS X U ⟶ underlying B S hS X U) = 𝟙 _ :=
  ObjectProperty.hom_ext _ (pullback.diagonal_fst U.1.hom.hom)

/-- The relative diagonal followed by the second projection of the fibre square is the
identity. -/
@[simp]
theorem diagMk_comp_snd (U : SpacesEtale B S hS X) :
    diagMk B S hS X U ≫ (ObjectProperty.homMk (pullback.snd U.1.hom.hom U.1.hom.hom) :
      fibreSquare B S hS X U ⟶ underlying B S hS X U) = 𝟙 _ :=
  ObjectProperty.hom_ext _ (pullback.diagonal_snd U.1.hom.hom)

/-- The algebraic space underlying `U ×_X U` is the fibre product over `X` of the algebraic
space underlying `U` with itself: the inclusion of the spaces-étale site of `X` into the slice
over `X` and the forgetful functor of that slice both preserve fibre products, and the final
object of the site is the identity of `X`. -/
theorem isPullback_toSpaces_prodTwo (U : SpacesEtale B S hS X) :
    IsPullback ((toSpaces B S hS X).map
        (pullback.fst (toFinal B S hS U) (toFinal B S hS U)))
      ((toSpaces B S hS X).map (pullback.snd (toFinal B S hS U) (toFinal B S hS U)))
      U.1.hom U.1.hom := by
  have h := (IsPullback.of_hasPullback (toFinal B S hS U)
    (toFinal B S hS U)).map (toSpaces B S hS X)
  rw [toSpaces_map_to_final] at h
  exact h

/-- The comparison isomorphism between the chosen fibre square of the structure morphism of
`U` and the algebraic space underlying `U ×_X U`. -/
abbrev fibreSquareIso (U : SpacesEtale B S hS X) :
    fibreSquare B S hS X U ≅ underlying B S hS X (prodTwo B S hS X U) :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS U.1.hom U.1.hom).isoIsPullback
    _ _ (isPullback_toSpaces_prodTwo B S hS X U)

/-- The diagonal of `U ×_X U` is the relative diagonal of the structure morphism of `U`,
transported along the comparison isomorphism of the two fibre squares. -/
theorem toSpaces_map_diagTwo (U : SpacesEtale B S hS X) :
    (toSpaces B S hS X).map (diagTwo B S hS X U) =
      diagMk B S hS X U ≫ (fibreSquareIso B S hS X U).hom := by
  have hsq := isPullback_toSpaces_prodTwo B S hS X U
  have hfp := AlgebraicSpaces.isPullback_fiberProduct B S hS U.1.hom U.1.hom
  refine hsq.hom_ext ?_ ?_
  · rw [Category.assoc, hfp.isoIsPullback_hom_fst, ← Functor.map_comp, diagTwo_comp_fst,
      CategoryTheory.Functor.map_id]
    exact (diagMk_comp_fst B S hS X U).symm
  · rw [Category.assoc, hfp.isoIsPullback_hom_snd, ← Functor.map_comp, diagTwo_comp_snd,
      CategoryTheory.Functor.map_id]
    exact (diagMk_comp_snd B S hS X U).symm

/-- **Stacks 06CR and 05W1 on points.** The point set of the diagonal of `U ×_X U` is open:
the diagonal is a morphism of the spaces-étale site of `X`, hence étale, hence open on
points. -/
theorem isOpen_range_pointsMap_diagTwo (U : SpacesEtale B S hS X) :
    IsOpen (Set.range (pointsMap B S hS (underlying B S hS X U).1
      ((toSpaces B S hS X).map (diagTwo B S hS X U)).hom)) := by
  rw [← Set.image_univ]
  exact isOpenMap_pointsMap_of_isEtale B S hS _ (underlying B S hS X U).2
    (underlying B S hS X (prodTwo B S hS X U)).2
    (isEtale_toSpaces_map B S hS X (diagTwo B S hS X U)) _ isOpen_univ

/-- The point set of the diagonal of `U ×_X U` is closed when the structure morphism of `U` is
separated: separatedness is the statement that the relative diagonal is a closed immersion, and
a closed immersion has closed point set by Stacks 04CD. -/
theorem isClosed_range_pointsMap_diagTwo (U : SpacesEtale B S hS X)
    (hsep : IsSeparated B S hS U.1.hom.hom) :
    IsClosed (Set.range (pointsMap B S hS (underlying B S hS X U).1
      ((toSpaces B S hS X).map (diagTwo B S hS X U)).hom)) := by
  have hcl := isClosed_range_pointsMap_of_isClosedImmersion B S hS (fibreSquare B S hS X U).2
    (pullback.diagonal U.1.hom.hom) hsep
  have hcomp : ((toSpaces B S hS X).map (diagTwo B S hS X U)).hom =
      pullback.diagonal U.1.hom.hom ≫ (fibreSquareIso B S hS X U).hom.hom :=
    congrArg (fun k => k.hom) (toSpaces_map_diagTwo B S hS X U)
  have h1 : pointsMap B S hS (underlying B S hS X U).1
        ((toSpaces B S hS X).map (diagTwo B S hS X U)).hom =
      pointsMap B S hS (fibreSquare B S hS X U).1 (fibreSquareIso B S hS X U).hom.hom ∘
        pointsMap B S hS (underlying B S hS X U).1 (pullback.diagonal U.1.hom.hom) :=
    (congrArg (fun k => pointsMap B S hS (underlying B S hS X U).1 k) hcomp).trans
      (pointsMap_comp B S hS (underlying B S hS X U).1 (pullback.diagonal U.1.hom.hom)
        (fibreSquareIso B S hS X U).hom.hom)
  rw [h1, Set.range_comp]
  exact isClosed_image_pointsMap_of_iso B S hS
    ((ObjectProperty.ι (IsAlgebraicSpace B S hS)).mapIso (fibreSquareIso B S hS X U)) hcl

/-! ### The complement of the diagonals -/

/-- The locus in `U^n` where the factors of index `i` and `j` agree: the preimage, under the
pair of projections to `U ×_X U`, of the point set of the diagonal. -/
def collisionPoints (U : SpacesEtale B S hS X) (n : ℕ) (i j : Fin n) :
    Set (points B S hS (underlying B S hS X (selfProd B S hS X U n)).1) :=
  pointsMap B S hS (underlying B S hS X (selfProd B S hS X U n)).1
      ((toSpaces B S hS X).map (projPair B S hS X U n i j)).hom ⁻¹'
    Set.range (pointsMap B S hS (underlying B S hS X U).1
      ((toSpaces B S hS X).map (diagTwo B S hS X U)).hom)

/-- A point of `V` is sent by `f : V ⟶ U^n` into the locus where two factors agree exactly when it
is sent by `f ≫ projPair U n i j` into the point set of the diagonal. -/
private theorem pointsMap_mem_collisionPoints_iff (U : SpacesEtale B S hS X) (n : ℕ)
    {V : SpacesEtale B S hS X} (f : V ⟶ selfProd B S hS X U n) (i j : Fin n)
    (y : points B S hS (underlying B S hS X V).1) :
    pointsMap B S hS (underlying B S hS X V).1 ((toSpaces B S hS X).map f).hom y ∈
        collisionPoints B S hS X U n i j ↔
      pointsMap B S hS (underlying B S hS X V).1
        ((toSpaces B S hS X).map (f ≫ projPair B S hS X U n i j)).hom y ∈
      Set.range (pointsMap B S hS (underlying B S hS X U).1
        ((toSpaces B S hS X).map (diagTwo B S hS X U)).hom) := by
  rw [pointsMap_toSpaces_map_comp]
  exact Iff.rfl

/-- The locus where two prescribed factors of `U^n` agree is open. -/
theorem isOpen_collisionPoints (U : SpacesEtale B S hS X) (n : ℕ) (i j : Fin n) :
    IsOpen (collisionPoints B S hS X U n i j) :=
  (isOpen_range_pointsMap_diagTwo B S hS X U).preimage (continuous_pointsMap B S hS _)

/-- The locus where two prescribed factors of `U^n` agree is closed when the structure
morphism of `U` is separated. -/
theorem isClosed_collisionPoints (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) (i j : Fin n) :
    IsClosed (collisionPoints B S hS X U n i j) :=
  (isClosed_range_pointsMap_diagTwo B S hS X U hsep).preimage (continuous_pointsMap B S hS _)

/-- The points of `U^n` avoiding all the diagonals: those at which no two factors of distinct
indices agree. -/
def diagonalComplementPoints (U : SpacesEtale B S hS X) (n : ℕ) :
    Set (points B S hS (underlying B S hS X (selfProd B S hS X U n)).1) :=
  ⋂ p : {p : Fin n × Fin n // p.1 ≠ p.2}, (collisionPoints B S hS X U n p.1.1 p.1.2)ᶜ

/-- A point of `U^n` avoids all the diagonals exactly when it avoids the locus where the
factors of index `i` and `j` agree for every pair of distinct indices. -/
theorem mem_diagonalComplementPoints_iff (U : SpacesEtale B S hS X) (n : ℕ)
    (x : points B S hS (underlying B S hS X (selfProd B S hS X U n)).1) :
    x ∈ diagonalComplementPoints B S hS X U n ↔
      ∀ i j : Fin n, i ≠ j → x ∉ collisionPoints B S hS X U n i j := by
  simp only [diagonalComplementPoints, Set.mem_iInter, Set.mem_compl_iff]
  exact ⟨fun h i j hij => h ⟨(i, j), hij⟩, fun h p => h p.1.1 p.1.2 p.2⟩

/-- The complement of all the diagonals in `U^n` is open when the structure morphism of `U` is
separated: it is the intersection of the complements of finitely many closed loci. -/
theorem isOpen_diagonalComplementPoints (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) :
    IsOpen (diagonalComplementPoints B S hS X U n) :=
  isOpen_iInter_of_finite fun p =>
    (isClosed_collisionPoints B S hS X U n hsep p.1.1 p.1.2).isOpen_compl

/-- The complement of all the diagonals in `U^n` is closed: it is the intersection of the
complements of open loci. -/
theorem isClosed_diagonalComplementPoints (U : SpacesEtale B S hS X) (n : ℕ) :
    IsClosed (diagonalComplementPoints B S hS X U n) :=
  isClosed_iInter fun p => (isOpen_collisionPoints B S hS X U n p.1.1 p.1.2).isClosed_compl

/-- The complement of all the diagonals in `U^n`, as an open subspace of the algebraic space
underlying `U^n`. -/
def diagonalComplementSubspace (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) :
    {W : Subfunctor (underlying B S hS X (selfProd B S hS X U n)).1 //
      IsOpenSubspace B S hS W} :=
  ⟨openSubspaceOfPoints B S hS (underlying B S hS X (selfProd B S hS X U n)).1
      (diagonalComplementPoints B S hS X U n),
    isOpenSubspace_openSubspaceOfPoints B S hS
      (underlying B S hS X (selfProd B S hS X U n)).2 _
      (isOpen_diagonalComplementPoints B S hS X U n hsep)⟩

/-- **Stacks 0726.** The space `W = U ×_X ⋯ ×_X U ∖ (all diagonals)` with `n` factors, as an
object of the spaces-étale site of `X`: the complement of the diagonals is an open subspace of
`U^n`, and an open subspace of an object of the site is again one. -/
@[stacks 0726 "the space W_p"]
def diagonalComplement (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) : SpacesEtale B S hS X :=
  openSubspaceObject B S hS X (selfProd B S hS X U n)
    (diagonalComplementSubspace B S hS X U n hsep)

/-- The inclusion of `W` into `U^n`. -/
def diagonalComplementι (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) :
    diagonalComplement B S hS X U n hsep ⟶ selfProd B S hS X U n :=
  openSubspaceInclusion B S hS X (selfProd B S hS X U n)
    (diagonalComplementSubspace B S hS X U n hsep)

/-- The point set of `W` is the complement of all the diagonals in `U^n`. -/
theorem range_pointsMap_diagonalComplementι (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) :
    Set.range (pointsMap B S hS
        (underlying B S hS X (diagonalComplement B S hS X U n hsep)).1
        ((toSpaces B S hS X).map (diagonalComplementι B S hS X U n hsep)).hom) =
      diagonalComplementPoints B S hS X U n :=
  range_pointsMap_ι_openSubspaceOfPoints B S hS (diagonalComplementPoints B S hS X U n)

/-- Every point of `W` avoids all the diagonals of `U^n`. -/
theorem mem_diagonalComplementPoints_pointsMap_diagonalComplementι
    (U : SpacesEtale B S hS X) (n : ℕ) (hsep : IsSeparated B S hS U.1.hom.hom)
    (y : points B S hS (underlying B S hS X (diagonalComplement B S hS X U n hsep)).1) :
    pointsMap B S hS (underlying B S hS X (diagonalComplement B S hS X U n hsep)).1
        ((toSpaces B S hS X).map (diagonalComplementι B S hS X U n hsep)).hom y ∈
      diagonalComplementPoints B S hS X U n := by
  rw [← range_pointsMap_diagonalComplementι B S hS X U n hsep]
  exact ⟨y, rfl⟩

/-- Two morphisms into `W` agreeing after the inclusion into `U^n` are equal: the inclusion of
an open subspace is a monomorphism. -/
theorem diagonalComplement_hom_ext (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) {V : SpacesEtale B S hS X}
    {a b : V ⟶ diagonalComplement B S hS X U n hsep}
    (h : a ≫ diagonalComplementι B S hS X U n hsep =
      b ≫ diagonalComplementι B S hS X U n hsep) : a = b := by
  refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext (ObjectProperty.hom_ext _ ?_))
  refine (cancel_mono (diagonalComplementSubspace B S hS X U n hsep).1.ι).1 ?_
  exact congrArg (fun k => ((toSpaces B S hS X).map k).hom) h

/-- A morphism into `U^n` all of whose points avoid the diagonals has image inside the
subfunctor of `U^n` that `W` is. -/
theorem range_le_diagonalComplementSubspace (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) {V : SpacesEtale B S hS X}
    (f : V ⟶ selfProd B S hS X U n)
    (hf : ∀ y : points B S hS (underlying B S hS X V).1,
      pointsMap B S hS (underlying B S hS X V).1 ((toSpaces B S hS X).map f).hom y ∈
        diagonalComplementPoints B S hS X U n) :
    Subfunctor.range ((toSpaces B S hS X).map f).hom ≤
      (diagonalComplementSubspace B S hS X U n hsep).1 :=
  range_le_openSubspaceOfPoints B S hS ((toSpaces B S hS X).map f).hom
    (diagonalComplementPoints B S hS X U n) hf

/-- A morphism into `U^n` all of whose points avoid the diagonals factors through `W`; this is
the factorization. -/
def diagonalComplementLift (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) {V : SpacesEtale B S hS X}
    (f : V ⟶ selfProd B S hS X U n)
    (hf : ∀ y : points B S hS (underlying B S hS X V).1,
      pointsMap B S hS (underlying B S hS X V).1 ((toSpaces B S hS X).map f).hom y ∈
        diagonalComplementPoints B S hS X U n) :
    V ⟶ diagonalComplement B S hS X U n hsep :=
  have hle := range_le_diagonalComplementSubspace B S hS X U n hsep f hf
  ObjectProperty.homMk (Over.homMk
    (ObjectProperty.homMk (Subfunctor.lift ((toSpaces B S hS X).map f).hom hle))
    (ObjectProperty.hom_ext _ (by
      change Subfunctor.lift ((toSpaces B S hS X).map f).hom hle ≫
          ((diagonalComplementSubspace B S hS X U n hsep).1.ι ≫
            (selfProd B S hS X U n).1.hom.hom) = V.1.hom.hom
      rw [← Category.assoc, Subfunctor.lift_ι]
      exact hom_toSpaces_map_comp_structure B S hS X f)))

/-- The factorization `diagonalComplementLift` followed by the inclusion of `W` into `U^n` is the
original morphism. -/
@[simp]
theorem diagonalComplementLift_ι (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) {V : SpacesEtale B S hS X}
    (f : V ⟶ selfProd B S hS X U n)
    (hf : ∀ y : points B S hS (underlying B S hS X V).1,
      pointsMap B S hS (underlying B S hS X V).1 ((toSpaces B S hS X).map f).hom y ∈
        diagonalComplementPoints B S hS X U n) :
    diagonalComplementLift B S hS X U n hsep f hf ≫
      diagonalComplementι B S hS X U n hsep = f :=
  ObjectProperty.hom_ext _ (Over.OverMorphism.ext (ObjectProperty.hom_ext _
    (Subfunctor.lift_ι ((toSpaces B S hS X).map f).hom
      (range_le_diagonalComplementSubspace B S hS X U n hsep f hf))))

/-! ### The free action of the symmetric group on `W` -/

/-- Permuting the factors of `U^n` carries the complement of the diagonals into itself: a
permutation turns the locus where the factors of index `i` and `j` agree into the locus where
the factors of index `σ⁻¹ i` and `σ⁻¹ j` agree. -/
theorem diagonalComplementPoints_pointsMap_permProd (U : SpacesEtale B S hS X) (n : ℕ)
    (σ : Equiv.Perm (Fin n))
    {x : points B S hS (underlying B S hS X (selfProd B S hS X U n)).1}
    (hx : x ∈ diagonalComplementPoints B S hS X U n) :
    pointsMap B S hS (underlying B S hS X (selfProd B S hS X U n)).1
        ((toSpaces B S hS X).map (permProd U n σ)).hom x ∈
      diagonalComplementPoints B S hS X U n := by
  rw [mem_diagonalComplementPoints_iff]
  intro i j hij hmem
  refine (mem_diagonalComplementPoints_iff B S hS X U n x).1 hx (σ⁻¹ i) (σ⁻¹ j)
    (fun h => hij (by simpa using congrArg (fun k => σ k) h)) ?_
  rw [pointsMap_mem_collisionPoints_iff, permProd_comp_projPair] at hmem
  exact hmem

/-- The automorphism of `W` permuting the factors of `U^n` by `σ`. -/
def diagonalComplementPerm (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) (σ : Equiv.Perm (Fin n)) :
    diagonalComplement B S hS X U n hsep ⟶ diagonalComplement B S hS X U n hsep :=
  diagonalComplementLift B S hS X U n hsep
    (diagonalComplementι B S hS X U n hsep ≫ permProd U n σ) (by
      intro y
      rw [pointsMap_toSpaces_map_comp]
      exact diagonalComplementPoints_pointsMap_permProd B S hS X U n σ
        (mem_diagonalComplementPoints_pointsMap_diagonalComplementι B S hS X U n hsep y))

/-- Permuting `W` by `σ` and then including it into `U^n` is including it and then permuting the
factors of `U^n` by `σ`. -/
@[simp]
theorem diagonalComplementPerm_ι (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) (σ : Equiv.Perm (Fin n)) :
    diagonalComplementPerm B S hS X U n hsep σ ≫ diagonalComplementι B S hS X U n hsep =
      diagonalComplementι B S hS X U n hsep ≫ permProd U n σ :=
  diagonalComplementLift_ι B S hS X U n hsep _ _

/-- Permuting the factors of `W` by `σ` and then by `τ` permutes them by `τ * σ`. -/
theorem diagonalComplementPerm_comp (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) (σ τ : Equiv.Perm (Fin n)) :
    diagonalComplementPerm B S hS X U n hsep σ ≫
        diagonalComplementPerm B S hS X U n hsep τ =
      diagonalComplementPerm B S hS X U n hsep (τ * σ) := by
  refine diagonalComplement_hom_ext B S hS X U n hsep ?_
  rw [Category.assoc, diagonalComplementPerm_ι, ← Category.assoc, diagonalComplementPerm_ι,
    Category.assoc, permProd_comp, diagonalComplementPerm_ι]

/-- The identity permutation acts on `W` as the identity. -/
@[simp]
theorem diagonalComplementPerm_one (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) :
    diagonalComplementPerm B S hS X U n hsep 1 = 𝟙 _ := by
  refine diagonalComplement_hom_ext B S hS X U n hsep ?_
  rw [diagonalComplementPerm_ι, permProd_one, Category.comp_id, Category.id_comp]

/-- **Stacks 0726.** The action of the symmetric group on `n` letters on `W` by permuting the
factors of `U^n`.  It is an action over `X` because `W` and the permutations of the factors
live in the spaces-étale site of `X`. -/
@[stacks 0726 "the action of S_{p+1} on W_p over X"]
def diagonalComplementAut (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) :
    Equiv.Perm (Fin n) →* Aut (diagonalComplement B S hS X U n hsep) where
  toFun σ :=
    { hom := diagonalComplementPerm B S hS X U n hsep σ
      inv := diagonalComplementPerm B S hS X U n hsep σ⁻¹
      hom_inv_id := by
        rw [diagonalComplementPerm_comp, inv_mul_cancel, diagonalComplementPerm_one]
      inv_hom_id := by
        rw [diagonalComplementPerm_comp, mul_inv_cancel, diagonalComplementPerm_one] }
  map_one' := Iso.ext (diagonalComplementPerm_one B S hS X U n hsep)
  map_mul' σ τ := Iso.ext (diagonalComplementPerm_comp B S hS X U n hsep τ σ).symm

/-- The automorphism `diagonalComplementAut U n hsep σ` has `diagonalComplementPerm U n hsep σ`
as its underlying morphism. -/
@[simp]
theorem diagonalComplementAut_hom (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) (σ : Equiv.Perm (Fin n)) :
    (diagonalComplementAut B S hS X U n hsep σ).hom =
      diagonalComplementPerm B S hS X U n hsep σ :=
  rfl

/-- An arrow in the presieve attached to a family of morphisms of the spaces-étale site of `X`
exhibits an index of that family. -/
theorem nonempty_of_presieve₀ (V : SpacesEtale B S hS X) (E : PreZeroHypercover.{u + 1} V)
    {Y : SpacesEtale B S hS X} {g : Y ⟶ V} (hg : E.presieve₀ g) : Nonempty E.I₀ := by
  cases hg with
  | mk i => exact ⟨i⟩

/-- An object of the spaces-étale site of `X` with no points is covered by the empty family,
hence by the empty sieve. -/
theorem bot_mem_topology_of_isEmpty_points (V : SpacesEtale B S hS X)
    (hV : IsEmpty (points B S hS (underlying B S hS X V).1)) :
    (⊥ : Sieve V) ∈ topology B S hS X V := by
  let E : PreZeroHypercover.{u + 1} V :=
    ⟨PEmpty.{u + 2}, fun i => i.elim, fun i => i.elim⟩
  have hbot : Sieve.generate E.presieve₀ = ⊥ :=
    eq_bot_iff.2 fun _ _ ⟨_, _, _, hb, _⟩ =>
      (nonempty_of_presieve₀ B S hS X V E hb).elim fun i => i.elim
  rw [← hbot, Precoverage.mem_toGrothendieck_iff]
  exact Precoverage.Saturate.of V E.presieve₀
    ((mem_precoverage_iff B S hS X).2 ⟨E, rfl, fun x => hV.elim x⟩)

/-- Permuting `W` by `σ` and then projecting its inclusion into `U^n` to the factor of index `i`
is projecting to the factor of index `σ⁻¹ i`. -/
private theorem diagonalComplementPerm_comp_ι_π (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    diagonalComplementPerm B S hS X U n hsep σ ≫
        diagonalComplementι B S hS X U n hsep ≫ Pi.π (fun _ : Fin n => U) i =
      diagonalComplementι B S hS X U n hsep ≫ Pi.π (fun _ : Fin n => U) (σ⁻¹ i) := by
  rw [← Category.assoc, diagonalComplementPerm_ι, Category.assoc, permProd_π]

/-- **Stacks 0726.** The action of the symmetric group on `W` is free: an object of the site
carrying a morphism to `W` fixed by a permutation `σ ≠ 1` has no points.

Pick `i` with `σ⁻¹ i ≠ i`.  A point of `V` would give a point of `U^n` at which the factors of
index `i` and `σ⁻¹ i` agree, whereas the points of `W` avoid all the diagonals. -/
@[stacks 0726 "freeness of the action of S_{p+1} on W_p: a fixed morphism has empty source"]
theorem isEmpty_points_of_comp_diagonalComplementAut (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) {V : SpacesEtale B S hS X}
    (φ : V ⟶ diagonalComplement B S hS X U n hsep) (σ : Equiv.Perm (Fin n)) (hσ : σ ≠ 1)
    (hφ : φ ≫ (diagonalComplementAut B S hS X U n hsep σ).hom = φ) :
    IsEmpty (points B S hS (underlying B S hS X V).1) := by
  refine ⟨fun y => ?_⟩
  obtain ⟨i, hi⟩ : ∃ i : Fin n, σ⁻¹ i ≠ i := by
    by_contra hall
    exact hσ (inv_eq_one.1 (Equiv.ext fun i => not_ne_iff.1 (fun h => hall ⟨i, h⟩)))
  set ψ := φ ≫ diagonalComplementι B S hS X U n hsep with hψ
  have hπ : ψ ≫ Pi.π (fun _ : Fin n => U) i =
      ψ ≫ Pi.π (fun _ : Fin n => U) (σ⁻¹ i) := by
    rw [hψ, Category.assoc, Category.assoc,
      ← diagonalComplementPerm_comp_ι_π B S hS X U n hsep σ i, ← diagonalComplementAut_hom]
    exact ((congrArg (· ≫ diagonalComplementι B S hS X U n hsep ≫ Pi.π (fun _ : Fin n => U) i)
      hφ).symm).trans (Category.assoc _ _ _)
  have hmemW : pointsMap B S hS (underlying B S hS X V).1
      ((toSpaces B S hS X).map ψ).hom y ∈ diagonalComplementPoints B S hS X U n := by
    rw [hψ, pointsMap_toSpaces_map_comp]
    exact mem_diagonalComplementPoints_pointsMap_diagonalComplementι B S hS X U n hsep _
  refine (mem_diagonalComplementPoints_iff B S hS X U n _).1 hmemW i (σ⁻¹ i) (Ne.symm hi) ?_
  rw [pointsMap_mem_collisionPoints_iff, comp_projPair_eq B S hS X U n ψ i (σ⁻¹ i) hπ,
    pointsMap_toSpaces_map_comp]
  exact ⟨_, rfl⟩

/-- **Stacks 0726.** The action of the symmetric group on `W` is free, in the shape the
site-theoretic notion of a torsor asks for: a morphism `φ : V ⟶ W` fixed by `σ` forces `σ = 1`
unless the empty sieve covers `V`. -/
@[stacks 0726 "freeness of the action of S_{p+1} on W_p"]
theorem eq_one_of_comp_diagonalComplementAut (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) {V : SpacesEtale B S hS X}
    (φ : V ⟶ diagonalComplement B S hS X U n hsep) (σ : Equiv.Perm (Fin n))
    (hφ : φ ≫ (diagonalComplementAut B S hS X U n hsep σ).hom = φ) :
    (⊥ : Sieve V) ∈ topology B S hS X V ∨ σ = 1 := by
  by_cases hσ : σ = 1
  · exact Or.inr hσ
  exact Or.inl (bot_mem_topology_of_isEmpty_points B S hS X V
    (isEmpty_points_of_comp_diagonalComplementAut B S hS X U n hsep φ σ hσ hφ))

/-! ### The sign twist of `W` and its map to `K^p` -/

/-- The wedge `φ_0 ∧ ⋯ ∧ φ_{n-1}` of the `n` components `V ⟶ U` of a morphism `V ⟶ W`, an
element of the `n`-th exterior power of the free abelian group on the morphisms `V ⟶ U`. -/
def signTwistWedge (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) {V : SpacesEtale B S hS X}
    (φ : V ⟶ diagonalComplement B S hS X U n hsep) :
    ⋀[ℤ]^n (FreeAbelianGroup (V ⟶ U)) :=
  exteriorPower.ιMulti ℤ n fun i =>
    FreeAbelianGroup.of (φ ≫ diagonalComplementι B S hS X U n hsep ≫
      Pi.π (fun _ : Fin n => U) i)

/-- Translating a morphism `V ⟶ W` by `σ` permutes its components: the component of index `i`
of the translate is the component of index `σ⁻¹ i` of the original. -/
theorem comp_diagonalComplementAut_comp_π (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) {V : SpacesEtale B S hS X}
    (φ : V ⟶ diagonalComplement B S hS X U n hsep) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (φ ≫ (diagonalComplementAut B S hS X U n hsep σ).hom) ≫
        diagonalComplementι B S hS X U n hsep ≫ Pi.π (fun _ : Fin n => U) i =
      φ ≫ diagonalComplementι B S hS X U n hsep ≫ Pi.π (fun _ : Fin n => U) (σ⁻¹ i) := by
  rw [Category.assoc, diagonalComplementAut_hom, diagonalComplementPerm_comp_ι_π]

/-- Translating a morphism `V ⟶ W` by `σ` multiplies the wedge of its components by the sign
of `σ`: the wedge is alternating and translation permutes the components. -/
theorem signTwistWedge_comp_diagonalComplementAut (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) {V : SpacesEtale B S hS X}
    (φ : V ⟶ diagonalComplement B S hS X U n hsep) (σ : Equiv.Perm (Fin n)) :
    signTwistWedge B S hS X U n hsep
        (φ ≫ (diagonalComplementAut B S hS X U n hsep σ).hom) =
      ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • signTwistWedge B S hS X U n hsep φ := by
  have hfam : (fun i => FreeAbelianGroup.of
        ((φ ≫ (diagonalComplementAut B S hS X U n hsep σ).hom) ≫
          diagonalComplementι B S hS X U n hsep ≫ Pi.π (fun _ : Fin n => U) i)) =
      (fun i => FreeAbelianGroup.of (φ ≫ diagonalComplementι B S hS X U n hsep ≫
        Pi.π (fun _ : Fin n => U) i)) ∘ (σ⁻¹ : Equiv.Perm (Fin n)) :=
    funext fun i => congrArg FreeAbelianGroup.of
      (comp_diagonalComplementAut_comp_π B S hS X U n hsep φ σ i)
  have h := AlternatingMap.map_perm (exteriorPower.ιMulti ℤ n
      (M := FreeAbelianGroup (V ⟶ U)))
    (fun i => FreeAbelianGroup.of (φ ≫ diagonalComplementι B S hS X U n hsep ≫
      Pi.π (fun _ : Fin n => U) i)) σ⁻¹
  rw [Equiv.Perm.sign_inv] at h
  simp only [signTwistWedge]
  rw [hfam, h, Units.smul_def]

/-- The free abelian presheaf on `W` divided by the relations imposed by the sign character of
the action of the symmetric group: the presheaf whose sheafification is `ℤ(sign)`. -/
abbrev signTwistPresheaf (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) :
    (SpacesEtale B S hS X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  characterTwistPresheaf (diagonalComplement B S hS X U n hsep)
    (diagonalComplementAut B S hS X U n hsep) Equiv.Perm.sign

/-- The map from the sign-twisted free abelian presheaf on `W` to the `n`-th exterior power of
the free abelian presheaf on `U`, read on one object of the site: the class of a morphism
`V ⟶ W` goes to the wedge of its components. -/
def signTwistToExteriorPowerApp (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) (V : (SpacesEtale B S hS X)ᵒᵖ) :
    (signTwistPresheaf B S hS X U n hsep).obj V ⟶
      (AddCommGrpCat.presheafExteriorPower
        (freeAbelianRepresentablePresheaf B S hS X U) n).obj V :=
  AddCommGrpCat.ofHom (QuotientAddGroup.lift _
    (FreeAbelianGroup.lift fun φ : V.unop ⟶ diagonalComplement B S hS X U n hsep =>
      signTwistWedge B S hS X U n hsep φ) (by
      intro x hx
      refine (show characterRelations (diagonalComplement B S hS X U n hsep)
          (diagonalComplementAut B S hS X U n hsep) Equiv.Perm.sign V.unop ≤
          (FreeAbelianGroup.lift fun φ : V.unop ⟶ diagonalComplement B S hS X U n hsep =>
            signTwistWedge B S hS X U n hsep φ).ker from ?_) hx
      rw [characterRelations, AddSubgroup.closure_le]
      rintro y ⟨g, φ, rfl⟩
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, map_zsmul,
        FreeAbelianGroup.lift_apply_of, sub_eq_zero]
      exact signTwistWedge_comp_diagonalComplementAut B S hS X U n hsep φ g))

/-- `signTwistToExteriorPowerApp` sends the twisted generator of a morphism `V ⟶ W` to the wedge
of its components. -/
@[simp]
theorem signTwistToExteriorPowerApp_twistedGenerator (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) (V : (SpacesEtale B S hS X)ᵒᵖ)
    (φ : V.unop ⟶ diagonalComplement B S hS X U n hsep) :
    (signTwistToExteriorPowerApp B S hS X U n hsep V)
        (twistedGenerator (diagonalComplement B S hS X U n hsep)
          (diagonalComplementAut B S hS X U n hsep) Equiv.Perm.sign φ) =
      signTwistWedge B S hS X U n hsep φ :=
  FreeAbelianGroup.lift_apply_of _ _

/-- The map from the sign-twisted free abelian presheaf on `W` to the `n`-th exterior power of
the free abelian presheaf on `U`: the class of a morphism `V ⟶ W` goes to the wedge of its
components. -/
def signTwistToExteriorPower (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) :
    signTwistPresheaf B S hS X U n hsep ⟶
      AddCommGrpCat.presheafExteriorPower (freeAbelianRepresentablePresheaf B S hS X U) n where
  app := signTwistToExteriorPowerApp B S hS X U n hsep
  naturality := by
    intro V₁ V₂ m
    apply AddCommGrpCat.hom_ext
    refine characterRelations_hom_ext (diagonalComplement B S hS X U n hsep)
      (diagonalComplementAut B S hS X U n hsep) Equiv.Perm.sign _ _ fun φ => ?_
    change (signTwistToExteriorPowerApp B S hS X U n hsep V₂)
        (twistedGenerator (diagonalComplement B S hS X U n hsep)
          (diagonalComplementAut B S hS X U n hsep) Equiv.Perm.sign (m.unop ≫ φ)) =
      (AddCommGrpCat.presheafExteriorPower
          (freeAbelianRepresentablePresheaf B S hS X U) n).map m
        ((signTwistToExteriorPowerApp B S hS X U n hsep V₁)
          (twistedGenerator (diagonalComplement B S hS X U n hsep)
            (diagonalComplementAut B S hS X U n hsep) Equiv.Perm.sign φ))
    rw [signTwistToExteriorPowerApp_twistedGenerator,
      signTwistToExteriorPowerApp_twistedGenerator]
    change signTwistWedge B S hS X U n hsep (m.unop ≫ φ) =
      exteriorPower.map n
        ((freeAbelianRepresentablePresheaf B S hS X U).map m).hom.toIntLinearMap
        (signTwistWedge B S hS X U n hsep φ)
    simp only [signTwistWedge]
    refine Eq.trans ?_ (exteriorPower.map_apply_ιMulti
      ((freeAbelianRepresentablePresheaf B S hS X U).map m).hom.toIntLinearMap
      (fun i => FreeAbelianGroup.of (φ ≫ diagonalComplementι B S hS X U n hsep ≫
        Pi.π (fun _ : Fin n => U) i))).symm
    congr 1

/-- The sheaf `ℤ(sign)` on the spaces-étale site of `X`: the twist of the integers by the sign
character of the action of the symmetric group on `W`. -/
abbrev signTwist (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) :
    Sheaf (topology B S hS X) AddCommGrpCat.{u + 1} :=
  characterTwist (diagonalComplement B S hS X U n hsep)
    (diagonalComplementAut B S hS X U n hsep) Equiv.Perm.sign (topology B S hS X)

/-- **Stacks 0726.** The canonical map `ℤ(sign) ⟶ K^p` from the sign twist of `W_p` to the
`(p+1)`-st exterior power of the extension by zero of `ℤ` from `U`: the sheafification of the
map sending the class of a morphism `V ⟶ W_p` to the wedge of its `p + 1` components. -/
@[stacks 0726 "the canonical map ℤ(sign) ⟶ K^p"]
def signTwistToKoszul (U : SpacesEtale B S hS X) (p : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) :
    signTwist B S hS X U (p + 1) hsep ⟶ (koszulComplex B S hS X U).X p :=
  (presheafToSheaf (topology B S hS X) AddCommGrpCat.{u + 1}).map
    (signTwistToExteriorPower B S hS X U (p + 1) hsep)

/-- **Stacks 0726.** The canonical map from `Hom(K^p, ℱ)` to the `S_{p+1}`-anti-invariant
sections of `ℱ` over `W_p`: precompose with `ℤ(sign) ⟶ K^p` and use that a map out of
`ℤ(sign)` is the same thing as an anti-invariant section over `W_p`.

Stacks 0726 asserts in addition that this map is bijective, which is not proved here. -/
@[stacks 0726 "the map Hom(K^p, F) ⟶ S_{p+1}-anti-invariant sections of F over W_p"]
def koszulHomToSignSections (U : SpacesEtale B S hS X) (p : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    AddCommGrpCat.of ((koszulComplex B S hS X U).X p ⟶ F) ⟶
      AddCommGrpCat.of (characterSections (diagonalComplement B S hS X U (p + 1) hsep)
        (diagonalComplementAut B S hS X U (p + 1) hsep) Equiv.Perm.sign F.obj) :=
  AddCommGrpCat.ofHom (AddMonoidHom.mk'
    (fun g => characterTwistHomEquiv (diagonalComplement B S hS X U (p + 1) hsep)
      (diagonalComplementAut B S hS X U (p + 1) hsep) Equiv.Perm.sign (topology B S hS X) F
      (signTwistToKoszul B S hS X U p hsep ≫ g)) (by
        intro g₁ g₂
        refine Subtype.ext ?_
        simp only [AddSubgroup.coe_add, characterTwistHomEquiv_apply, Preadditive.comp_add]
        rfl))

/-- **Stacks 0726.** The map from `Hom(K^p, ℱ)` to the `S_{p+1}`-anti-invariant sections of `ℱ`
over `W_p` is functorial in `ℱ`: composing a map `K^p ⟶ ℱ` with `ℱ ⟶ ℱ'` takes the
corresponding section to its image over `W_p`. -/
@[stacks 0726 "functoriality in F of the map Hom(K^p, F) ⟶ anti-invariant sections"]
theorem koszulHomToSignSections_naturality (U : SpacesEtale B S hS X) (p : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom)
    {F F' : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}} (k : F ⟶ F')
    (g : (koszulComplex B S hS X U).X p ⟶ F) :
    (((koszulHomToSignSections B S hS X U p hsep F').hom (g ≫ k)).1 :
        F'.obj.obj (op (diagonalComplement B S hS X U (p + 1) hsep))) =
      k.hom.app (op (diagonalComplement B S hS X U (p + 1) hsep))
        (((koszulHomToSignSections B S hS X U p hsep F).hom g).1) := by
  have h := characterTwistHomEquiv_comp (diagonalComplement B S hS X U (p + 1) hsep)
    (diagonalComplementAut B S hS X U (p + 1) hsep) Equiv.Perm.sign (topology B S hS X)
    (signTwistToKoszul B S hS X U p hsep ≫ g) k
  rw [Category.assoc] at h
  exact h

end SpacesEtale

end AlgebraicGeometry.Space

end
