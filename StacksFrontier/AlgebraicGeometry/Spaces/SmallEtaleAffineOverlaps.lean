module

public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement
public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineCoproductDecomposition
public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineFamilyAlgebraTower
public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineFppfFaithfullyFlat

/-!
# The affine overlaps of a covering family of étale charts, and the rings between them

Descent along a covering family `{g i : Y i ⟶ T}` of a slice of the small étale site of an
algebraic space consumes, besides the family itself, the double overlaps `Y i ×_T Y j` and the
triple overlaps `Y i ×_T (Y j ×_T Y k)` with their projections, and then four layers of rings: the
ring of global functions on the scheme underlying the object covered, the rings of the members,
and the rings of the two kinds of overlap, together with the maps between them.

This file produces all of that for the small étale site, and records the two facts about the rings
which flat descent along the family needs: the ring of an overlap is the tensor product of the
rings of the two factors, and the product of the rings of the members is faithfully flat over the
ring of the base.

The deep algebra is untouched: a fibre product square of affine schemes is a pushout square of
their rings of global functions
(`AlgebraicGeometry.algEquivTensorAppTopOfIsPullback`), and a finite jointly surjective family of
flat morphisms of affine schemes gives a faithfully flat product of rings
(`AlgebraicGeometry.faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage`).  Both are stated
for schemes and are used here unchanged; what the file supplies is the passage from a fibre
product square of a slice of the small étale site to one of schemes, which is where the site
enters.

## Main definitions

* `AlgebraicGeometry.Space.SmallEtale.sectionRingEquivGamma`: the ring of sections of the
  coefficient sheaf of rings of a slice of the small étale ringed site, identified with the
  commutative ring of global functions on the underlying scheme.
* `AlgebraicGeometry.Space.SmallEtale.sectionsEquivFinsuppOfIsAffine`,
  `AlgebraicGeometry.Space.SmallEtale.tautBasisOfIsAffine` and
  `AlgebraicGeometry.Space.SmallEtale.tautBasisOfIsAffineCoeffs`: **the sections of a coproduct of
  copies of the structure sheaf over an object of a slice whose underlying scheme is affine are
  the finitely supported families of sections of the structure sheaf**, read as an equivalence, as
  a basis, and as a basis over a commutative ring identified with the ring of sections.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.isPullback_toScheme_of_isPullback`: a fibre product square
  of a slice of the small étale site is a fibre product square of the underlying schemes.
* `AlgebraicGeometry.Space.SmallEtale.isAffine_of_isPullback`: **the fibre product of two objects
  of a slice with affine underlying scheme over one with affine underlying scheme again has affine
  underlying scheme.**
* `AlgebraicGeometry.Space.SmallEtale.exists_affine_family_overlaps`: **a family of objects of a
  slice with affine underlying scheme over one with affine underlying scheme has affine double and
  triple overlaps**, with the five families of projections, the diagonals, the two fibre product
  squares and the three commutations a family descent datum consumes.
* `AlgebraicGeometry.Space.SmallEtale.appTopGamma_comp_apply`,
  `AlgebraicGeometry.Space.SmallEtale.appTopGamma_id_apply` and
  `AlgebraicGeometry.Space.SmallEtale.appTopGamma_comp_apply_of_eq`: **the global functions on the
  schemes underlying the étale charts of `F` are a contravariant functor of the charts.**
* `AlgebraicGeometry.Space.SmallEtale.restrictₛₗ_smul_appTopGamma`: **restriction of sections along
  a morphism of the slice is semilinear along the induced map of global functions.**
* `AlgebraicGeometry.Space.SmallEtale.isScalarTower_appTopGamma`: **a factorisation of a morphism
  of the slice makes a scalar tower on the sections at its source.**
* `AlgebraicGeometry.Space.SmallEtale.exists_ringEquivTensorGamma_of_isPullback`: **the ring of
  global functions on a fibre product of two affine objects of a slice over an affine object is
  the tensor product of the rings of the two factors.**
* `AlgebraicGeometry.Space.SmallEtale.faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage`:
  **the product of the rings of the members of a finite flat covering family of affine objects is
  faithfully flat over the ring of the object covered.**

## Implementation notes

A fibre product square of `CategoryTheory.Over V` is carried to the underlying schemes by three
functors which all preserve fibre products: the forgetful functor of the slice, the projection of
an étale chart to the object of the big fppf site of `S` underlying it
(`AlgebraicGeometry.Space.SmallEtale.instPreservesPullbacksToOver`) and the projection of the big
fppf site to schemes.  No fibredness hypothesis appears, in contrast to
`AlgebraicGeometry.FibredSite.isPullback_toScheme_of_isPullback`: for the small étale site the
preservation is an instance of the site itself.

The module structures over the rings of global functions are instance arguments together with
hypotheses identifying their action with that of the ring of sections of the coefficient sheaf of
rings, which are the same ring by
`AlgebraicGeometry.Space.SmallEtale.ringSheaf_over_obj_obj`; for the structures a consumer
naturally has — `inferInstanceAs` at an object and `Module.compHom` along an induced map at an
object over it — the hypotheses are `fun _ _ => rfl`.  No instance is created, and no statement
here presupposes which of the two structures the caller has chosen.  This is the convention of
`AlgebraicGeometry.FibredSite.restrictₛₗ_smul_appTopGamma` and is what lets a consumer which
already holds a scalar tower over the ring of sections at the object covered use these statements
without rebuilding it.

Two spellings of the objects of the small étale site occur, and the choice is forced in each case.
The purely geometric statements, and the two about the rings of global functions, take a chart of
`AlgebraicGeometry.Space.SmallEtale`, which is what makes the fibre products and the
preservation instances of that site available; the statements mentioning the structure sheaf take
an object of the underlying category of `AlgebraicGeometry.Space.smallEtaleRingedSite`, which is
the same type behind a structure projection and is what the sheaf is indexed by.  The two are
definitionally equal, so a consumer holding the second applies a statement about the first; what
does *not* work is rewriting with such a statement inside a goal phrased in the second spelling,
since the rewrite is type-checked at a transparency which does not unfold the projection.  Hence
`AlgebraicGeometry.Space.SmallEtale.appTopGamma_comp_apply_of_eq` is applied as a term and not by
`rw` in the proof of `AlgebraicGeometry.Space.SmallEtale.isScalarTower_appTopGamma`.

The three statements about the global functions are about morphisms of charts and not of a slice:
a morphism of a slice is a morphism of charts, and `CategoryTheory.Over.comp_left` identifies a
composite in a slice with the composite of the underlying morphisms, so a consumer working in a
slice applies them to the underlying morphisms.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0D05](https://stacks.math.columbia.edu/tag/0D05)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe z r t u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

namespace SmallEtale

/-! ### Fibre products in a slice, and affineness of the overlaps -/

/-- **A fibre product square of a slice of the small étale site is a fibre product square of the
underlying schemes.**  The three functors involved — the forgetful functor of the slice, the
projection of a chart to the underlying object of the big fppf site of `S` and the projection of
that site to schemes — all preserve fibre products. -/
theorem isPullback_toScheme_of_isPullback {V : SmallEtale B S hS F} {W Y Z Pb : Over V}
    {fst : Pb ⟶ Y} {snd : Pb ⟶ Z} {f : Y ⟶ W} {g : Z ⟶ W} (h : IsPullback fst snd f g) :
    IsPullback
      ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map fst.left))
      ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map snd.left))
      ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map f.left))
      ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map g.left)) :=
  ((h.map (Over.forget V)).map (SmallEtale.toOver B S hS F)).map (BigFppfOver.toScheme B S hS)

/-- **The fibre product of two objects of a slice of the small étale site whose underlying schemes
are affine, over an object whose underlying scheme is affine, again has affine underlying
scheme.**  The square of underlying schemes is a fibre product square, and a fibre product of
affine schemes over an affine scheme is affine. -/
theorem isAffine_of_isPullback {V : SmallEtale B S hS F} {W Y Z Pb : Over V}
    {fst : Pb ⟶ Y} {snd : Pb ⟶ Z} {f : Y ⟶ W} {g : Z ⟶ W} (h : IsPullback fst snd f g)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj W.left)))
    (hY : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj Y.left)))
    (hZ : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj Z.left))) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj Pb.left)) := by
  have _ := hW
  have _ := hY
  have _ := hZ
  exact IsAffine.of_isIso (isPullback_toScheme_of_isPullback B S hS F h).isoPullback.hom

/-- **A family of objects of a slice of the small étale site with affine underlying scheme over an
object with affine underlying scheme has affine double and triple overlaps.**

The double overlap `Pb i j` is a fibre product of `g i` and `g j`, with projections `pr₁ i j` and
`pr₂ i j` and, on the diagonal, a section `δ i` of both projections of `Pb i i`.  The triple
overlap `Pb₃ i j k` is a fibre product of `g i` with the composite `pr₁ j k ≫ g j`, with a
projection `q i j k` onto `Y i` and a projection `t₂₃ i j k` onto `Pb j k`, and it carries two
further projections `t₁₂ i j k` onto `Pb i j` and `t₁₃ i j k` onto `Pb i k` whose composites with
the first projections are `q i j k` and whose composites with the second projections are the two
legs of `t₂₃ i j k`.  Both overlaps have affine underlying scheme.

The two projections onto the double overlaps and their four equations are
`CategoryTheory.IsPullback.exists_familyCechProjections`, the diagonals are
`CategoryTheory.IsPullback.exists_diagonal` at the self-overlaps, and the affineness is
`AlgebraicGeometry.Space.SmallEtale.isAffine_of_isPullback`.  Neither finiteness of the index type
nor any covering property of the family is used.

This is the small étale counterpart of
`AlgebraicGeometry.FibredSite.exists_affine_family_overlaps`; everything is returned in one
existential rather than in several, as there, because the equations speak of the same morphisms
the earlier components return. -/
theorem exists_affine_family_overlaps {V : SmallEtale B S hS F} {T : Over V}
    {ι : Type*} (Y : ι → Over V) (g : ∀ i, Y i ⟶ T)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj T.left)))
    (hY : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj (Y i).left))) :
    ∃ (Pb : ι → ι → Over V) (Pb₃ : ι → ι → ι → Over V)
      (pr₁ : ∀ i j, Pb i j ⟶ Y i) (pr₂ : ∀ i j, Pb i j ⟶ Y j) (δ : ∀ i, Y i ⟶ Pb i i)
      (q : ∀ i j k, Pb₃ i j k ⟶ Y i) (t₁₂ : ∀ i j k, Pb₃ i j k ⟶ Pb i j)
      (t₁₃ : ∀ i j k, Pb₃ i j k ⟶ Pb i k) (t₂₃ : ∀ i j k, Pb₃ i j k ⟶ Pb j k),
      (∀ i j, IsAffine ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj (Pb i j).left))) ∧
      (∀ i j k, IsAffine ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj (Pb₃ i j k).left))) ∧
      (∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (g i) (g j)) ∧
      (∀ i j k, IsPullback (q i j k) (t₂₃ i j k) (g i) (pr₁ j k ≫ g j)) ∧
      (∀ i, δ i ≫ pr₁ i i = 𝟙 (Y i)) ∧ (∀ i, δ i ≫ pr₂ i i = 𝟙 (Y i)) ∧
      (∀ i j k, t₁₂ i j k ≫ pr₁ i j = q i j k) ∧
      (∀ i j k, t₁₃ i j k ≫ pr₁ i k = q i j k) ∧
      (∀ i j k, t₁₂ i j k ≫ pr₂ i j = t₂₃ i j k ≫ pr₁ j k) ∧
      (∀ i j k, t₁₃ i j k ≫ pr₂ i k = t₂₃ i j k ≫ pr₂ j k) := by
  have hpb : ∀ i j, IsPullback (pullback.fst (g i) (g j)) (pullback.snd (g i) (g j))
      (g i) (g j) := fun i j ↦ IsPullback.of_hasPullback (g i) (g j)
  have hpb₃ : ∀ i j k, IsPullback
      (pullback.fst (g i) (pullback.fst (g j) (g k) ≫ g j))
      (pullback.snd (g i) (pullback.fst (g j) (g k) ≫ g j))
      (g i) (pullback.fst (g j) (g k) ≫ g j) := fun i j k ↦ IsPullback.of_hasPullback _ _
  obtain ⟨t₁₂, t₁₃, hq₁₂, hq₁₃, hc₂, hc₃⟩ := IsPullback.exists_familyCechProjections hpb hpb₃
  choose δ hδ₁ hδ₂ using fun i ↦ (hpb i i).exists_diagonal
  have hPaff : ∀ i j, IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj (pullback (g i) (g j)).left)) := fun i j ↦
    isAffine_of_isPullback B S hS F (hpb i j) hT (hY i) (hY j)
  exact ⟨fun i j ↦ pullback (g i) (g j),
    fun i j k ↦ pullback (g i) (pullback.fst (g j) (g k) ≫ g j),
    fun i j ↦ pullback.fst (g i) (g j), fun i j ↦ pullback.snd (g i) (g j), δ,
    fun i j k ↦ pullback.fst (g i) (pullback.fst (g j) (g k) ≫ g j), t₁₂, t₁₃,
    fun i j k ↦ pullback.snd (g i) (pullback.fst (g j) (g k) ≫ g j), hPaff,
    fun i j k ↦ isAffine_of_isPullback B S hS F (hpb₃ i j k) hT (hY i) (hPaff j k),
    hpb, hpb₃, hδ₁, hδ₂, hq₁₂, hq₁₃, hc₂, hc₃⟩

/-! ### The global functions on the étale charts -/

/-- **The global functions on the schemes underlying the étale charts of `F` are contravariantly
functorial.**  The map induced by a composite is the composite of the two induced maps in the
other order, because `AlgebraicGeometry.Scheme.Hom.appTop` is contravariant.

Stated for morphisms of charts rather than for morphisms of a slice: a morphism of a slice is a
morphism of charts and a composite in a slice has the composite as its underlying morphism, so a
consumer working in a slice applies this to the underlying morphisms. -/
theorem appTopGamma_comp_apply {U W Z : SmallEtale B S hS F} (f : U ⟶ W) (h : W ⟶ Z)
    (b : Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj Z), ⊤)) :
    ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map f)).appTop.hom
        (((BigFppfOver.toScheme B S hS).map
          ((SmallEtale.toOver B S hS F).map h)).appTop.hom b) =
      ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS F).map (f ≫ h))).appTop.hom b := by
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Scheme.Hom.comp_appTop]
  rfl

/-- The map of global functions induced by an identity of charts is the identity. -/
theorem appTopGamma_id_apply {U : SmallEtale B S hS F}
    (b : Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj U), ⊤)) :
    ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS F).map (𝟙 U : U ⟶ U))).appTop.hom b = b := by
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  simp

/-- **A factorisation of a morphism of charts factors the induced map of global functions.**
This is `AlgebraicGeometry.Space.SmallEtale.appTopGamma_comp_apply` with the composite named,
which is the form the commutations between the projections of the overlaps of a covering family
are stated in; with the composite an identity it says that the map induced by a section is a
retraction of the map induced by the morphism it is a section of. -/
theorem appTopGamma_comp_apply_of_eq {U W Z : SmallEtale B S hS F} (f : U ⟶ W) (h : W ⟶ Z)
    (k : U ⟶ Z) (hk : f ≫ h = k)
    (b : Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj Z), ⊤)) :
    ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map f)).appTop.hom
        (((BigFppfOver.toScheme B S hS).map
          ((SmallEtale.toOver B S hS F).map h)).appTop.hom b) =
      ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS F).map k)).appTop.hom b := by
  rw [appTopGamma_comp_apply, hk]

/-! ### The ring of sections of the structure sheaf of a slice -/

variable (hF : IsAlgebraicSpace B S hS F)

/-- **The sections of the coefficient sheaf of rings of a slice of the small étale ringed site at
an object are the global functions on the underlying scheme.**  The restriction of a sheaf to a
slice is its composite with the forgetful functor of the slice, and the structure sheaf of the
small étale site sends a chart to the global functions on the scheme underlying it, so the two
sides are the same object of `RingCat`.

This is a definitional equation rather than a `simp` lemma: it is named so that a statement about
the sections of a sheaf of modules on a slice can be matched with a statement about modules over a
commutative ring, which is what
`AlgebraicGeometry.Space.SmallEtale.sectionRingEquivGamma` then does. -/
theorem ringSheaf_over_obj_obj {V : (smallEtaleRingedSite B S hS F hF).C} (W : Over V) :
    (((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)).over V).obj.obj (op W) =
      RingCat.of Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj W.left), ⊤) := rfl

/-- **The ring of sections of the coefficient sheaf of rings of a slice of the small étale ringed
site at an object, identified with a commutative ring.**  By
`AlgebraicGeometry.Space.SmallEtale.ringSheaf_over_obj_obj` the two are the same ring, so the
identification is the identity; its point is that the right-hand side is the carrier of a
`CommRingCat` and therefore carries a `CommRing` instance, which the ring of sections of a sheaf
of `RingCat` does not.

This is what a consumer asking for a basis over a commutative ring supplies to
`AlgebraicGeometry.Space.SmallEtale.tautBasisOfIsAffineCoeffs`. -/
noncomputable def sectionRingEquivGamma {V : (smallEtaleRingedSite B S hS F hF).C} (W : Over V) :
    ((((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)).over V).obj.obj (op W) :
        Type u) ≃+*
      Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj W.left), ⊤) :=
  RingEquiv.refl _

/-- **Restriction of sections along a morphism of the slice is semilinear along the induced map of
global functions.**

The ring of sections of the coefficient sheaf of rings at an object of the slice is the ring of
global functions on the underlying scheme, and its restriction map is the induced map of global
functions, so the semilinearity of the restriction of a sheaf of modules reads as stated.  The two
module structures are the caller's, identified with the action of the ring of sections by `hW` and
`hU`; for the structures a consumer has they are `fun _ _ => rfl`. -/
theorem restrictₛₗ_smul_appTopGamma {V : (smallEtaleRingedSite B S hS F hF).C}
    (N : SheafOfModules.{u} (((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)).over V))
    {U W : Over V} (f : U ⟶ W)
    [Module Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj W.left), ⊤) (N.val.obj (op W))]
    [Module Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj U.left), ⊤) (N.val.obj (op U))]
    (hW : ∀ (c : Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj W.left), ⊤)) (n : N.val.obj (op W)),
      c • n = (sectionRingEquivGamma B S hS F hF W).symm c • n)
    (hU : ∀ (c : Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj U.left), ⊤)) (n : N.val.obj (op U)),
      c • n = (sectionRingEquivGamma B S hS F hF U).symm c • n)
    (b : Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj W.left), ⊤)) (n : N.val.obj (op W)) :
    N.val.restrictₛₗ f.op (b • n) =
      ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS F).map f.left)).appTop.hom b •
          N.val.restrictₛₗ f.op n := by
  rw [hW, hU]
  exact N.val.map_smul f.op _ n

/-- **A factorisation of a morphism of the slice makes a scalar tower on the sections at its
source.**  Let `f : U ⟶ W` and `h : W ⟶ Z` compose to `k`.  The sections of a sheaf of modules
over `U` are a module over the global functions on `W` through `f` and over those on `Z` through
`k`, and the structure map of the algebra of `W` over `Z` is the one induced by `h`; the two
actions are then compatible, because the map induced by `k` is the map induced by `h` followed by
the map induced by `f`.

This is the only scalar tower of a family descent datum which is not
`IsScalarTower.of_algebraMap_smul fun _ _ => rfl`: the two over an overlap whose two legs are a
projection onto a member and the structural morphism of another member hold by the commutation of
the fibre product square, which is this statement with `hk` that commutation. -/
theorem isScalarTower_appTopGamma {V : (smallEtaleRingedSite B S hS F hF).C}
    (N : SheafOfModules.{u} (((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)).over V))
    {U W Z : Over V} (f : U ⟶ W) (h : W ⟶ Z) (k : U ⟶ Z) (hk : f ≫ h = k)
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj Z.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left), ⊤)]
    [Module Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj U.left), ⊤) (N.val.obj (op U))]
    [Module Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj W.left), ⊤) (N.val.obj (op U))]
    [Module Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj Z.left), ⊤) (N.val.obj (op U))]
    (halg : algebraMap Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj Z.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj W.left), ⊤) =
      ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS F).map h.left)).appTop.hom)
    (hW : ∀ (b : Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj W.left), ⊤)) (n : N.val.obj (op U)),
      b • n = ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS F).map f.left)).appTop.hom b • n)
    (hZ : ∀ (a : Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj Z.left), ⊤)) (n : N.val.obj (op U)),
      a • n = ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS F).map k.left)).appTop.hom a • n) :
    IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj Z.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W.left), ⊤)
      (N.val.obj (op U)) :=
  IsScalarTower.of_algebraMap_smul fun a n ↦ by
    have hk' : f.left ≫ h.left = k.left := by rw [← Over.comp_left, hk]
    rw [halg, hW, hZ]
    exact congrArg (fun c ↦ c • n) (appTopGamma_comp_apply_of_eq B S hS F _ _ _ hk' a)

/-! ### The rings of the overlaps as tensor products -/

/-- **The ring of global functions on a fibre product of two objects of a slice of the small étale
site with affine underlying scheme over an object with affine underlying scheme is the tensor
product of the rings of the two factors over the ring of the object they lie over**, by an
isomorphism taking `b ⊗ₜ 1` to the image of `b` along the first projection and `1 ⊗ₜ c` to the
image of `c` along the second.

The isomorphism is `AlgebraicGeometry.algEquivTensorAppTopOfIsPullback` at the square of
underlying schemes, and the two values are
`AlgebraicGeometry.algEquivTensorAppTopOfIsPullback_tmul`.  It is returned as a ring isomorphism,
and the second value is stated through the algebra structure along the second projection rather
than through that projection itself, which is the shape a descent datum for a family of covering
morphisms asks for: there the two factors may be the same member, so the two maps into the ring of
the overlap cannot both be algebra structures.

Taking the second factor to be a double overlap of the family rather than a member gives the same
statement for the triple overlaps, since a triple overlap is a fibre product of a member with a
double overlap. -/
theorem exists_ringEquivTensorGamma_of_isPullback {V : SmallEtale B S hS F}
    {T Yi Yj Pb : Over V} {fst : Pb ⟶ Yi} {snd : Pb ⟶ Yj} {gi : Yi ⟶ T} {gj : Yj ⟶ T}
    (h : IsPullback fst snd gi gj)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj T.left)))
    (hYi : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj Yi.left)))
    (hYj : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj Yj.left)))
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj T.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj Yi.left), ⊤)]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj T.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj Yj.left), ⊤)]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj T.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj Pb.left), ⊤)]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj Yj.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj Pb.left), ⊤)]
    (hgi : algebraMap Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj T.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj Yi.left), ⊤) =
      ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS F).map gi.left)).appTop.hom)
    (hgj : algebraMap Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj T.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj Yj.left), ⊤) =
      ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS F).map gj.left)).appTop.hom)
    (hPb : algebraMap Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj T.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj Pb.left), ⊤) =
      ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS F).map (fst ≫ gi).left)).appTop.hom)
    (hsnd : algebraMap Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj Yj.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj Pb.left), ⊤) =
      ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS F).map snd.left)).appTop.hom) :
    ∃ ψ : Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj Yi.left), ⊤)
        ⊗[Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj T.left), ⊤)]
        Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj Yj.left), ⊤) ≃+*
        Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj Pb.left), ⊤),
      (∀ b : Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj Yi.left), ⊤),
        ψ (b ⊗ₜ[Γ((BigFppfOver.toScheme B S hS).obj
            ((SmallEtale.toOver B S hS F).obj T.left), ⊤)]
            (1 : Γ((BigFppfOver.toScheme B S hS).obj
              ((SmallEtale.toOver B S hS F).obj Yj.left), ⊤))) =
          ((BigFppfOver.toScheme B S hS).map
            ((SmallEtale.toOver B S hS F).map fst.left)).appTop.hom b) ∧
      (∀ c : Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj Yj.left), ⊤),
        ψ ((1 : Γ((BigFppfOver.toScheme B S hS).obj
              ((SmallEtale.toOver B S hS F).obj Yi.left), ⊤))
            ⊗ₜ[Γ((BigFppfOver.toScheme B S hS).obj
              ((SmallEtale.toOver B S hS F).obj T.left), ⊤)] c) =
          algebraMap Γ((BigFppfOver.toScheme B S hS).obj
              ((SmallEtale.toOver B S hS F).obj Yj.left), ⊤)
            Γ((BigFppfOver.toScheme B S hS).obj
              ((SmallEtale.toOver B S hS F).obj Pb.left), ⊤) c) := by
  have _ := hT
  have _ := hYi
  have _ := hYj
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj Pb.left)) :=
    isAffine_of_isPullback B S hS F h hT hYi hYj
  have hsq := isPullback_toScheme_of_isPullback B S hS F h
  refine (fun hu hv ↦ ⟨(algEquivTensorAppTopOfIsPullback hsq hgi hgj hu hv).toRingEquiv,
    fun b ↦ ?_, fun c ↦ ?_⟩) (fun a ↦ ?_) (fun a ↦ ?_)
  · rw [hgi, hPb]
    exact appTopGamma_comp_apply B S hS F fst.left gi.left a
  · rw [hgj, hPb, h.w]
    exact appTopGamma_comp_apply B S hS F snd.left gj.left a
  · refine (algEquivTensorAppTopOfIsPullback_tmul hsq hgi hgj _ _ b 1).trans ?_
    simp
  · refine (algEquivTensorAppTopOfIsPullback_tmul hsq hgi hgj _ _ 1 c).trans ?_
    rw [hsnd]
    simp

/-! ### Faithful flatness of the product of the rings of a covering family -/

/-- **The product of the rings of global functions on the members of a finite flat covering family
of an object of a slice of the small étale site with affine underlying scheme, by objects with
affine underlying scheme, is faithfully flat over the ring of global functions on the object
covered.**

This is the form of faithful flatness a covering *family* supplies, and it is what descent along
the family needs: no member of the family is surjective by itself, so no single ring of global
functions is faithfully flat over the base, and the separatedness argument runs through the
product.  It is
`AlgebraicGeometry.faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage` with the affineness
hypotheses read off the slice. -/
theorem faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage {V : SmallEtale B S hS F}
    {W : Over V} {ι : Type*} [Finite ι] (Y : ι → Over V) (a : ∀ i, Y i ⟶ W)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj W.left)))
    (hY : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj (Y i).left)))
    (hfppf : Presieve.ofArrows
        (fun i ↦ (BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj (Y i).left))
        (fun i ↦ (BigFppfOver.toScheme B S hS).map
          ((SmallEtale.toOver B S hS F).map (a i).left)) ∈
      Scheme.fppfPrecoverage ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj W.left)))
    [∀ i, Algebra Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj W.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Y i).left), ⊤)]
    (halg : ∀ i, algebraMap Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj W.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj (Y i).left), ⊤) =
      ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS F).map (a i).left)).appTop.hom) :
    Module.FaithfullyFlat Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj W.left), ⊤)
      (∀ i, Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (Y i).left), ⊤)) :=
  have _ := hW
  have _ : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj (Y i).left)) := hY
  _root_.AlgebraicGeometry.faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage _ hfppf halg

/-! ### The sections of a coproduct of structure sheaves over an affine object -/

section Decomposition

variable {V : (smallEtaleRingedSite B S hS F hF).C}
  {R : Sheaf ((smallEtaleRingedSite B S hS F hF).J.over V) RingCat.{r}}
  {I : Type z} {N : SheafOfModules.{max t r} R}
  (ι : ∀ _ : I, SheafOfModules.uliftForPresentation.{u + 1, u, r, r, t}
    (SheafOfModules.unit R) ⟶ N)
  (hN : IsColimit (Cofan.mk N ι)) (W : Over V)
  (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((SmallEtale.toOver B S hS F).obj W.left)))

/-- **The sections of a coproduct of copies of the universe lift of the structure sheaf over an
object of a slice of the small étale site whose underlying scheme is affine are the finitely
supported families of sections of the structure sheaf.**  This is
`SheafOfModules.sectionsEquivFinsupp` with its finite subcovering hypothesis discharged by
`AlgebraicGeometry.Space.SmallEtale.hasFiniteSubcovering_over`.

Nothing is assumed of the sheaf of rings on the slice beyond its being one: the identification is
the statement that the coproduct is computed section by section at an affine object, and the
finiteness which makes that true comes from quasi-compactness of the affine scheme alone. -/
noncomputable def sectionsEquivFinsuppOfIsAffine :
    (I →₀ R.obj.obj (op W)) ≃ₗ[R.obj.obj (op W)] N.val.obj (op W) :=
  SheafOfModules.sectionsEquivFinsupp ι hN (hasFiniteSubcovering_over B S hS F W hW)

/-- `AlgebraicGeometry.Space.SmallEtale.sectionsEquivFinsuppOfIsAffine` is the linear combination
of the tautological generators. -/
lemma sectionsEquivFinsuppOfIsAffine_apply (c : I →₀ R.obj.obj (op W)) :
    sectionsEquivFinsuppOfIsAffine B S hS F hF ι hN W hW c =
      Finsupp.linearCombination (R.obj.obj (op W))
        (fun i ↦ SheafOfModules.tautGen ι i (op W)) c :=
  SheafOfModules.sectionsEquivFinsupp_apply ι hN _ c

/-- **The tautological generators of a coproduct of copies of the universe lift of the structure
sheaf form a basis of its sections over an object of a slice of the small étale site whose
underlying scheme is affine.**  This is `SheafOfModules.tautBasis` with its finite subcovering
hypothesis discharged by
`AlgebraicGeometry.Space.SmallEtale.hasFiniteSubcovering_over`; it is the shape in which the
comparison of the sections of a presented module with a base change consumes the
decomposition. -/
noncomputable def tautBasisOfIsAffine :
    Module.Basis I (R.obj.obj (op W)) (N.val.obj (op W)) :=
  SheafOfModules.tautBasis ι hN (hasFiniteSubcovering_over B S hS F W hW)

/-- `AlgebraicGeometry.Space.SmallEtale.tautBasisOfIsAffine` is the family of tautological
generators. -/
@[simp]
lemma tautBasisOfIsAffine_apply (i : I) :
    tautBasisOfIsAffine B S hS F hF ι hN W hW i = SheafOfModules.tautGen ι i (op W) :=
  SheafOfModules.tautBasis_apply ι hN _ i

variable {A : Type*} [Semiring A] [Module A (N.val.obj (op W))]
  (f : (R.obj.obj (op W) : Type r) ≃+* A)
  (hf : ∀ (c : R.obj.obj (op W)) (n : N.val.obj (op W)), f c • n = c • n)

/-- **The tautological generators as a basis over a ring identified with the ring of sections.**
`AlgebraicGeometry.Space.SmallEtale.tautBasisOfIsAffine` is a basis over the ring of sections of
the structure sheaf, which is an object of `RingCat` and so carries no commutativity; a consumer
comparing the sections of a presented module with a base change needs a basis over a genuine
commutative ring.  Transporting along a ring equivalence acting in the same way supplies it.

The equivalence and the agreement of the two actions are hypotheses rather than being produced
here, because the module structure over `A` is the consumer's: it arrives together with the scalar
tower over the ring of sections at the object covered which the base change is taken along.  For
the coefficient sheaf of rings of a slice of the small étale ringed site the equivalence is
`AlgebraicGeometry.Space.SmallEtale.sectionRingEquivGamma`. -/
noncomputable def tautBasisOfIsAffineCoeffs : Module.Basis I A (N.val.obj (op W)) :=
  (tautBasisOfIsAffine B S hS F hF ι hN W hW).mapCoeffs f hf

/-- `AlgebraicGeometry.Space.SmallEtale.tautBasisOfIsAffineCoeffs` is still the family of
tautological generators: transporting the coefficients does not move the basis vectors.  This is
the identification of the basis vectors which the base-change comparison asks for alongside the
basis itself. -/
@[simp]
lemma tautBasisOfIsAffineCoeffs_apply (i : I) :
    tautBasisOfIsAffineCoeffs B S hS F hF ι hN W hW f hf i =
      SheafOfModules.tautGen ι i (op W) :=
  (Module.Basis.mapCoeffs_apply _ f hf i).trans
    (tautBasisOfIsAffine_apply B S hS F hF ι hN W hW i)

end Decomposition

end SmallEtale

end AlgebraicGeometry.Space

end
