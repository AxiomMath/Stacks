module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.SetTheory.Cardinal.ENat
public import Mathlib.Topology.KrullDimension
public import StacksCore.Tactic.StacksAttribute

/-!
# The étale site of schemes locally of finite type over a base

The schemes locally of finite type over a base scheme `S` form a full subcategory of the
schemes over `S`, and the big étale topology restricts to a Grothendieck topology on it.
The quasi-compact objects of this site, together with the étale coverings whose members are
quasi-compact, form a distinguished collection: every object is covered by quasi-compact
ones, and the quasi-compact coverings of any object are cofinal among all of its coverings.
Attached to an object is the numerical bound
`1 + 2 dim S + sup_v (trdeg_{κ(s)} κ(v) + 2 dim 𝒪_{V, v})`
above which étale cohomology of sheaves of modules over a finite ring of invertible order
vanishes.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.etaleCohomologyBound` is the displayed bound attached to a
  morphism of schemes.
* `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale` is the category of schemes locally of
  finite type over `S`, and `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.topology` is the
  étale topology on it.
* `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.IsQuasiCompact` singles out the
  quasi-compact objects, and
  `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.IsQuasiCompactCovering` the étale
  coverings all of whose members are quasi-compact.

## Main results

* `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.exists_isQuasiCompactCovering`: every
  object has an étale covering by quasi-compact objects.
* `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.exists_isQuasiCompactCovering_le`: the
  étale coverings by quasi-compact objects are cofinal among all étale coverings.

## Implementation notes

The topology is the coarsest one on the subcategory containing the sieves whose image
generates an étale covering sieve of schemes; a covering by affine opens witnesses both
covering statements, since an affine scheme is quasi-compact and an open immersion is étale
and locally of finite type. In the bound the supremum is taken in `WithBot ℕ∞` and joined
with `0`, so that an object with no points gets the bound `1 + 2 dim S`. The transcendence
degree is that of the residue field of a point over the residue field of its image, for the
algebra structure given by the induced map of residue fields. The vanishing of étale
cohomology above the bound, for sheaves of modules over a finite ring whose order is
invertible on a base that is the spectrum of a finite or separably closed field, or of a
henselian Noetherian local ring with separably closed or finite residue field, rests on
Gabber's theorem on cohomological dimension and is not proved here.

## References

* [Stacks Project, Tag 0DC6](https://stacks.math.columbia.edu/tag/0DC6)
* [Travaux de Gabber, Exposé VIII-A, Corollary 1.2 and Lemma 2.2]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe w u

namespace AlgebraicGeometry.Scheme

/-- The degree `1 + 2 dim S + sup_v (trdeg_{κ(s)} κ(v) + 2 dim 𝒪_{X, v})` attached to a
morphism `f : X ⟶ S`, where `s` is the image of `v` under `f`. -/
@[stacks 0DC6 "the bound d_V"]
public def Hom.etaleCohomologyBound {X S : Scheme.{u}} (f : X ⟶ S) : WithBot ℕ∞ :=
  1 + 2 * topologicalKrullDim S +
    (0 ⊔ ⨆ x : X, (letI := (f.residueFieldMap x).hom.toAlgebra
      (Cardinal.toENat (Algebra.trdeg (S.residueField (f.base x)) (X.residueField x)) :
        WithBot ℕ∞) + 2 * ringKrullDim (X.presheaf.stalk x)))

/-- Being locally of finite type over `S`, as a property of the objects of the category of
schemes over `S`. -/
public def IsLocallyOfFiniteTypeOver (S : Scheme.{u}) : ObjectProperty (Over S) :=
  fun V ↦ LocallyOfFiniteType V.hom

/-- The schemes locally of finite type over `S`, as a full subcategory of the schemes
over `S`. -/
@[stacks 0DC6 "the site C of schemes locally of finite type over S"]
public abbrev LocallyFiniteTypeEtale (S : Scheme.{u}) : Type _ :=
  (IsLocallyOfFiniteTypeOver S).FullSubcategory

namespace LocallyFiniteTypeEtale

/-- The underlying scheme of a scheme locally of finite type over `S`. -/
public abbrev forget (S : Scheme.{u}) : LocallyFiniteTypeEtale S ⥤ Scheme.{u} :=
  (IsLocallyOfFiniteTypeOver S).ι ⋙ Over.forget S

/-- The étale topology on the schemes locally of finite type over `S`: the coarsest topology
containing every sieve whose underlying family of schemes generates an étale covering. -/
@[stacks 0DC6 "the étale topology on C"]
public abbrev topology (S : Scheme.{u}) : GrothendieckTopology (LocallyFiniteTypeEtale S) :=
  (forget S).restrictedTopology Scheme.etaleTopology

variable {S : Scheme.{u}}

/-- An object of the locally-finite-type étale site is quasi-compact when the scheme
underlying it is. -/
@[stacks 0DC6 "the set B of quasi-compact objects"]
public def IsQuasiCompact (V : LocallyFiniteTypeEtale S) : Prop := CompactSpace V.obj.left

/-- A family `{U i ⟶ V}` in the locally-finite-type étale site is a distinguished covering of
`V` when every `U i` is quasi-compact and the family generates a covering sieve. -/
@[stacks 0DC6 "the coverings Cov_V"]
public def IsQuasiCompactCovering {V : LocallyFiniteTypeEtale S} {I : Type w}
    (U : I → LocallyFiniteTypeEtale S) (f : ∀ i, U i ⟶ V) : Prop :=
  (∀ i, IsQuasiCompact (U i)) ∧
    Sieve.generate (Presieve.ofArrows U f) ∈ topology S V

/-- A member of the canonical cover of `V` by affine opens, again locally of finite type
over `S`. -/
public def affineObj (V : LocallyFiniteTypeEtale S) (i : V.obj.left.affineCover.I₀) :
    LocallyFiniteTypeEtale S :=
  ⟨Over.mk (V.obj.left.affineCover.f i ≫ V.obj.hom), by
    change LocallyOfFiniteType (V.obj.left.affineCover.f i ≫ V.obj.hom)
    have : LocallyOfFiniteType V.obj.hom := V.property
    infer_instance⟩

/-- The open immersion of a member of the canonical affine cover of `V` into `V`. -/
public def affineMap (V : LocallyFiniteTypeEtale S) (i : V.obj.left.affineCover.I₀) :
    affineObj V i ⟶ V :=
  ObjectProperty.homMk (Over.homMk (V.obj.left.affineCover.f i) rfl)

/-- The members of the canonical affine cover are quasi-compact. -/
public lemma isQuasiCompact_affineObj (V : LocallyFiniteTypeEtale S)
    (i : V.obj.left.affineCover.I₀) : IsQuasiCompact (affineObj V i) := by
  change CompactSpace (V.obj.left.affineCover.X i)
  infer_instance

/-- A member of a family belongs to the sieve the family generates. -/
public lemma mem_generate_ofArrows {V : LocallyFiniteTypeEtale S} {I : Type w}
    (U : I → LocallyFiniteTypeEtale S) (f : ∀ i, U i ⟶ V) (i : I) :
    (Sieve.generate (Presieve.ofArrows U f)).arrows (f i) :=
  Sieve.le_generate _ _ _ ⟨i⟩

/-- A family of étale morphisms in the site whose images cover the target generates a
covering sieve for the étale topology. -/
public lemma mem_topology_of_etale_of_surjective {V : LocallyFiniteTypeEtale S} {I : Type w}
    (U : I → LocallyFiniteTypeEtale S) (f : ∀ i, U i ⟶ V)
    (het : ∀ i, Etale ((forget S).map (f i)))
    (hsurj : ∀ x : V.obj.left, ∃ i, x ∈ Set.range ((forget S).map (f i)).base) :
    Sieve.generate (Presieve.ofArrows U f) ∈ topology S V := by
  apply Functor.mem_restrictedTopology_of_functorPushforward_mem
  have h : Sieve.generate (Presieve.ofArrows (fun i ↦ (forget S).obj (U i))
      (fun i ↦ (forget S).map (f i))) ∈ Scheme.etaleTopology ((forget S).obj V) :=
    Precoverage.generate_mem_toGrothendieck
      ((Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).mpr ⟨hsurj, het⟩)
  refine Scheme.etaleTopology.superset_covering ?_ h
  rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  exact fun i ↦ ⟨U i, f i, 𝟙 _, mem_generate_ofArrows U f i, by simp⟩

/-- The canonical cover of an object by its affine opens generates a covering sieve. -/
public lemma affineMap_mem_topology (V : LocallyFiniteTypeEtale S) :
    Sieve.generate (Presieve.ofArrows (affineObj V) (affineMap V)) ∈ topology S V := by
  refine mem_topology_of_etale_of_surjective _ _ (fun i ↦ ?_) (fun x ↦ ?_)
  · change Etale (V.obj.left.affineCover.f i)
    infer_instance
  · exact ⟨V.obj.left.affineCover.idx x, V.obj.left.affineCover.covers x⟩

/-- Every scheme locally of finite type over `S` has an étale covering whose members are
quasi-compact. -/
@[stacks 0DC6 "every object of C is covered by members of B"]
public theorem exists_isQuasiCompactCovering (V : LocallyFiniteTypeEtale S) :
    ∃ (I : Type u) (U : I → LocallyFiniteTypeEtale S) (f : ∀ i, U i ⟶ V),
      IsQuasiCompactCovering U f :=
  ⟨_, affineObj V, affineMap V, isQuasiCompact_affineObj V, affineMap_mem_topology V⟩

/-- Every étale covering sieve of a scheme locally of finite type over `S` is refined by an
étale covering whose members are quasi-compact. -/
@[stacks 0DC6 "Cov_V is a cofinal system of coverings"]
public theorem exists_isQuasiCompactCovering_le (V : LocallyFiniteTypeEtale S) (R : Sieve V)
    (hR : R ∈ topology S V) :
    ∃ (I : Type (u + 1)) (U : I → LocallyFiniteTypeEtale S) (f : ∀ i, U i ⟶ V),
      IsQuasiCompactCovering U f ∧ Sieve.generate (Presieve.ofArrows U f) ≤ R := by
  refine ⟨(W : LocallyFiniteTypeEtale S) ×
      {g : W ⟶ V // R.arrows g ∧ IsQuasiCompact W},
    fun p ↦ p.1, fun p ↦ p.2.1, ⟨fun p ↦ p.2.2.2, ?_⟩, ?_⟩
  · refine (topology S).transitive hR _ ?_
    intro T h hh
    refine GrothendieckTopology.superset_covering _ ?_ (affineMap_mem_topology T)
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    exact fun i ↦ mem_generate_ofArrows
      (fun p : (W : _) × {g : W ⟶ V // R.arrows g ∧ IsQuasiCompact W} ↦ p.1) _
      ⟨affineObj T i, ⟨affineMap T i ≫ h, R.downward_closed hh _,
        isQuasiCompact_affineObj T i⟩⟩
  · rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    exact fun p ↦ p.2.2.1

end LocallyFiniteTypeEtale

end AlgebraicGeometry.Scheme

end
