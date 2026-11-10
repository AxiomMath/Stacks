module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.NodeStalkCharacterization
public import StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.SingularLocus
public import StacksFrontier.AlgebraicGeometry.F6Rank136.AtWorstNodalRelativeDimensionOne
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.FibrePointResidueField
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.LocalCompleteIntersection
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ClosedPoint
public import StacksFrontier.RingTheory.CompleteIntersection.Local
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The unramified singular subscheme of a local complete intersection curve

Let `k` be a field and let `X` be a locally algebraic `k`-scheme, equidimensional of dimension
one.  Suppose that `X` is a local complete intersection over `k` and that the closed subscheme
`Z ⊆ X` cut out by the first Fitting ideal of `Ω_{X/k}` is unramified over `k`.  Then at every
closed point `x` of `X` either the structure morphism is smooth, or all three numerical
conditions of Tag 0C4D hold at `x`: the residue field extension at `x` is separable, the local
ring `𝒪_{X,x}` is one-dimensional of depth one, and the first Fitting ideal of `Ω_{X/k}`
generates the maximal ideal of `𝒪_{X,x}`.

Those two hypotheses are condition (2) of Tag 0C4E and the three conditions are condition (5)
of Tag 0C4D, so this is the implication (2) ⟹ (1) of Tag 0C4E up to the one step that turns
condition (5) of Tag 0C4D into the node condition.  That step is not proved *in this file*, but
it is available in the library — `Stacks.Curves.isNode_tfae_of_isClosed` carries a bare
`@[stacks 0C4D]` over an arbitrary field; see the implementation notes.

## Main results

* `Stacks.Curves.relativeDimension_one_of_equidimensional` — over a field, an equidimensional
  scheme of dimension one is a morphism of relative dimension one.
* `Stacks.Curves.ringKrullDim_stalk_eq_one_of_equidimensional` — the local ring at a closed
  point of such a scheme is one-dimensional.
* `Stacks.Curves.isField_stalk_of_unramified_over_field` — the local rings of a scheme
  unramified over a field are fields.
* `Stacks.Curves.isSeparable_residueField_of_unramified_comp` — if `i ≫ f` is unramified and
  `i` is surjective on stalks, the residue field extension of `f` at the image of a point is
  separable.
* `Stacks.Curves.smoothAt_or_isSeparable_and_depth_eq_one_and_fittingIdeal_eq_maximalIdeal` —
  the implication above.

## Implementation notes

The closed subscheme cut out by the first Fitting ideal of `Ω_{X/k}` is
`AlgebraicGeometry.relativeSingularIdeal`, whose subscheme inclusion is
`Scheme.IdealSheafData.subschemeι`, and condition (2) of Tag 0C4E is the conjunction of
`AlgebraicGeometry.IsLocalCompleteIntersectionOverField` for the structure morphism with
unramifiedness of that inclusion followed by the structure morphism.  These are the two halves
of `AlgebraicGeometry.IsAtWorstNodalOfRelativeDimensionOne` of Tag 0C5A, up to the fibre
dimension, which the equidimensionality hypothesis supplies.

Three of the four pieces are read off results in the library.  The point lies in `Z` exactly when
the structure morphism is not smooth there, by Tag 0C3K; the local ring is one-dimensional because
at a closed point of a locally algebraic scheme the dimension of the local ring is the local
dimension of the scheme (Tag 0A21), which equidimensionality makes constant; and the depth is
the dimension because a local complete intersection over a field has complete-intersection
local rings (Tag 01UG) and those are Cohen-Macaulay (Tag 00SB).

The Fitting-ideal condition is the one assertion about `Z` itself.  A scheme unramified over a
field is reduced and discrete, so its local rings are fields; the stalk map of the subscheme
inclusion is surjective with kernel the stalk of the ideal sheaf, so a surjection onto a field
from `𝒪_{X,x}` has kernel the maximal ideal, and that kernel is the stalk of the first Fitting
ideal.  Separability is the residue field half of Tag 02G8 for `Z ⟶ Spec k`, carried to `X`
along the residue field map of the subscheme inclusion, which is an isomorphism because that
inclusion is surjective on stalks.

Separability is stated over `(Spec k).residueField (f x)` rather than over `k`.  That field is
`k`, through the canonical map `k ⟶ Γ(Spec k, ⊤) ⟶ 𝒪_{Spec k, f x} ⟶ κ(f x)`; the spelling is
the one of Tag 02G8 as it is stated in
`AlgebraicGeometry.isSeparable_residueField_of_unramified`, and no identification of that field
with `k` is made here.

What this file leaves to another is the implication (5) ⟹ (1) of Tag 0C4D, and **it is
available**: `Stacks.Curves.isNode_tfae_of_isClosed`
(`StacksFrontier/AlgebraicGeometry/Curves/NodeFittingIdealClosedPoint.lean`) carries a bare
`@[stacks 0C4D]`, i.e. the whole six-clause equivalence at a closed point of a one-dimensional
scheme locally of finite type over an **arbitrary** field, and the separability supplied in the
second disjunct of the theorem below is exactly what lets its cycle
`1 → 2 → 3 → 4 → 5 → 6 → 1` be run; `(... ).out 5 1` is then the step that turns condition (5)
into the node condition.  The two are composed in
`Stacks.NodalEtaleLocalStructure.isNode_asFiber_of_mem_relativeSingular`
(`StacksFrontier/AlgebraicGeometry/Curves/NodalEtaleLocalStructureAssembly.lean`), on which Tag
0CBY's existence statement rests.  Alternatives, if the closed-point hypothesis is inconvenient:
`Stacks.Curves.isNode_of_isNodalAlgebra_stalk`
(`StacksFrontier/AlgebraicGeometry/Curves/NodeNodalAlgebraAscent.lean`,
`@[stacks 0C4D "clause (2) implies clause (1), over an arbitrary base field"]`) and
`Stacks.Curves.isNode_iff_isNodalAlgebra_stalk`
(`StacksFrontier/AlgebraicGeometry/Curves/NodeResidueFieldSeparable.lean`).

This paragraph previously said the implication "is not available" over an arbitrary base field,
pointing at the unproved `h₁₄`/`h₄₅` of `Stacks.Curves.isNode_tfae_of_residual_equivalences`.
That was true of *that* route only.  As written it suggested that Tag 0CBY was blocked on
unproved mathematics when it was assembly of existing results.  What remains genuinely unproved is
the converse (1) ⟹ (2) of Tag 0C4E, which nothing here claims.

## References

* [Stacks Project, Tag 0C4E](https://stacks.math.columbia.edu/tag/0C4E)
* [Stacks Project, Tag 0C4D](https://stacks.math.columbia.edu/tag/0C4D)
* [Stacks Project, Tag 0C3K](https://stacks.math.columbia.edu/tag/0C3K)
* [Stacks Project, Tag 01UG](https://stacks.math.columbia.edu/tag/01UG)
* [Stacks Project, Tag 00SB](https://stacks.math.columbia.edu/tag/00SB)
* [Stacks Project, Tag 02G8](https://stacks.math.columbia.edu/tag/02G8)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry IsLocalRing

universe u

namespace Stacks.Curves

/-! ### Dimension of a locally algebraic curve and of its local rings -/

/-- The preimage of any point under a morphism to the spectrum of a field is the whole space. -/
private theorem preimage_singleton_eq_univ_of_field (k : Type u) [Field k] {Z : Scheme.{u}}
    (g : Z ⟶ AlgebraicGeometry.Spec (.of k)) (s : AlgebraicGeometry.Spec (.of k)) :
    g.base ⁻¹' {s} = (Set.univ : Set Z) := by
  have : Subsingleton (AlgebraicGeometry.Spec (.of k)) := by
    change Subsingleton (PrimeSpectrum k)
    infer_instance
  ext z
  simp [Subsingleton.elim (g.base z) s]

/-- **A scheme over a field, equidimensional of dimension one, is of relative dimension one.**
The unique fibre of the structure morphism is homeomorphic to the scheme itself, so both clauses
of `AlgebraicGeometry.RelativeDimension` transport from the scheme to the fibre. -/
theorem relativeDimension_one_of_equidimensional (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (.of k)) [LocallyOfFiniteType f]
    (hequi : Equidimensional X) (hdim : topologicalKrullDim X = 1) :
    RelativeDimension f 1 := by
  intro s _
  have hpre := preimage_singleton_eq_univ_of_field k f s
  let e : f.fiber s ≃ₜ X :=
    (f.fiberHomeo s).trans ((Homeomorph.setCongr hpre).trans (Homeomorph.Set.univ X))
  refine ⟨Equidimensional.of_homeomorph e hequi, ?_⟩
  rw [IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph, hdim]
  norm_num

/-- **The local ring at a closed point of a locally algebraic scheme over a field,
equidimensional of dimension one, is one-dimensional.**  At a closed point the dimension of the
local ring is the local dimension of the scheme (Tag 0A21), and equidimensionality makes the
local dimension equal to the dimension of the scheme. -/
theorem ringKrullDim_stalk_eq_one_of_equidimensional (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (.of k)) [LocallyOfFiniteType f]
    (hequi : Equidimensional X) (hdim : topologicalKrullDim X = 1)
    (x : X) (hx : IsClosed ({x} : Set X)) :
    ringKrullDim (X.presheaf.stalk x) = 1 := by
  rw [← topologicalKrullDimAt_eq_krullDimOfRing_stalk k X f x hx]
  exact topologicalKrullDimAt_eq_of_equidimensional k X f (d := 1) hequi
    (by norm_num [hdim]) x

/-! ### Local rings of a scheme unramified over a field -/

/-- A scheme formally unramified and locally of finite type over a field is reduced. -/
@[sga "3 XI 1.3" "(i)(a)⇒(d)"]
private theorem isReduced_of_formallyUnramified_over_base_field (k : Type u) [Field k]
    {Z : Scheme.{u}} (g : Z ⟶ AlgebraicGeometry.Spec (.of k)) [FormallyUnramified g]
    [LocallyOfFiniteType g] : IsReduced Z := by
  wlog hZ : ∃ A : CommRingCat.{u}, Z = AlgebraicGeometry.Spec A generalizing Z
  · rw [IsReduced.iff_of_openCover Z Z.affineCover]
    intro i
    have hF : FormallyUnramified (Z.affineCover.f i ≫ g) :=
      MorphismProperty.comp_mem @FormallyUnramified _ _
        (inferInstanceAs (FormallyUnramified (Z.affineCover.f i))) inferInstance
    have hL : LocallyOfFiniteType (Z.affineCover.f i ≫ g) :=
      MorphismProperty.comp_mem @LocallyOfFiniteType _ _
        (inferInstanceAs (LocallyOfFiniteType (Z.affineCover.f i))) inferInstance
    exact this (g := Z.affineCover.f i ≫ g) ⟨_, rfl⟩
  obtain ⟨A, rfl⟩ := hZ
  obtain ⟨φ, rfl⟩ := Spec.map_surjective g
  algebraize [φ.hom]
  have : Algebra.FormallyUnramified k A :=
    (HasRingHomProperty.Spec_iff (P := @FormallyUnramified) (φ := φ)).mp inferInstance
  have : Algebra.FiniteType k A :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp inferInstance
  have : Algebra.EssFiniteType k A := inferInstance
  have : _root_.IsReduced A := Algebra.FormallyUnramified.isReduced_of_field k A
  infer_instance

/-- A scheme unramified over a field has discrete underlying space: the whole space is the
unique fibre of the structure morphism, and the fibres of an unramified morphism are
discrete. -/
private theorem discreteTopology_of_unramified_over_base_field (k : Type u) [Field k]
    {Z : Scheme.{u}} (g : Z ⟶ AlgebraicGeometry.Spec (.of k)) [LocallyQuasiFinite g] :
    DiscreteTopology Z := by
  let s : AlgebraicGeometry.Spec (.of k) := IsLocalRing.closedPoint k
  rw [← isDiscrete_univ_iff]
  simpa only [preimage_singleton_eq_univ_of_field k g s] using g.isDiscrete_preimage_singleton s

/-- **The local rings of a scheme unramified over a field are fields.**  Such a scheme is
reduced and its underlying space is discrete, so every point is a maximal point of a reduced
scheme. -/
@[sga "3 XI 1.3" "(ii)"]
theorem isField_stalk_of_unramified_over_field (k : Type u) [Field k] {Z : Scheme.{u}}
    (g : Z ⟶ AlgebraicGeometry.Spec (.of k)) [Unramified g] (z : Z) :
    IsField (Z.presheaf.stalk z) := by
  have : FormallyUnramified g := formallyUnramified_of_unramified g
  have : IsReduced Z := isReduced_of_formallyUnramified_over_base_field k g
  have : DiscreteTopology Z := discreteTopology_of_unramified_over_base_field k g
  exact isField_stalk_of_isMax (x := z) fun b hb =>
    (specializes_iff_eq.mp (show b ⤳ z from hb)) ▸ le_rfl

/-! ### The residue field extension at a point of an unramified subscheme -/

/-- **The residue field extension at the image of a point of an unramified subscheme is
separable.**  If `i ≫ f` is unramified and `i` is surjective on stalks, then the residue field
map of `i` is an isomorphism, so the residue field extension of `f` at `i z` is the one of
`i ≫ f` at `z`, which is separable by Tag 02G8. -/
theorem isSeparable_residueField_of_unramified_comp {X Z S : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X)
    [SurjectiveOnStalks i] [Unramified (i ≫ f)] (z : Z) :
    letI : Algebra (S.residueField (f.base (i.base z))) (X.residueField (i.base z)) :=
      (f.residueFieldMap (i.base z)).hom.toAlgebra
    Algebra.IsSeparable (S.residueField (f.base (i.base z))) (X.residueField (i.base z)) := by
  let : Algebra (S.residueField (f.base (i.base z))) (X.residueField (i.base z)) :=
    (f.residueFieldMap (i.base z)).hom.toAlgebra
  let : Algebra (S.residueField (f.base (i.base z))) (Z.residueField z) :=
    ((i ≫ f).residueFieldMap z).hom.toAlgebra
  have hsep : Algebra.IsSeparable (S.residueField (f.base (i.base z))) (Z.residueField z) :=
    isSeparable_residueField_of_unramified (i ≫ f) z
  let eiso : X.residueField (i.base z) ≃+* Z.residueField z :=
    (asIso (i.residueFieldMap z)).commRingCatIsoToRingEquiv
  have key : ∀ a, eiso ((f.residueFieldMap (i.base z)).hom a) =
      algebraMap (S.residueField (f.base (i.base z))) (Z.residueField z) a := by
    intro a
    change eiso ((f.residueFieldMap (i.base z)).hom a) = ((i ≫ f).residueFieldMap z).hom a
    rw [Scheme.residueFieldMap_comp]
    rfl
  refine Algebra.IsSeparable.of_equiv_equiv
    (RingEquiv.refl (S.residueField (f.base (i.base z)))) eiso.symm (RingHom.ext fun a => ?_)
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_refl, id_eq,
    RingEquiv.coe_toRingHom]
  exact (eiso.symm_apply_eq.mpr (key a).symm).symm

/-! ### The implication (2) ⟹ (1) of Tag 0C4E, up to Tag 0C4D -/

/-- **Condition (2) of Tag 0C4E gives condition (5) of Tag 0C4D at every closed point.**  Let
`k` be a field and `X` a locally algebraic `k`-scheme, equidimensional of dimension one.  Assume
`X` is a local complete intersection over `k` and that the closed subscheme cut out by the first
Fitting ideal of `Ω_{X/k}` is unramified over `k`.  Then at a closed point `x` of `X` either the
structure morphism is smooth, or the residue field extension at `x` is separable, `𝒪_{X,x}` is
one-dimensional of depth one, and the first Fitting ideal of `Ω_{X/k}` generates the maximal
ideal of `𝒪_{X,x}`.

The hypotheses are condition (2) of Tag 0C4E and the second disjunct is condition (5) of Tag
0C4D together with the dimension of the local ring.  Separability is stated over the residue
field of the image point of `Spec k`, the spelling of Tag 02G8.

The remaining step of the implication (2) ⟹ (1) of Tag 0C4E — that condition (5) of Tag 0C4D
makes such a point a node — is not delivered *here*, but it **is** available in the library:
`Stacks.Curves.isNode_tfae_of_isClosed`
(`StacksFrontier/AlgebraicGeometry/Curves/NodeFittingIdealClosedPoint.lean`) carries a bare
`@[stacks 0C4D]`, i.e. the whole six-clause equivalence at a closed point of a one-dimensional
scheme locally of finite type over an **arbitrary** field, and the separability this theorem
supplies in its second disjunct is exactly what lets its cycle `1 → 2 → 3 → 4 → 5 → 6 → 1` be
run, so `(... ).out 5 1` supplies the step.  (5) ⟹ (1) over an arbitrary base field is therefore
in hand, and the two are composed in
`Stacks.NodalEtaleLocalStructure.isNode_asFiber_of_mem_relativeSingular`
(`StacksFrontier/AlgebraicGeometry/Curves/NodalEtaleLocalStructureAssembly.lean`), which is what Tag
0CBY's existence statement rests on.

The step does not depend on the unproved `h₁₄`/`h₄₅` of
`Stacks.Curves.isNode_tfae_of_residual_equivalences`; that route is only one of several, and
Tag 0CBY is an assembly of proved results.  Alternatives, if the
closed-point hypothesis of `isNode_tfae_of_isClosed` is inconvenient:
`Stacks.Curves.isNode_of_isNodalAlgebra_stalk`
(`StacksFrontier/AlgebraicGeometry/Curves/NodeNodalAlgebraAscent.lean`,
`@[stacks 0C4D "clause (2) implies clause (1), over an
arbitrary base field"]`) and `Stacks.Curves.isNode_iff_isNodalAlgebra_stalk`
(`StacksFrontier/AlgebraicGeometry/Curves/NodeResidueFieldSeparable.lean`). -/
@[stacks 0C4E "the implication (2) ⟹ (1), via condition (5) of Tag 0C4D at every closed point"]
theorem smoothAt_or_isSeparable_and_depth_eq_one_and_fittingIdeal_eq_maximalIdeal
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ AlgebraicGeometry.Spec (.of k))
    [LocallyOfFiniteType f] (hequi : Equidimensional X) (hdim : topologicalKrullDim X = 1)
    (hlci : IsLocalCompleteIntersectionOverField f)
    (hZ : Unramified ((relativeSingularIdeal f).subschemeι ≫ f))
    (x : X) (hx : IsClosed ({x} : Set X)) :
    letI : Algebra ((AlgebraicGeometry.Spec (.of k)).residueField (f.base x))
        (X.residueField x) := (f.residueFieldMap x).hom.toAlgebra
    (InfinitesimalLifting.SmoothAt f x ∨
      (Algebra.IsSeparable ((AlgebraicGeometry.Spec (.of k)).residueField (f.base x))
          (X.residueField x) ∧
        ringKrullDim (X.presheaf.stalk x) = 1 ∧
          Module.depth (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))
              (X.presheaf.stalk x) = 1 ∧
            IdealSheafData.stalk (relativeSingularIdeal f) x =
              maximalIdeal (X.presheaf.stalk x))) := by
  let : Algebra ((AlgebraicGeometry.Spec (.of k)).residueField (f.base x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  by_cases hsm : InfinitesimalLifting.SmoothAt f x
  · exact Or.inl hsm
  -- the point lies in the subscheme cut out by the first Fitting ideal, by Tag 0C3K
  have hRD : RelativeDimension f 1 := relativeDimension_one_of_equidimensional k f hequi hdim
  have : Flat f := inferInstance
  have : LocallyOfFinitePresentation f := inferInstance
  obtain ⟨z, rfl⟩ : x ∈ Set.range (relativeSingularIdeal f).subschemeι :=
    (mem_fittingIdeal_relativeDifferentials_iff_not_smoothAt f 1 hRD x).mpr hsm
  refine Or.inr ⟨isSeparable_residueField_of_unramified_comp f _ z, ?_, ?_, ?_⟩
  · exact ringKrullDim_stalk_eq_one_of_equidimensional k f hequi hdim _ hx
  · -- a local complete intersection over a field has Cohen-Macaulay local rings
    let : Algebra k (X.presheaf.stalk ((relativeSingularIdeal f).subschemeι.base z)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
        X.presheaf.germ ⊤ _ (by simp)).hom.toAlgebra
    have hci : IsCompleteIntersection k
        (X.presheaf.stalk ((relativeSingularIdeal f).subschemeι.base z)) := by
      have h := ((localCompleteIntersection_tfae k X f).out 1 3).mp hlci
      exact h _
    have : IsNoetherianRing (X.presheaf.stalk ((relativeSingularIdeal f).subschemeι.base z)) :=
      (isNagataRing_stalk_of_locallyOfFiniteType k f
        ((relativeSingularIdeal f).subschemeι.base z)).isNoetherianRing
    have hCM := hci.isMaximalCohenMacaulay
    rw [Module.IsMaximalCohenMacaulay,
      ringKrullDim_stalk_eq_one_of_equidimensional k f hequi hdim _ hx] at hCM
    exact_mod_cast hCM
  · -- the local ring of the subscheme is a field, so the stalk of the ideal is maximal
    let : Field ((relativeSingularIdeal f).subscheme.presheaf.stalk z) :=
      (isField_stalk_of_unramified_over_field k
        ((relativeSingularIdeal f).subschemeι ≫ f) z).toField
    exact (IdealSheafData.ker_stalkMap_subschemeι_eq_stalk (relativeSingularIdeal f) z).symm.trans
      (IsLocalRing.ker_eq_maximalIdeal _
        ((relativeSingularIdeal f).subschemeι.stalkMap_surjective z))

end Stacks.Curves

end
