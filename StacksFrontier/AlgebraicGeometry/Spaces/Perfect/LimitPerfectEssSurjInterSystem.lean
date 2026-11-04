module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectDescentBridgeCocycle
public import StacksFrontier.CategoryTheory.PullbackData.LimitHomSystem

/-!
# The three systems of the base changes of an elementary distinguished square

Let `(U₀ ⊆ W₀, f₀ : V₀ ⟶ W₀)` be an elementary distinguished square, let `p_b : W_b ⟶ W₀` be a
morphism of algebraic spaces and let `T` be a directed system over `W_b` with a cone — a
`CategoryTheory.PullbackData.LimitSystem` with base `W_b`, stages `T_j`, structure morphisms
`k_j : T_j ⟶ W_b`, transition morphisms over `W_b` and a vertex with projections over `W_b`.  By
Stacks 08GN, part (2), the square pulls back along each composite `k_j ≫ p_b`, and the induced
maps of the three members (`AlgebraicGeometry.Space.edsPreimageOpenMap`,
`…edsPreimageEtaleMap`, `…edsPreimageInterMap`) turn each member into a system of the same shape
over the corresponding member of the square over `W_b`.

**This file builds those three systems.**  In Situation 09RH, read `W₀` as a quasi-compact
quasi-separated algebraic space étale over `X₀`, `T` as the system of base changes
`W₀ ×_{X₀} X_j` with vertex `W₀ ×_{X₀} X`, and `p_b` as the structure morphism of the base
stage; the three systems are then the systems of base changes of the open subspace, of the étale
algebraic space and of the intersection of the square, which are what the
elementary-distinguished-square step of the essential surjectivity half of Stacks 09RJ works
with.

## Main definitions

* `AlgebraicGeometry.Space.edsPreimageOpenLimitSystem`,
  `…edsPreimageEtaleLimitSystem`, `…edsPreimageInterLimitSystem`: the three systems.

## No geometric identification is used, and none is needed

A `CategoryTheory.PullbackData.LimitSystem` asks only for transition morphisms that lie over the
base and compose, and projections that lie over the base and are compatible with the transition
morphisms.  **It carries no limit property.**  So the three systems below are assembled from the
cocycle identities of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitPerfectDescentBridgeCocycle.lean` and nothing
else: in particular the identification

`edsInter (edsPreimage hsq (k_j ≫ p_b)) ≅ edsInter hsq ×_{W₀} T_j`

— the fibre-product description of the intersection of a base-changed square, which would be
needed to read the system of intersections as the system of stages of Situation 09RH base
changed along the intersection, `AlgebraicGeometry.Space.DescentSituation.stagesBaseChangeAlong`
— is **not** used and is **not** assumed.  It is therefore unnecessary for producing the systems
the step works with, and for the hom-level map
`CategoryTheory.PullbackData.LimitSystem.projHom` that the step's comparison isomorphism is
measured against.  It remains needed only to import the colimit statement of Stacks 09RI in the
shape in which that statement is currently stated, namely for a
`AlgebraicGeometry.Space.DescentSituation` and its own system of stages
(`AlgebraicGeometry.Space.DescentSituation.isHomColimit_canonicalDerivedPullbackSystem_iff`); a
statement of Stacks 09RI for an arbitrary `CategoryTheory.PullbackData.LimitSystem` would remove
it from the argument entirely.

## The hypotheses carried

None beyond the elementary distinguished square, the morphism `p_b` and the system `T`.  Each of
the nine structure fields of each system below is an instance of one of the three cocycle
identities, with the third morphism of the identity supplied by the corresponding field of `T`;
no `Prop` binder stands in for missing mathematics and no limit property of `T` is used or
assumed.

## References

* [Stacks Project, Lemma 75.9.1 (Tag 08GN)](https://stacks.math.columbia.edu/tag/08GN)
* [Stacks Project, Lemma 75.24.3 (Tag 09RJ)](https://stacks.math.columbia.edu/tag/09RJ)
* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Lemma 75.9.3 (Tag 08GP)](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Situation 75.24.1 (Tag 09RH)](https://stacks.math.columbia.edu/tag/09RH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe w u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {W₀ : AlgebraicSpaces B S hS} {V₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {U₀ : Subfunctor W₀.1} {f₀ : V₀ ⟶ W₀.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W₀.2 U₀ f₀)
  {Wb : AlgebraicSpaces B S hS} (pb : Wb ⟶ W₀)
  {J : Type w} [Preorder J]
  (T : PullbackData.LimitSystem (A := AlgebraicSpaces B S hS) Wb J)

/-- **The system of open subspaces of the base changes of an elementary distinguished square**
along a system over `W_b`: its stages are the open subspaces `U₀ ×_{W₀} T_j` of the base changes
of the square, its base is the open subspace of the square over `W_b`, and all nine structure
fields are instances of
`AlgebraicGeometry.Space.edsPreimageOpenMap_comp_edsPreimageOpenMap`. -/
def edsPreimageOpenLimitSystem :
    PullbackData.LimitSystem (A := AlgebraicSpaces B S hS)
      (edsOpen B S hS (edsPreimage hsq pb)) J where
  stage j := edsOpen B S hS (edsPreimage hsq (T.toBase j ≫ pb))
  toBase j := edsPreimageOpenMap hsq pb (T.toBase j ≫ pb) (T.toBase j) rfl
  transition {i j} h := edsPreimageOpenMap hsq (T.toBase i ≫ pb) (T.toBase j ≫ pb)
    (T.transition h) (by rw [← Category.assoc, T.transition_toBase h])
  transition_toBase {i j} h := edsPreimageOpenMap_comp_edsPreimageOpenMap hsq pb
    (T.toBase i ≫ pb) (T.toBase j ≫ pb) (T.toBase i) (T.transition h) rfl
    (by rw [← Category.assoc, T.transition_toBase h]) (T.toBase j)
    (T.transition_toBase h).symm rfl
  transition_comp {i j k} h h' := edsPreimageOpenMap_comp_edsPreimageOpenMap hsq
    (T.toBase i ≫ pb) (T.toBase j ≫ pb) (T.toBase k ≫ pb) (T.transition h) (T.transition h')
    (by rw [← Category.assoc, T.transition_toBase h])
    (by rw [← Category.assoc, T.transition_toBase h']) (T.transition (h.trans h'))
    (T.transition_comp h h').symm (by rw [← Category.assoc, T.transition_toBase (h.trans h')])
  limit := edsOpen B S hS (edsPreimage hsq (T.limitToBase ≫ pb))
  limitToBase := edsPreimageOpenMap hsq pb (T.limitToBase ≫ pb) T.limitToBase rfl
  proj j := edsPreimageOpenMap hsq (T.toBase j ≫ pb) (T.limitToBase ≫ pb) (T.proj j)
    (by rw [← Category.assoc, T.proj_toBase j])
  proj_toBase j := edsPreimageOpenMap_comp_edsPreimageOpenMap hsq pb (T.toBase j ≫ pb)
    (T.limitToBase ≫ pb) (T.toBase j) (T.proj j) rfl
    (by rw [← Category.assoc, T.proj_toBase j]) T.limitToBase (T.proj_toBase j).symm rfl
  proj_transition {i j} h := edsPreimageOpenMap_comp_edsPreimageOpenMap hsq
    (T.toBase i ≫ pb) (T.toBase j ≫ pb) (T.limitToBase ≫ pb) (T.transition h) (T.proj j)
    (by rw [← Category.assoc, T.transition_toBase h])
    (by rw [← Category.assoc, T.proj_toBase j]) (T.proj i) (T.proj_transition h).symm
    (by rw [← Category.assoc, T.proj_toBase i])

/-- **The system of étale algebraic spaces of the base changes of an elementary distinguished
square** along a system over `W_b`: its stages are the fibre products `V₀ ×_{W₀} T_j`, and all
nine structure fields are instances of
`AlgebraicGeometry.Space.edsPreimageEtaleMap_comp_edsPreimageEtaleMap`. -/
def edsPreimageEtaleLimitSystem :
    PullbackData.LimitSystem (A := AlgebraicSpaces B S hS)
      (edsEtale B S hS (edsPreimage hsq pb)) J where
  stage j := edsEtale B S hS (edsPreimage hsq (T.toBase j ≫ pb))
  toBase j := edsPreimageEtaleMap hsq pb (T.toBase j ≫ pb) (T.toBase j) rfl
  transition {i j} h := edsPreimageEtaleMap hsq (T.toBase i ≫ pb) (T.toBase j ≫ pb)
    (T.transition h) (by rw [← Category.assoc, T.transition_toBase h])
  transition_toBase {i j} h := edsPreimageEtaleMap_comp_edsPreimageEtaleMap hsq pb
    (T.toBase i ≫ pb) (T.toBase j ≫ pb) (T.toBase i) (T.transition h) rfl
    (by rw [← Category.assoc, T.transition_toBase h]) (T.toBase j)
    (T.transition_toBase h).symm rfl
  transition_comp {i j k} h h' := edsPreimageEtaleMap_comp_edsPreimageEtaleMap hsq
    (T.toBase i ≫ pb) (T.toBase j ≫ pb) (T.toBase k ≫ pb) (T.transition h) (T.transition h')
    (by rw [← Category.assoc, T.transition_toBase h])
    (by rw [← Category.assoc, T.transition_toBase h']) (T.transition (h.trans h'))
    (T.transition_comp h h').symm (by rw [← Category.assoc, T.transition_toBase (h.trans h')])
  limit := edsEtale B S hS (edsPreimage hsq (T.limitToBase ≫ pb))
  limitToBase := edsPreimageEtaleMap hsq pb (T.limitToBase ≫ pb) T.limitToBase rfl
  proj j := edsPreimageEtaleMap hsq (T.toBase j ≫ pb) (T.limitToBase ≫ pb) (T.proj j)
    (by rw [← Category.assoc, T.proj_toBase j])
  proj_toBase j := edsPreimageEtaleMap_comp_edsPreimageEtaleMap hsq pb (T.toBase j ≫ pb)
    (T.limitToBase ≫ pb) (T.toBase j) (T.proj j) rfl
    (by rw [← Category.assoc, T.proj_toBase j]) T.limitToBase (T.proj_toBase j).symm rfl
  proj_transition {i j} h := edsPreimageEtaleMap_comp_edsPreimageEtaleMap hsq
    (T.toBase i ≫ pb) (T.toBase j ≫ pb) (T.limitToBase ≫ pb) (T.transition h) (T.proj j)
    (by rw [← Category.assoc, T.transition_toBase h])
    (by rw [← Category.assoc, T.proj_toBase j]) (T.proj i) (T.proj_transition h).symm
    (by rw [← Category.assoc, T.proj_toBase i])

/-- **The system of intersections of the base changes of an elementary distinguished square**
along a system over `W_b`: its stages are the intersections `(U₀ ×_{W₀} V₀) ×_{W₀} T_j` of the
base changes of the square, its base is the intersection of the square over `W_b`, and all nine
structure fields are instances of
`AlgebraicGeometry.Space.edsPreimageInterMap_comp_edsPreimageInterMap`.

This is the system the comparison isomorphism over the intersection is produced on.  See "No
geometric identification is used, and none is needed" in this file's module documentation: the
fibre-product description of these stages is neither used nor assumed. -/
def edsPreimageInterLimitSystem :
    PullbackData.LimitSystem (A := AlgebraicSpaces B S hS)
      (edsInter B S hS (edsPreimage hsq pb)) J where
  stage j := edsInter B S hS (edsPreimage hsq (T.toBase j ≫ pb))
  toBase j := edsPreimageInterMap hsq pb (T.toBase j ≫ pb) (T.toBase j) rfl
  transition {i j} h := edsPreimageInterMap hsq (T.toBase i ≫ pb) (T.toBase j ≫ pb)
    (T.transition h) (by rw [← Category.assoc, T.transition_toBase h])
  transition_toBase {i j} h := edsPreimageInterMap_comp_edsPreimageInterMap hsq pb
    (T.toBase i ≫ pb) (T.toBase j ≫ pb) (T.toBase i) (T.transition h) rfl
    (by rw [← Category.assoc, T.transition_toBase h]) (T.toBase j)
    (T.transition_toBase h).symm rfl
  transition_comp {i j k} h h' := edsPreimageInterMap_comp_edsPreimageInterMap hsq
    (T.toBase i ≫ pb) (T.toBase j ≫ pb) (T.toBase k ≫ pb) (T.transition h) (T.transition h')
    (by rw [← Category.assoc, T.transition_toBase h])
    (by rw [← Category.assoc, T.transition_toBase h']) (T.transition (h.trans h'))
    (T.transition_comp h h').symm (by rw [← Category.assoc, T.transition_toBase (h.trans h')])
  limit := edsInter B S hS (edsPreimage hsq (T.limitToBase ≫ pb))
  limitToBase := edsPreimageInterMap hsq pb (T.limitToBase ≫ pb) T.limitToBase rfl
  proj j := edsPreimageInterMap hsq (T.toBase j ≫ pb) (T.limitToBase ≫ pb) (T.proj j)
    (by rw [← Category.assoc, T.proj_toBase j])
  proj_toBase j := edsPreimageInterMap_comp_edsPreimageInterMap hsq pb (T.toBase j ≫ pb)
    (T.limitToBase ≫ pb) (T.toBase j) (T.proj j) rfl
    (by rw [← Category.assoc, T.proj_toBase j]) T.limitToBase (T.proj_toBase j).symm rfl
  proj_transition {i j} h := edsPreimageInterMap_comp_edsPreimageInterMap hsq
    (T.toBase i ≫ pb) (T.toBase j ≫ pb) (T.limitToBase ≫ pb) (T.transition h) (T.proj j)
    (by rw [← Category.assoc, T.transition_toBase h])
    (by rw [← Category.assoc, T.proj_toBase j]) (T.proj i) (T.proj_transition h).symm
    (by rw [← Category.assoc, T.proj_toBase i])

end AlgebraicGeometry.Space

end
