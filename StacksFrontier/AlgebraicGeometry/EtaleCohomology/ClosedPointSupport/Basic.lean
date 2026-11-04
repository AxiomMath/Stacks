module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import StacksFrontier.AlgebraicGeometry.BirationalCurveFinite.Basic
public import StacksFrontier.AlgebraicGeometry.Etale.SupportSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkIsomorphismCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SupportSheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Abelian sheaves supported at closed points: the ambient toolkit

An abelian sheaf on the small étale site of [Stacks, Tag 021B] — the size-bounded site cut out
of a big étale site `B` — is detected by its geometric stalks, and this file records the three
consequences of that which the study of sheaves supported at closed points needs: a sheaf all of
whose geometric stalks vanish is zero, a morphism surjective on all geometric stalks is an
epimorphism, and the two spellings of the support of such a sheaf agree.

It also records the field-theoretic input: over a separably closed field the residue field at a
closed point of a scheme locally of finite type is again separably closed. The extension is
finite by the Nullstellensatz, hence algebraic, and an algebraic extension of a separably closed
field is separably closed — it is purely inseparable, so it creates no new separable roots.

## Main results

* `AlgebraicGeometry.SmallEtale.isGrothendieckAbelian_sheaf_succ` — abelian sheaves on the small
  étale site of [Stacks, Tag 021B] at the coefficient universe `u + 1` form a Grothendieck
  abelian category relative to `u + 1`. This is what makes `CategoryTheory.Sheaf.H` and the
  injective resolutions behind it available on this site with no hypothesis.
* `AlgebraicGeometry.epi_of_surjective_etaleStalkMap` — a morphism of abelian sheaves surjective
  on every geometric stalk is an epimorphism.
* `AlgebraicGeometry.isZero_of_forall_isZero_etaleStalk` — an abelian sheaf all of whose
  geometric stalks vanish is zero.
* `AlgebraicGeometry.supportSheaf_eq_smallEtale_supportSheaf` — the universe-lifted support of
  [Stacks, Tag 04FS] agrees with the unlifted one of [Stacks, Tag 04FU].
* `AlgebraicGeometry.preservesFiniteLimits_etaleStalkPresheafFunctor` — a geometric stalk is left
  exact, and `AlgebraicGeometry.supportSheaf_subset_of_mono` — hence the support of a subsheaf
  lies in the support of the ambient sheaf.
* `AlgebraicGeometry.finite_of_isClosed_of_forall_isClosed_singleton` — a closed subset of a
  Noetherian scheme all of whose points are closed is finite.
* `AlgebraicGeometry.isSepClosed_residueField_of_isClosed` — the residue field at a closed point
  of a scheme locally of finite type over a separably closed field is separably closed.

## Implementation notes

Both support definitions of the library are needed downstream: the colimit decomposition of
[Stacks, Tag 0F0N] is stated with the lifted `AlgebraicGeometry.supportSheaf`, while the
essential-image criterion of [Stacks, Tag 04CA] is stated with the unlifted
`AlgebraicGeometry.SmallEtale.supportSheaf`. Their agreement is
`AlgebraicGeometry.isZero_etaleStalk_ulift_iff` applied pointwise, which is exactly why the
unlifted one carries a `CategoryTheory.Limits.HasColimit` hypothesis and the lifted one does not.

The Grothendieck-abelian fact is stated as a theorem rather than an instance: its head mentions
the universe `u + 1` with the site's universe `u` free, and an instance of that shape makes
resolution fail on a universe constraint rather than backtrack. Consumers install it with
`attribute [local instance]`, as
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointDirectSumCohomology` does for Mathlib's
small étale site.

The algebra structure on the residue field used for the separable-closedness statement is the one
coming from `AlgebraicGeometry.Scheme.fromSpecResidueField` followed by the structure morphism,
built by hand as a `letI` inside the proof; no `Algebra` instance is exported, since a scheme
point carries no canonical one.

## References

* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
* [Stacks Project, Tag 04FS](https://stacks.math.columbia.edu/tag/04FS)
* [Stacks Project, Tag 04FU](https://stacks.math.columbia.edu/tag/04FU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open scoped ZeroObject

universe u v

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Abelian sheaves on the small étale site of [Stacks, Tag 021B] form a Grothendieck abelian
category** relative to `u + 1`, at the coefficient universe `u + 1`: the site is essentially
small in that universe.

`AlgebraicGeometry.SmallEtale.isGrothendieckAbelian_sheaf` is the statement at the coefficient
universe of the *morphisms* of the site; this is the one at the universe of its *objects*, which
is where étale cohomology is written, and neither follows from the other. -/
public theorem SmallEtale.isGrothendieckAbelian_sheaf_succ :
    IsGrothendieckAbelian.{u + 1} (Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u + 1}) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1} _ _

/-- **A morphism of abelian étale sheaves surjective on every geometric stalk is an
epimorphism.** Surjectivity on stalks makes it locally surjective, and on this site local
surjectivity of abelian sheaves is epimorphy. -/
public theorem epi_of_surjective_etaleStalkMap [UnivLE.{u, v}]
    {F G : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v}} (α : F ⟶ G)
    (h : ∀ s : GeometricPoint S, Function.Surjective
      ((etaleStalkPresheafFunctor B S hS s AddCommGrpCat.{v}).map α.hom)) :
    Epi α :=
  have := isLocallySurjective_of_surjective_etaleStalkMap B S hS α h
  Sheaf.epi_of_isLocallySurjective α

/-- **An abelian étale sheaf all of whose geometric stalks vanish is zero.** The zero morphism to
the zero sheaf is surjective on every geometric stalk, hence an epimorphism.

Stated at the coefficient universe `u + 1`, the first one in which the site has a zero sheaf: the
zero object of the category of abelian sheaves comes from sheafification, which is available there
because the site is essentially small in that universe. -/
public theorem isZero_of_forall_isZero_etaleStalk
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u + 1})
    (h : ∀ s : GeometricPoint S,
      IsZero ((etaleStalkPresheafFunctor B S hS s AddCommGrpCat.{u + 1}).obj F.obj)) :
    IsZero F := by
  have hepi : Epi (0 : (0 : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u + 1}) ⟶ F) :=
    epi_of_surjective_etaleStalkMap.{u, u + 1} B S hS _
      fun s y => ⟨0, @Subsingleton.elim _ (AddCommGrpCat.subsingleton_of_isZero (h s)) _ _⟩
  exact (isZero_zero _).of_epi (0 : _ ⟶ F)

/-- **The two spellings of the support of an abelian étale sheaf agree.** The support of
[Stacks, Tag 04FS] is computed from the geometric stalks of the universe-lifted sheaf and the
support of [Stacks, Tag 04FU] from those of the sheaf itself; lifting does not change vanishing
of a stalk that already exists. -/
public theorem supportSheaf_eq_smallEtale_supportSheaf [UnivLE.{u, v}]
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    [∀ t : GeometricPoint S, HasColimit (SmallEtale.etaleStalkDiagram B S hS t F.obj)] :
    supportSheaf B S hS F = SmallEtale.supportSheaf B S hS F := by
  ext x
  simp only [mem_supportSheaf_iff_exists, SmallEtale.supportSheaf, Set.mem_ofPred_eq]
  exact exists_congr fun p =>
    and_congr_right fun _ => not_congr (isZero_etaleStalk_ulift_iff B S hS F p)

/-- **A geometric stalk of abelian étale sheaves is left exact.** It is a filtered colimit taken
in a category satisfying AB5 for the size of the indexing category of étale neighbourhoods. -/
public theorem preservesFiniteLimits_etaleStalkPresheafFunctor (p : GeometricPoint S) :
    PreservesFiniteLimits (etaleStalkPresheafFunctor B S hS p AddCommGrpCat.{u + 1}) := by
  let : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
    AB5OfSize_shrink.{u, u, u + 1, u + 1, u + 1, u + 2} AddCommGrpCat.{u + 1}
  let : HasExactColimitsOfShape
      (geometricPointFiber B S hS p).Elementsᵒᵖ AddCommGrpCat.{u + 1} :=
    hasExactColimitsOfShape_of_final AddCommGrpCat.{u + 1}
      (FinallySmall.fromFilteredFinalModel.{u} ((geometricPointFiber B S hS p).Elementsᵒᵖ))
  dsimp [etaleStalkPresheafFunctor]
  infer_instance

/-- **The support of a subsheaf is contained in the support of the ambient sheaf.** A geometric
stalk is left exact, so it carries a monomorphism of abelian sheaves to a monomorphism of abelian
groups, and a group injecting into a zero group is zero. -/
public theorem supportSheaf_subset_of_mono
    (F G : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u + 1}) (α : F ⟶ G) [Mono α] :
    supportSheaf B S hS F ⊆ supportSheaf B S hS G := by
  intro x hx
  rw [mem_supportSheaf_iff_exists] at hx ⊢
  simp only [isZero_etaleStalk_ulift_iff] at hx ⊢
  obtain ⟨p, hp, hn⟩ := hx
  refine ⟨p, hp, fun hzero => hn ?_⟩
  let FtoP := sheafToPresheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u + 1}
  let St := etaleStalkPresheafFunctor B S hS p AddCommGrpCat.{u + 1}
  let : PreservesFiniteLimits St := preservesFiniteLimits_etaleStalkPresheafFunctor B S hS p
  let : Mono (FtoP.map α) := FtoP.map_mono α
  have hmono : Mono (St.map (FtoP.map α)) := preserves_mono_of_preservesLimit St (FtoP.map α)
  refine (IsZero.iff_id_eq_zero _).2 (hmono.right_cancellation (𝟙 _) 0 ?_)
  calc 𝟙 _ ≫ St.map (FtoP.map α) = St.map (FtoP.map α) := by simp
    _ = 0 := hzero.eq_of_tgt (St.map (FtoP.map α)) 0
    _ = 0 ≫ St.map (FtoP.map α) := by simp

/-- **A closed subset of a Noetherian scheme all of whose points are closed is finite.** It is a
discrete subspace by [Stacks, Tag 0A2R], and a Noetherian discrete space is compact and discrete,
hence finite. -/
@[ega "I 6.2.2" "more general"]
public theorem finite_of_isClosed_of_forall_isClosed_singleton {X : Scheme.{u}} [IsNoetherian X]
    {s : Set X} (hs : IsClosed s) (hcl : ∀ x ∈ s, IsClosed ({x} : Set X)) :
    s.Finite := by
  have hdisc :=
    Stacks.AlgebraicGeometry.BirationalCurveFinite.isDiscrete_of_forall_isClosed_singleton hs hcl
  have : DiscreteTopology ↥s := _root_.isDiscrete_iff_discreteTopology.mp hdisc
  have : TopologicalSpace.NoetherianSpace ↥X := inferInstance
  have : TopologicalSpace.NoetherianSpace ↥s := inferInstance
  have : CompactSpace ↥s := inferInstance
  exact Set.finite_coe_iff.mp finite_of_compact_of_discrete

/-- **The residue field at a closed point of a scheme locally of finite type over a separably
closed field is separably closed.** The point being closed, its spectrum is reduced with one
point, so the composite to the base is finite by the Nullstellensatz; the residue field is
therefore an algebraic extension of the base, and an algebraic extension of a separably closed
field is separably closed. -/
public theorem isSepClosed_residueField_of_isClosed {K : Type u} [Field K] [IsSepClosed K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] (x : X)
    (hx : IsClosed ({x} : Set X)) :
    IsSepClosed (X.residueField x) := by
  have hfin : (Spec.preimage (X.fromSpecResidueField x ≫ f)).hom.Finite := by
    have : IsFinite (X.fromSpecResidueField x ≫ f) := by
      rw [isClosed_singleton_iff_isClosedImmersion] at hx
      rw [isFinite_iff_locallyOfFiniteType_of_jacobsonSpace]
      infer_instance
    rw [← IsFinite.SpecMap_iff, Spec.map_preimage]
    infer_instance
  let : Algebra K (X.residueField x) :=
    (Spec.preimage (X.fromSpecResidueField x ≫ f)).hom.toAlgebra
  have : Module.Finite K (X.residueField x) := hfin
  exact Algebra.IsAlgebraic.isSepClosed (F := K) (E := X.residueField x)

end AlgebraicGeometry

end
