module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.RingTheory.Rig.FiniteType
public import StacksFrontier.RingTheory.Rig.IdealIndependence
public import StacksFrontier.RingTheory.Rig.RigSmoothDefs
public import StacksFrontier.Topology.Algebra.AdicTopology.IdealOfDefinition

/-!
# Rig-smooth and rig-étale homomorphisms of adic rings

Let `A` be a Noetherian ring, `I` an ideal of `A` and `B` an `I`-adically complete `A`-algebra
of finite type modulo `I`.  Then `B` is *rig-smooth* over `(A, I)` when a power of `I`
annihilates `Ext¹` out of the completed naive cotangent complex of `B`, and *rig-étale* over
`(A, I)` when a power of `I` annihilates the completed naive cotangent complex itself in the
derived category of `B`-modules.

For a continuous homomorphism of Noetherian adic topological rings which is adic and
topologically of finite type, neither notion depends on the chosen ideal of definition of the
source: if `I` and `J` are two ideals of definition then `I ^ n ≤ J` and `J ^ n ≤ I` for some
`n`, and the completed naive cotangent complex is independent of the ideal of definition, so
the annihilation condition for one ideal gives it for the other with the exponent multiplied
by `n`.

## Main definitions

* `Rig.IsRigEtaleOver`: rig-étaleness of the algebra defined by a ring homomorphism over a
  specified ideal of the source.
* `Rig.adicFiniteTypeAlgebra`: the target of a morphism satisfying condition (6) of
  Tag 0GBW, as an object of the category of Tag 0AL4 for a chosen ideal of definition.
* `RingHom.IsRigSmooth`: **Stacks 0GCJ**, rig-smoothness of a continuous homomorphism of
  Noetherian adic topological rings, and `RingHom.IsRigSmoothArrow`, the same notion as a
  property of arrows of `WAdm^{Noeth}`.
* `RingHom.IsRigEtale`: **Stacks 0GCV**, rig-étaleness of a continuous homomorphism of
  Noetherian adic topological rings.

## Main results

* `Rig.isRigSmooth_iff_forall_idealOfDefinition`: **Stacks 0GCI**.
* `Rig.rigEtaleOver_iff_forall_idealOfDefinition`: **Stacks 0GCU**.
* `RingHom.IsRigEtale.forall_idealOfDefinition`: a rig-étale homomorphism is rig-étale over
  *every* ideal of definition of its source, not only the one its definition provides, and
  `RingHom.IsRigSmooth.forall_idealOfDefinition` likewise for rig-smoothness.

## Implementation notes

The two notions themselves, `Rig.IsRigSmooth` (**Stacks 0GAI**) and `Rig.IsRigEtale`
(**Stacks 0GAY**), are defined in `StacksFrontier.RingTheory.Rig.RigSmoothDefs` and imported here.
They are shared with the presentation-independence development
(`StacksFrontier.RingTheory.Restricted.RigSmooth`, `…Restricted.RigEtale`), which builds on the
same two definitions from the other side; keeping them in a module below both is what lets the
two developments be imported together.

The two independence statements are deduced from one transfer lemma each
(`Rig.isRigSmooth_of_isRigSmooth`, `Rig.isRigEtale_of_isRigEtale`), and both of those rest on
the single isomorphism `Rig.CompletedPolynomialPresentation.transportCochainComplexIso` of
Stacks 0GBX together with the elementary observation that a scalar annihilating the identity
of an object, or an `Ext` class out of it, does the same for an isomorphic object.

For the existential direction one needs an ideal of definition to exist.  For Tag 0GCU this is
part of the adicness hypothesis; for Tag 0GCI it follows from weak admissibility, since over a
Noetherian ring a weak ideal of definition is finitely generated and hence an ideal of
definition.

Because Tag 0GCU shows the two conditions it compares are equivalent, `RingHom.IsRigEtale` may
be taken to be either of them; it is the existential one, so that a witnessing ideal of
definition is immediately available, and the universally quantified form is recovered by
`RingHom.IsRigEtale.forall_idealOfDefinition`.  The topological hypotheses needed to pass
between the two are carried by that lemma rather than by the definition, which therefore makes
sense for any continuous homomorphism and states the source's condition literally.

## References

* [Stacks Project, Tag 0GAI](https://stacks.math.columbia.edu/tag/0GAI)
* [Stacks Project, Tag 0GAY](https://stacks.math.columbia.edu/tag/0GAY)
* [Stacks Project, Tag 0GCI](https://stacks.math.columbia.edu/tag/0GCI)
* [Stacks Project, Tag 0GCJ](https://stacks.math.columbia.edu/tag/0GCJ)
* [Stacks Project, Tag 0GCU](https://stacks.math.columbia.edu/tag/0GCU)
* [Stacks Project, Tag 0GCV](https://stacks.math.columbia.edu/tag/0GCV)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Rig

universe u v

attribute [local instance] HasDerivedCategory.standard

section Transfer

variable {C : Type*} [Category* C] [Preadditive C] {R : Type*} [Semiring R] [Linear R C]

/-- A scalar which annihilates the identity of an object annihilates the identity of every
isomorphic object. -/
public theorem smul_id_eq_zero_of_iso {Y Z : C} (e : Y ≅ Z) (r : R) (h : r • 𝟙 Y = 0) :
    r • 𝟙 Z = 0 := by
  have he : r • 𝟙 Z = e.inv ≫ (r • 𝟙 Y) ≫ e.hom := by
    rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, e.inv_hom_id]
  rw [he, h, Limits.zero_comp, Limits.comp_zero]

/-- A scalar which annihilates every morphism out of an object annihilates every morphism out
of an isomorphic object. -/
public theorem smul_eq_zero_of_iso {Y Z T : C} (e : Y ≅ Z) (r : R) (g : Z ⟶ T)
    (h : r • (e.hom ≫ g) = 0) : r • g = 0 := by
  have he : r • g = e.inv ≫ (r • (e.hom ≫ g)) := by
    rw [Linear.comp_smul, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  rw [he, h, Limits.comp_zero]

end Transfer

section Independence

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I J : Ideal A} {a b : ℕ}
  {X : CommAlgCat.{v} A}

omit [IsNoetherianRing A] in
/-- From `J ^ (b * c) ≤ I ^ c` for a pair of ideals with `J ^ b ≤ I`. -/
public theorem pow_mul_le_pow (hb : J ^ b ≤ I) (c : ℕ) : J ^ (b * c) ≤ I ^ c :=
  (pow_mul J b c).le.trans (Ideal.pow_right_mono hb c)

/-- Rig-étaleness over `(A, I)` transfers to rig-étaleness over `(A, J)` for a mutually
cofinal pair of ideals. -/
public theorem isRigEtale_of_isRigEtale (pI : IsAdicFiniteType I X)
    (pJ : IsAdicFiniteType J X) (ha : I ^ a ≤ J) (hb : J ^ b ≤ I)
    (h : IsRigEtale (AdicFiniteTypeAlgebra.mk' X pI)) :
    IsRigEtale (AdicFiniteTypeAlgebra.mk' X pJ) := by
  intro Q
  obtain ⟨c, hc⟩ := h (CompletedPolynomialPresentation.transport pI pJ Q ha hb)
  refine ⟨b * c, fun r hr ↦ ?_⟩
  exact smul_id_eq_zero_of_iso
    (DerivedCategory.Q.mapIso
      (CompletedPolynomialPresentation.transportCochainComplexIso pI pJ Q ha hb))
    _ (hc r (pow_mul_le_pow hb c hr))

/-- Rig-smoothness over `(A, I)` transfers to rig-smoothness over `(A, J)` for a mutually
cofinal pair of ideals. -/
public theorem isRigSmooth_of_isRigSmooth (pI : IsAdicFiniteType I X)
    (pJ : IsAdicFiniteType J X) (ha : I ^ a ≤ J) (hb : J ^ b ≤ I)
    (h : IsRigSmooth (AdicFiniteTypeAlgebra.mk' X pI)) :
    IsRigSmooth (AdicFiniteTypeAlgebra.mk' X pJ) := by
  obtain ⟨P, c, hc⟩ := h
  refine ⟨CompletedPolynomialPresentation.transport pJ pI P hb ha, b * c, fun N y r hr ↦ ?_⟩
  exact smul_eq_zero_of_iso
    (DerivedCategory.Q.mapIso
      (CompletedPolynomialPresentation.transportCochainComplexIso pJ pI P hb ha)).symm
    _ y (hc N _ r (pow_mul_le_pow hb c hr))

end Independence

section Statements

/-- A continuous homomorphism satisfying condition (6) of Tag 0GBW makes its target an object
of the category of Tag 0AL4, for every ideal of definition of the source. -/
public theorem isAdicFiniteType_of_finiteTypeAdicAlgebraForEveryIdeal
    {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    (φ : A →+* B) (hft : FiniteTypeAdicAlgebraForEveryIdeal φ)
    (I : Ideal A) (hI : TopologicalRing.IsIdealOfDefinition I) :
    letI : Algebra A B := φ.toAlgebra
    IsAdicFiniteType I (CommAlgCat.of A B) := by
  let _ : Algebra A B := φ.toAlgebra
  obtain ⟨-, hcomplete, hfin⟩ := hft I hI
  exact ⟨hcomplete, RingHom.finiteType_algebraMap.mp hfin⟩

/-- The target of a morphism satisfying condition (6) of Tag 0GBW, regarded as an adically
complete algebra of finite type for a chosen ideal of definition of the source. -/
public def adicFiniteTypeAlgebra
    {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    (φ : A →+* B) (hft : FiniteTypeAdicAlgebraForEveryIdeal φ)
    (I : Ideal A) (hI : TopologicalRing.IsIdealOfDefinition I) :
    AdicFiniteTypeAlgebra.{u, v} A I :=
  letI : Algebra A B := φ.toAlgebra
  AdicFiniteTypeAlgebra.mk' (CommAlgCat.of A B)
    (isAdicFiniteType_of_finiteTypeAdicAlgebraForEveryIdeal φ hft I hI)

/-- **Stacks Project, Tag 0GCI.** Rig-smoothness of a finite-type morphism of Noetherian
weakly admissible rings does not depend on the ideal of definition of its source. -/
@[stacks 0GCI]
public theorem isRigSmooth_iff_forall_idealOfDefinition
    {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (hA : TopologicalRing.IsWeaklyAdmissible A) (_hB : TopologicalRing.IsWeaklyAdmissible B)
    (φ : A →+* B) (_hφ : Continuous φ) (hft : FiniteTypeAdicAlgebraForEveryIdeal φ) :
    (∃ (I : Ideal A) (hI : TopologicalRing.IsIdealOfDefinition I),
      IsRigSmooth (adicFiniteTypeAlgebra φ hft I hI)) ↔
      (∀ (I : Ideal A) (hI : TopologicalRing.IsIdealOfDefinition I),
        IsRigSmooth (adicFiniteTypeAlgebra φ hft I hI)) := by
  refine ⟨fun ⟨I, hI, h⟩ J hJ ↦ ?_, fun h ↦
    (TopologicalRing.isPreAdmissible_of_isWeaklyPreAdmissible hA.1).imp fun I hI ↦ ⟨hI, h I hI⟩⟩
  obtain ⟨_, hIJ, hJI⟩ := hI.exists_pow_le_and_pow_le hJ
  exact isRigSmooth_of_isRigSmooth _ _ hIJ hJI h

end Statements

section RigEtaleOver

/-- Rig-étaleness of the algebra defined by a ring homomorphism over a specified ideal, with
the completeness and finite-type data required for the algebra object. -/
public abbrev IsRigEtaleOver {A : Type u} {B : Type v}
    [CommRing A] [IsNoetherianRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) : Prop :=
  letI : Algebra A B := φ.toAlgebra
  ∃ hc : IsAdicComplete (I.map (algebraMap A B)) B,
    ∃ hf : Algebra.FiniteType (A ⧸ I) (B ⧸ I.map (algebraMap A B)),
      letI : Algebra.FiniteType (A ⧸ I) (B ⧸ I.map (algebraMap A B)) := hf
      IsRigEtale (AdicFiniteTypeAlgebra.of (I := I) B hc)

/-- **Stacks Project, Tag 0GCU.** For an adic morphism of topologically finite type between
Noetherian adic rings, rig-étaleness over one ideal of definition is equivalent to
rig-étaleness over every ideal of definition. -/
@[stacks 0GCU]
public theorem rigEtaleOver_iff_forall_idealOfDefinition
    {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [IsNoetherianRing B]
    (φ : A →+* B) (_hφ : Continuous φ)
    (_hA : TopologicalRing.IsAdic A) (_hB : TopologicalRing.IsAdic B) :
    (FiniteTypeAdicAlgebraForEveryIdeal φ ∧
      ∃ I : Ideal A, TopologicalRing.IsIdealOfDefinition I ∧ IsRigEtaleOver φ I) ↔
    (FiniteTypeAdicAlgebraForEveryIdeal φ ∧
      ∀ I : Ideal A, TopologicalRing.IsIdealOfDefinition I → IsRigEtaleOver φ I) := by
  refine ⟨fun ⟨hft, I, hI, hc, hf, hrig⟩ ↦ ⟨hft, fun K hK ↦ ?_⟩, fun ⟨hft, h⟩ ↦
    let ⟨I, hI, _⟩ := _hA.1; ⟨hft, I, hI, h I hI⟩⟩
  obtain ⟨_, hIK, hKI⟩ := hI.exists_pow_le_and_pow_le hK
  have pK := isAdicFiniteType_of_finiteTypeAdicAlgebraForEveryIdeal φ hft K hK
  exact ⟨pK.1, pK.2, isRigEtale_of_isRigEtale ⟨hc, hf⟩ pK hIK hKI hrig⟩

end RigEtaleOver

end Rig

namespace RingHom

universe u v

/-- **Stacks Project, Tag 0GCJ.** A continuous homomorphism of Noetherian adic topological
rings is *rig-smooth* when it is adic of topologically finite type — condition (6) of Tag 0GBW
— and makes its target rig-smooth over some ideal of definition of its source.  By Tag 0GCI the
choice of that ideal is immaterial. -/
@[stacks 0GCJ]
public abbrev IsRigSmooth {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [IsNoetherianRing B]
    (φ : A →+* B) : Prop :=
  ∃ hft : Rig.FiniteTypeAdicAlgebraForEveryIdeal φ,
    ∃ (I : Ideal A) (hI : TopologicalRing.IsIdealOfDefinition I),
      Rig.IsRigSmooth (Rig.adicFiniteTypeAlgebra φ hft I hI)

/-- Rig-smoothness as a property of arrows of `WAdm^{Noeth}`, in the form the local-property
bundles of Tags 0ANI, 0GBG and 0GBK consume: a continuous homomorphism of topological rings is
rig-smooth in the sense of Tag 0GCJ once the source and target are Noetherian and linearly
topologized, which the objects of `WAdm^{Noeth}` are. -/
public abbrev IsRigSmoothArrow {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (φ : A →+* B) : Prop :=
  ∀ [IsLinearTopology A A] [IsLinearTopology B B] [IsNoetherianRing A] [IsNoetherianRing B],
    Continuous φ ∧ IsRigSmooth φ

/-- **Stacks Project, Tag 0GCV.** A continuous homomorphism of Noetherian adic topological
rings is *rig-étale* when it is adic of topologically finite type — condition (6) of Tag 0GBW
— and makes its target rig-étale over some ideal of definition of its source.  By Tag 0GCU the
choice of that ideal is immaterial. -/
@[stacks 0GCV]
public abbrev IsRigEtale {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [IsNoetherianRing B]
    (φ : A →+* B) : Prop :=
  Rig.FiniteTypeAdicAlgebraForEveryIdeal φ ∧
    ∃ I : Ideal A, TopologicalRing.IsIdealOfDefinition I ∧ Rig.IsRigEtaleOver φ I

/-- Rig-étaleness as a property of arrows of `WAdm^{Noeth}`, in the form the local-property
bundles of Tags 0ANI, 0GBG, 0GBK and 0GBP consume: a continuous homomorphism of topological
rings is rig-étale in the sense of Tag 0GCV once the source and target are Noetherian and
linearly topologized, which the objects of `WAdm^{Noeth}` are.  This is the exact analogue of
`RingHom.IsRigSmoothArrow`. -/
public abbrev IsRigEtaleArrow {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (φ : A →+* B) : Prop :=
  ∀ [IsLinearTopology A A] [IsLinearTopology B B] [IsNoetherianRing A] [IsNoetherianRing B],
    Continuous φ ∧ IsRigEtale φ

variable {A : Type u} {B : Type v}
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
  [IsNoetherianRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
  [IsNoetherianRing B]
  {φ : A →+* B}

/-- A rig-smooth homomorphism of Noetherian adic rings makes its target rig-smooth over
*every* ideal of definition of its source, by the equivalence of Tag 0GCI. -/
public theorem IsRigSmooth.forall_idealOfDefinition (h : IsRigSmooth φ) (hφ : Continuous φ)
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hB : TopologicalRing.IsWeaklyAdmissible B)
    (hft : Rig.FiniteTypeAdicAlgebraForEveryIdeal φ)
    (I : Ideal A) (hI : TopologicalRing.IsIdealOfDefinition I) :
    Rig.IsRigSmooth (Rig.adicFiniteTypeAlgebra φ hft I hI) := by
  obtain ⟨hft', hex⟩ := h
  exact (Rig.isRigSmooth_iff_forall_idealOfDefinition hA hB φ hφ hft').mp hex I hI

/-- A rig-étale homomorphism of Noetherian adic rings is rig-étale over *every* ideal of
definition of its source, by the equivalence of Tag 0GCU. -/
public theorem IsRigEtale.forall_idealOfDefinition (h : IsRigEtale φ) (hφ : Continuous φ)
    (hA : TopologicalRing.IsAdic A) (hB : TopologicalRing.IsAdic B)
    (I : Ideal A) (hI : TopologicalRing.IsIdealOfDefinition I) : Rig.IsRigEtaleOver φ I :=
  ((Rig.rigEtaleOver_iff_forall_idealOfDefinition φ hφ hA hB).mp h).2 I hI

/-- Rig-étaleness may be checked at any single ideal of definition of the source: the
condition of Tag 0GCV holds as soon as it holds for one such ideal. -/
public theorem isRigEtale_of_isRigEtaleOver
    (hft : Rig.FiniteTypeAdicAlgebraForEveryIdeal φ) (I : Ideal A)
    (hI : TopologicalRing.IsIdealOfDefinition I) (h : Rig.IsRigEtaleOver φ I) :
    IsRigEtale φ :=
  ⟨hft, I, hI, h⟩

end RingHom

end
