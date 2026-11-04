module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.ThickeningStage
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountableColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrum
public import StacksFrontier.RingTheory.Valuation.Domination
public import StacksFrontier.Topology.Algebra.AdicTopology.AdmissibleRings
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible

/-!
# A weak ideal of definition which is not an ideal of definition (Stacks 0CB8)

Let `(A, 𝔪, κ)` be a valuation ring which is `(π)`-adically complete for a nonzero `π ∈ 𝔪`
whose radical is `𝔪`, and assume that `𝔪` is not finitely generated. **Stacks 0CB8** observes
that `𝔪` is then a weak ideal of definition of `A`, that `A` is weakly admissible, that
`X = Spf A` is an affine formal algebraic space, and that the residue-field stage
`Spec κ ⟶ X` of its formal spectrum is a thickening — while `𝔪` is *not* an ideal of
definition. So the thickening `Spec κ ⟶ X` does not come from an ideal of definition, which is
the point of the example.

## Main results

* `isWeakIdealOfDefinition_maximalIdeal`: the maximal ideal is a weak ideal of definition, so
  the residue field is one of the quotient stages of the formal spectrum.
* `isWeaklyAdmissible`: such a ring is weakly admissible.
* `isAffineFormalAlgebraicSpace_formalSpectrum`: its formal spectrum is an affine formal
  algebraic space.
* `isRelativelyRepresentable_residueField` and `isThickening_residueField`: the residue-field
  stage maps to the formal spectrum by a representable morphism which is a thickening.
* `not_isIdealOfDefinition_maximalIdeal`: the maximal ideal is not an ideal of definition.

The union of these six statements is the content of the tag.

## Implementation notes

The affine-formal assertion does **not** go through
`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_formalSpectrum`, which assumes that
the ambient big fppf site contains the coproduct of *all* the quotient spectra
(`AlgebraicGeometry.FormalSpace.QuotientSystem.HasLargeSite`). Here no such hypothesis is
needed: the powers of `(π)` are cofinal among the weak ideals of definition, so the quotient
spectra of the powers form a *countable* cofinal subdiagram, and
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_countable_colimit` supplies the
set-theoretic condition of Stacks 0AIS for it. Cofinality is `CategoryTheory.Functor.Final` for
the functor `n ↦ (π)^(n+1)` into the weak ideals of definition ordered by reverse inclusion, and
the colimit is unchanged along it.

The residue field is the quotient of `A` by the weak ideal of definition `𝔪`, and the morphism
`Spec κ ⟶ Spf A` is the colimit cocone map at that stage, so the thickening assertion is the
stage statement `AlgebraicGeometry.FormalSpace.isThickening_colimitι` of Stacks 0AI9 transported
along the equivalence between the weak ideals of definition and their universe lift, which is
what the index of a presentation has to be. Being a thickening is phrased, as there, as the
relative morphism property of `Stacks.Thickenings.IsThickening` pulled back along
`AlgebraicGeometry.BigFppfOver.toScheme`; representability is recorded separately because
consumers use it on its own.

Three of the statements carry the weak ideal of definition `𝔪` in their type as an element of
the subtype `{I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I}`: that subtype is the
index of the diagram defining the formal spectrum, so this is what names the stage the
thickening is about.

Two private helpers here have counterparts elsewhere in the library that are not importable. That the transition
morphism between two quotient stages is a thickening is proved inline, for the same diagram, in
the proof of `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_formalSpectrum`, and
`StacksFrontier.Topology.Algebra.AdicTopology.PadicComplexInt` declares privately the converse of
the bridge `valuationRing_of_isValuationRing` between `IsValuationRing` and Mathlib's
`ValuationRing`. Extracting either would require refactoring those files.

## References

* [Stacks Project, Tag 0CB8](https://stacks.math.columbia.edu/tag/0CB8)
* [Stacks Project, Tag 0AMV](https://stacks.math.columbia.edu/tag/0AMV)
* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
* [Stacks Project, Tag 0AI9](https://stacks.math.columbia.edu/tag/0AI9)
* [Stacks Project, Tag 07E8](https://stacks.math.columbia.edu/tag/07E8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
open Filter
open scoped Topology

universe u

namespace AlgebraicGeometry.FormalSpace.WeakIdealOfDefinitionExample

/-- An element of the radical of an ideal defining an adic topology is topologically nilpotent:
some power of it lies in the ideal, hence all high powers of it lie in any prescribed power of
the ideal, and those powers are a fundamental system of neighbourhoods of zero. -/
private lemma isTopologicallyNilpotent_of_mem_radical
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A]
    (I : Ideal A) (x : A) (hadic : IsAdic I) (hx : x ∈ I.radical) :
    IsTopologicallyNilpotent x := by
  obtain ⟨N, hN⟩ := Ideal.mem_radical_iff.mp hx
  change Filter.Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0)
  refine Filter.tendsto_def.2 fun U hU => ?_
  obtain ⟨m, hm⟩ := (isAdic_iff.mp hadic).2 U hU
  have hbase : x ^ (N * m) ∈ I ^ m := by
    rw [pow_mul]
    exact Ideal.pow_mem_pow hN m
  exact Filter.eventually_atTop.2 ⟨N * m, fun k hk => hm ((I ^ m).pow_mem_of_pow_mem hbase hk)⟩

/-- In a local ring whose topology is `I`-adic for an ideal `I` with radical the maximal ideal,
the maximal ideal is open: it contains the open ideal `I`. -/
private lemma isOpen_maximalIdeal_of_isAdic
    {A : Type u} [CommRing A] [IsLocalRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A]
    (I : Ideal A) (hadic : IsAdic I) (hrad : I.radical = maximalIdeal A) :
    IsOpen (maximalIdeal A : Set A) := by
  apply Ideal.isOpen_of_isOpen_subideal (hrad ▸ Ideal.le_radical)
  simpa using (isAdic_iff.mp hadic).1 1

/-- The transition morphism of quotient spectra attached to an inclusion `L ⊆ J` of weak ideals
of definition is a thickening: the kernel of `A ⧸ L ⟶ A ⧸ J` is generated by the image of `J`,
whose elements are topologically nilpotent, hence nilpotent modulo the open ideal `L`. -/
@[ega "I 10.1.1" "partial"]
private lemma isThickening_specMap_quotientFactor
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {J L : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }}
    (hJL : L.1 ≤ J.1) :
    Stacks.Thickenings.IsThickening
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hJL))) := by
  let q := Ideal.Quotient.factor hJL
  have hker : RingHom.ker q ≤ nilradical (A ⧸ L.1) := by
    rw [Ideal.Quotient.factor_ker hJL]
    refine Ideal.map_le_iff_le_comap.mpr fun x hx => ?_
    rw [Ideal.mem_comap, mem_nilradical]
    obtain ⟨n, hn⟩ := (J.2.2 x hx).exists_pow_mem_of_mem_nhds
      (L.2.1.mem_nhds (Ideal.zero_mem L.1))
    refine ⟨n, ?_⟩
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hn
  have hqSurj : Function.Surjective q := Ideal.Quotient.factor_surjective hJL
  have hSpecSurj : Function.Surjective (PrimeSpectrum.comap q) := by
    intro p
    have hp : RingHom.ker q ≤ p.asIdeal := hker.trans (nilradical_le_prime p.asIdeal)
    refine ⟨⟨p.asIdeal.map q, Ideal.map_isPrime_of_surjective hqSurj hp⟩, ?_⟩
    apply PrimeSpectrum.ext
    change (p.asIdeal.map q).comap q = p.asIdeal
    rw [Ideal.comap_map_of_surjective q hqSurj p.asIdeal,
      ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hp]
  exact ⟨IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom q) hqSurj, hSpecSurj⟩

/-- The transition morphism of the quotient system along any morphism of weak ideals of
definition is a thickening. -/
private lemma isThickening_toScheme_map_diagram
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (D : QuotientSystem B S hS A)
    {i j : OrderDual { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }} (f : i ⟶ j) :
    Stacks.Thickenings.IsThickening
      ((BigAffineFppf.toScheme B S hS).map ((QuotientSystem.diagram D).map f)) := by
  have hJL : (OrderDual.ofDual j).1 ≤ (OrderDual.ofDual i).1 := leOfHom f
  change Stacks.Thickenings.IsThickening
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hJL)))
  exact isThickening_specMap_quotientFactor hJL

/-- The weak ideals of definition of a topological ring, ordered by reverse inclusion, are
directed: the intersection of two of them is again one, and it is larger than both for that
order. -/
private lemma isDirected_weakIdealOfDefinition {A : Type u} [CommRing A] [TopologicalSpace A] :
    IsDirected (OrderDual { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
      (· ≤ ·) :=
  ⟨fun i j => ⟨OrderDual.toDual ⟨i.1 ⊓ j.1,
    TopologicalRing.isWeakIdealOfDefinition_inf_of_isOpen_right i.2 j.2.1⟩,
    (inf_le_left : i.1 ⊓ j.1 ≤ i.1), (inf_le_right : i.1 ⊓ j.1 ≤ j.1)⟩⟩

/-- A local domain which is a valuation ring in the sense of domination of local subrings of its
fraction field is a valuation ring in Mathlib's sense: divisibility is total on it. -/
@[ega "II 7.1.1" "partial"]
private lemma valuationRing_of_isValuationRing
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] (hval : IsValuationRing A) :
    ValuationRing A := by
  let K := FractionRing A
  let f : A →+* K := algebraMap A K
  obtain ⟨V, hV⟩ := LocalSubring.isMax_iff.mp hval
  have hrange : V.toSubring = f.range := congrArg LocalSubring.toSubring hV
  have hmem (a : A) : f a ∈ V := by
    change f a ∈ V.toSubring
    rw [hrange]
    exact ⟨a, rfl⟩
  have hpre (c : V) : ∃ d, f d = c := by
    rw [← RingHom.mem_range, ← hrange]
    exact c.property
  have key (a b : A) (c : V) (h : (⟨f a, hmem a⟩ : V) * c = ⟨f b, hmem b⟩) :
      ∃ d, a * d = b := by
    obtain ⟨d, hd⟩ := hpre c
    have hEq : f a * (c : K) = f b := congrArg Subtype.val h
    rw [← hd] at hEq
    have hmap : f (a * d) = f b := by simpa only [map_mul] using hEq
    exact ⟨d, IsFractionRing.injective A K hmap⟩
  have _ : PreValuationRing A := ⟨fun a b => by
    obtain ⟨c, h | h⟩ := ValuationRing.cond (⟨f a, hmem a⟩ : V) ⟨f b, hmem b⟩
    · exact (key a b c h).imp fun _ => Or.inl
    · exact (key b a c h).imp fun _ => Or.inr⟩
  exact ⟨⟩

/-- The maximal ideal of a valuation ring is idempotent as soon as it is not finitely generated:
it is not principal, so for every `f ∈ 𝔪` there is `a ∈ 𝔪` not divisible by `f`, and by totality
of divisibility `f = a * b` with `b ∈ 𝔪`, whence `f ∈ 𝔪 ^ 2`. -/
private lemma maximalIdeal_sq_eq_of_not_fg
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    (hval : IsValuationRing A) (hnotfg : ¬ (maximalIdeal A).FG) :
    (maximalIdeal A) ^ 2 = maximalIdeal A := by
  have _ : ValuationRing A := valuationRing_of_isValuationRing A hval
  have hdvd : @Std.Total A (· ∣ ·) := ValuationRing.iff_dvd_total.mp inferInstance
  rw [pow_two]
  refine le_antisymm Ideal.mul_le_left fun f hf => ?_
  have hnotle : ¬ maximalIdeal A ≤ Ideal.span ({f} : Set A) := fun h =>
    hnotfg (le_antisymm h ((Ideal.span_singleton_le_iff_mem _).mpr hf) ▸
      Submodule.fg_span_singleton f)
  obtain ⟨a, ha, haf⟩ := Set.not_subset.mp hnotle
  obtain ⟨b, rfl⟩ := (hdvd.total a f).resolve_right fun hfa =>
    haf (Ideal.mem_span_singleton.mpr hfa)
  have hb : b ∈ maximalIdeal A := by
    by_contra hb
    exact haf (Ideal.mem_span_singleton.mpr
      ((IsLocalRing.notMem_maximalIdeal.mp hb).mul_right_dvd.mpr dvd_rfl))
  exact Ideal.mul_mem_mul ha hb

variable {A : Type u} [CommRing A] [IsLocalRing A]
  [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
  (π : A)

/-- **Stacks 0CB8.** In a local ring whose topology is `(π)`-adic, with the radical of `(π)` the
maximal ideal, the maximal ideal is a weak ideal of definition: it is open, and each of its
elements lies in the radical of `(π)`, hence is topologically nilpotent. -/
@[stacks 0CB8 "a weak ideal of definition that is not an ideal of definition"]
theorem isWeakIdealOfDefinition_maximalIdeal
    (hadic : IsAdic (Ideal.span ({π} : Set A)))
    (hrad : (Ideal.span ({π} : Set A)).radical = maximalIdeal A) :
    TopologicalRing.IsWeakIdealOfDefinition (maximalIdeal A) := by
  refine ⟨isOpen_maximalIdeal_of_isAdic _ hadic hrad, fun x hx =>
    isTopologicallyNilpotent_of_mem_radical _ x hadic ?_⟩
  simpa [hrad] using hx

/-- **Stacks 0CB8.** A complete local ring whose topology is `(π)`-adic, with the radical of
`(π)` the maximal ideal, is weakly admissible: the maximal ideal is a weak ideal of
definition. -/
@[stacks 0CB8 "a weak ideal of definition that is not an ideal of definition"]
theorem isWeaklyAdmissible
    (hadic : IsAdic (Ideal.span ({π} : Set A)))
    (hcomplete : TopologicalRing.IsComplete A)
    (hrad : (Ideal.span ({π} : Set A)).radical = maximalIdeal A) :
    TopologicalRing.IsWeaklyAdmissible A :=
  ⟨⟨maximalIdeal A, isWeakIdealOfDefinition_maximalIdeal π hadic hrad⟩,
    hcomplete.2, hcomplete.1⟩

/-- The formal spectrum of a ring whose topology is `M`-adic is an affine formal algebraic
space, with no hypothesis on the ambient site: the quotients by the powers of `M` are a
countable cofinal subdiagram of the quotients by all weak ideals of definition, so the
set-theoretic condition of Stacks 0AIS holds for a countable presentation. -/
private theorem isAffineFormalAlgebraicSpace_of_isAdic
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] (M : Ideal A) (hadic : IsAdic M)
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (D : QuotientSystem B S hS A) :
    IsAffineFormalAlgebraicSpace B S hS (formalSpectrum D) := by
  have _ : HasColimitsOfSize.{u + 1, u + 1}
      (Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))) :=
    Sheaf.instHasColimitsOfSize
  let I₀ := { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }
  let I := ULift.{u + 1} ℕ
  let q : I → I₀ := fun n =>
    ⟨M ^ (n.down + 1),
      ⟨(isAdic_iff.mp hadic).1 (n.down + 1), fun x hx =>
        isTopologicallyNilpotent_of_mem_radical M x hadic
          ((Ideal.pow_le_self (by omega) |>.trans Ideal.le_radical) hx)⟩⟩
  have _ : Nonempty I := ⟨ULift.up 0⟩
  have _ : IsDirected I (· ≤ ·) :=
    ⟨fun i j => ⟨ULift.up (max i.down j.down), le_max_left _ _, le_max_right _ _⟩⟩
  let F : I ⥤ OrderDual I₀ := {
    obj n := OrderDual.toDual (q n)
    map {n m} f := homOfLE (show q m ≤ q n from
      Ideal.pow_le_pow_right (Nat.add_le_add_right (show n ≤ m from leOfHom f) 1))
    map_id _ := Subsingleton.elim _ _
    map_comp _ _ := Subsingleton.elim _ _ }
  have hfinal : Functor.Final F := by
    refine Functor.final_of_exists_of_isFiltered F (fun J => ?_)
      fun _ _ => ⟨_, 𝟙 _, Subsingleton.elim _ _⟩
    let J₀ := OrderDual.ofDual J
    obtain ⟨n, hn⟩ := (isAdic_iff.mp hadic).2
      (J₀.1 : Set A) (J₀.2.1.mem_nhds (Ideal.zero_mem J₀.1))
    exact ⟨ULift.up n, ⟨homOfLE fun x hx => hn (Ideal.pow_le_pow_right (Nat.le_succ n) hx)⟩⟩
  let d := F ⋙ QuotientSystem.diagram D
  have hd : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening
        ((BigAffineFppf.toScheme B S hS).map (d.map f)) :=
    fun _ _ f => isThickening_toScheme_map_diagram D (F.map f)
  let K := formalSpectrumDiagram D
  exact ⟨satisfiesSetTheoreticCondition_of_countable_colimit B S hS d hd _
      ⟨(Functor.Final.colimitIso F K).symm⟩,
    I, inferInstance, inferInstance, inferInstance, d, hd, ⟨(Functor.Final.colimitIso F K).symm⟩⟩

/-- **Stacks 0CB8.** A complete local ring whose topology is `(π)`-adic, with the radical of
`(π)` the maximal ideal, has an affine formal algebraic space as formal spectrum, with no
hypothesis on the chosen big fppf site beyond its containing the quotient spectra.

Completeness and the radical identity are part of the situation of the example but are not
needed for this particular conclusion, which holds for any adic topology; their names are
therefore prefixed by an underscore. -/
@[stacks 0CB8 "a weak ideal of definition that is not an ideal of definition"]
theorem isAffineFormalAlgebraicSpace_formalSpectrum
    (hadic : IsAdic (Ideal.span ({π} : Set A)))
    (_hcomplete : TopologicalRing.IsComplete A)
    (_hrad : (Ideal.span ({π} : Set A)).radical = maximalIdeal A)
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (D : QuotientSystem B S hS A) :
    IsAffineFormalAlgebraicSpace B S hS (formalSpectrum D) :=
  isAffineFormalAlgebraicSpace_of_isAdic _ hadic D

/-- Every quotient stage of the formal spectrum maps to it by a morphism which is representable
by objects of the site and whose represented base changes are thickenings. This is the stage
statement of Stacks 0AI9 for the canonical presentation of the formal spectrum, transported
along the universe lift of the index of weak ideals of definition. -/
private theorem relativelyRepresentable_and_isThickening_formalSpectrumInclusion
    {A : Type u} [CommRing A] [TopologicalSpace A]
    (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (D : QuotientSystem B S hS A) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable
      (formalSpectrumInclusion D (OrderDual.toDual J)) ∧
    (MorphismProperty.relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)))
      (formalSpectrumInclusion D (OrderDual.toDual J)) := by
  have _ : HasColimitsOfSize.{u + 1, u + 1} (Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))) :=
    Sheaf.instHasColimitsOfSize
  let I₀ := { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }
  let I := ULift.{u + 1} (OrderDual I₀)
  let eOrder : OrderDual I₀ ≃o I :=
    { toEquiv := Equiv.ulift.symm, map_rel_iff' := Iff.rfl }
  let eI : OrderDual I₀ ≌ I := eOrder.equivalence
  have _ : Nonempty I := ⟨ULift.up (OrderDual.toDual J)⟩
  have _ : IsDirected I (· ≤ ·) := ⟨fun i j => by
    obtain ⟨k, hik, hjk⟩ :=
      (isDirected_weakIdealOfDefinition (A := A)).directed i.down j.down
    exact ⟨ULift.up k, hik, hjk⟩⟩
  let d₀ := QuotientSystem.diagram D
  let d := eI.inverse ⋙ d₀
  have hd : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening
        ((BigAffineFppf.toScheme B S hS).map (d.map f)) :=
    fun _ _ f => isThickening_toScheme_map_diagram D (eI.inverse.map f)
  let H := BigAffineFppf.inclusion B S hS
  let G := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let K₀ := formalSpectrumDiagram D
  let K := d ⋙ H ⋙ G
  have hw : eI.functor ⋙ K ≅ K₀ := by
    dsimp [K, K₀, d, d₀, H, G]
    exact Functor.isoWhiskerRight eI.unitIso.symm (d₀ ⋙ H ⋙ G)
  let eCol := HasColimit.isoOfEquivalence eI hw
  let j := OrderDual.toDual J
  let i : I := ULift.up j
  let eSrc : K.obj i ≅ K₀.obj j := K.mapIso (asIso (eI.counitInv.app i)) ≪≫ hw.app j
  let f : K.obj i ⟶ formalSpectrum D := colimit.ι K i ≫ eCol.symm.hom
  let g : K₀.obj j ⟶ formalSpectrum D := formalSpectrumInclusion D j
  have hcomm : eSrc.hom ≫ g = f := (HasColimit.ι_isoOfEquivalence_inv eI hw i).symm
  let hArrow : Arrow.mk f ≅ Arrow.mk g := Arrow.isoMk eSrc (Iso.refl _) hcomm
  exact ⟨(MorphismProperty.arrow_mk_iso_iff G.relativelyRepresentable hArrow).mp
      (relativelyRepresentable_colimitι B S hS d hd (formalSpectrum D) eCol.symm i),
    (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.relative G <|
      MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) hArrow).mp
      (isThickening_colimitι B S hS d hd (formalSpectrum D) eCol.symm i)⟩

/-- **Stacks 0CB8.** The residue-field stage `Spec κ ⟶ Spf A` of the formal spectrum, that is
the colimit cocone map at the weak ideal of definition `𝔪`, is representable by objects of the
big fppf site. -/
@[stacks 0CB8 "a weak ideal of definition that is not an ideal of definition"]
theorem isRelativelyRepresentable_residueField
    (hadic : IsAdic (Ideal.span ({π} : Set A)))
    (hrad : (Ideal.span ({π} : Set A)).radical = maximalIdeal A)
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (D : QuotientSystem B S hS A) :
    let J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I } :=
      ⟨maximalIdeal A, isWeakIdealOfDefinition_maximalIdeal π hadic hrad⟩
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable
      (formalSpectrumInclusion D (OrderDual.toDual J)) :=
  (relativelyRepresentable_and_isThickening_formalSpectrumInclusion
    ⟨maximalIdeal A, isWeakIdealOfDefinition_maximalIdeal π hadic hrad⟩ D).1

/-- **Stacks 0CB8.** The residue-field stage `Spec κ ⟶ Spf A` of the formal spectrum is a
thickening: each of its base changes along a morphism from a represented sheaf is a thickening
of schemes. -/
@[stacks 0CB8 "a weak ideal of definition that is not an ideal of definition"]
theorem isThickening_residueField
    (hadic : IsAdic (Ideal.span ({π} : Set A)))
    (hrad : (Ideal.span ({π} : Set A)).radical = maximalIdeal A)
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (D : QuotientSystem B S hS A) :
    let J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I } :=
      ⟨maximalIdeal A, isWeakIdealOfDefinition_maximalIdeal π hadic hrad⟩
    (MorphismProperty.relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)))
      (formalSpectrumInclusion D (OrderDual.toDual J)) :=
  (relativelyRepresentable_and_isThickening_formalSpectrumInclusion
    ⟨maximalIdeal A, isWeakIdealOfDefinition_maximalIdeal π hadic hrad⟩ D).2

omit [IsLinearTopology A A] in
/-- **Stacks 0CB8.** In a valuation ring whose topology is `(π)`-adic for some `π` in the
maximal ideal, the maximal ideal is not an ideal of definition if it is not finitely generated:
it is then idempotent, so all its powers coincide and cofinality of those powers would force
`𝔪 = (π)` to be principal. -/
@[stacks 0CB8 "a weak ideal of definition that is not an ideal of definition"]
theorem not_isIdealOfDefinition_maximalIdeal
    [IsDomain A] (hval : IsValuationRing A) (hπm : π ∈ maximalIdeal A)
    (hadic : IsAdic (Ideal.span ({π} : Set A)))
    (hnotfg : ¬ (maximalIdeal A).FG) :
    ¬ TopologicalRing.IsIdealOfDefinition (maximalIdeal A) := by
  intro hdef
  have hopen : IsOpen ((Ideal.span ({π} : Set A) : Ideal A) : Set A) := by
    simpa using (isAdic_iff.mp hadic).1 1
  obtain ⟨n, hn⟩ := hdef.2 _ (hopen.mem_nhds (Ideal.zero_mem _))
  have hpow : ∀ k : ℕ, (maximalIdeal A) ^ (k + 1) = maximalIdeal A := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ih, ← pow_two, maximalIdeal_sq_eq_of_not_fg A hval hnotfg]
  have hsub : maximalIdeal A ≤ Ideal.span ({π} : Set A) := fun _ hx =>
    hn (Ideal.pow_le_pow_right (Nat.le_succ n) ((hpow n).ge hx))
  exact hnotfg (le_antisymm hsub ((Ideal.span_singleton_le_iff_mem _).mpr hπm) ▸
    Submodule.fg_span_singleton π)

end AlgebraicGeometry.FormalSpace.WeakIdealOfDefinitionExample

end
