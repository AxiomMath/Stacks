module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineBaseProperDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineBaseSeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescentLimitFacts
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProperCriteria

/-!
# Stacks 0D1I: descent of proper flat families along affine limits

`StacksFrontier.AlgebraicGeometry.Quot.ProperFlatLimitPreservingReduction` reduces **Stacks 0D1I**,
limit preservation of the category fibred in groupoids `𝒮paces'_{fp,flat,proper}` of Stacks 0D1E,
to three geometric descent conditions at an affine cofiltered cone, and
`StacksFrontier.AlgebraicGeometry.Quot.ProperFlatMorphismDescent` discharges two of them. This file
discharges the remaining one. The tag itself is
`AlgebraicGeometry.isLimitPreserving_cartesianProperFlatFiberedCategory`, in
`StacksFrontier.AlgebraicGeometry.Quot.StackOfSpacesLimitPreservingUnconditional`.

The remaining condition is descent of *objects*: over the vertex of an affine cofiltered cone, a
finitely presented, flat and proper family of algebraic spaces is the base change of such a family
over a finite stage. Its proof is the conjunction of four descent statements, each already proved
unconditionally over an affine base with no bound on the index category:

* finite presentation descends — the essential-surjectivity half of the size-free **Stacks 07SK**,
  `AlgebraicGeometry.Space.exists_model_of_finitePresentation_affineBase`;
* separatedness descends — the size-free **Stacks 0851**,
  `AlgebraicGeometry.Space.exists_isSeparated_isPullback_of_isSeparated_limit`;
* properness descends — the size-free **Stacks 08K1**,
  `AlgebraicGeometry.Space.exists_isProper_isPullback_of_isProper_limit`;
* flatness descends — the size-free final sentence of **Stacks 08K0**,
  `AlgebraicGeometry.Space.exists_isFlat_isPullback_of_isFlat_limit`.

## Main results

* `AlgebraicGeometry.properFlatFamilyDescendsAlongAffineLimit`: the third and last geometric input
  of Stacks 0D1I, descent of objects, proved outright.

## Implementation notes

*The order of the four steps.* Finite presentation must come first: it is what produces a family
over a stage at all, and the other three statements descend a property of a family that is already
given at a stage. Among the remaining three, properness must come after separatedness, because
`AlgebraicGeometry.Space.exists_isProper_isPullback_of_isProper_limit` takes separatedness of the
family *at its starting stage* as a hypothesis — that is what Chow's lemma consumes — and the only
separatedness available at the outset is that of the family over the vertex, inherited from its
properness. Flatness is placed last, so that the order is

  finite presentation, separatedness, properness, flatness.

With this order exactly one property has to be carried across a later transition, namely
properness across the transition the flatness step produces, and that is
`AlgebraicGeometry.Space.isProper_pullback_fst`. Any other order needs at least two such transports
and no common upper bound in the index category has to be taken, so
`CategoryTheory.IsCofiltered.min` does not appear.

*Two pieces of bookkeeping, isolated as private lemmas.* Each of the three property-descent
statements hands back a family at a later stage together with an abstract cartesian square over the
transition, and the next step needs that family to be an admissible input again.
`AlgebraicGeometry.modelData_of_isPullback` transports algebraicity, finite presentation and
quasi-compactness of the source across such a square, and
`AlgebraicGeometry.isPullback_stage_of_isPullback` re-presents the family over the vertex as the
base change of the new stage family, which is `CategoryTheory.IsPullback.of_right'` applied to the
factorisation of the cone leg through the transition.

## Index universes

The condition discharged here, like the two discharged in
`StacksFrontier.AlgebraicGeometry.Quot.ProperFlatMorphismDescent`, quantifies over an index category
`I : Type v` with `Category.{w} I`, while the four size-free descent statements it rests on are
proved for `I : Type u` with `Category.{u} I`. It is therefore established at `v = w = u`, i.e. at
a *small* index category, the index universes at which Stacks 0D1I is registered. That is this
library's canonical form of a Stacks 07XL condition — the source's directed inverse systems of
affine schemes are sets — recorded in the "Index universes" note of
`StacksDraft.AlgebraicGeometry.Stacks.SetoidLimitPreserving` and followed by Stacks
0D43, `AlgebraicGeometry.isLimitPreservingPolarizedUnconditional`, which carries its tag at a small
index category for exactly this reason. It is not a weakening of the mathematical content.

## References

* [Stacks Project, Tag 0D1I](https://stacks.math.columbia.edu/tag/0D1I)
* [Stacks Project, Tag 0D1E](https://stacks.math.columbia.edu/tag/0D1E)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 0851](https://stacks.math.columbia.edu/tag/0851)
* [Stacks Project, Tag 08K0](https://stacks.math.columbia.edu/tag/08K0)
* [Stacks Project, Tag 08K1](https://stacks.math.columbia.edu/tag/08K1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

section OverComparison

variable {A : Type*} [Category* A] [HasPullbacks A]

/-- **An identification of a slice object with a chosen base change, read as a cartesian
square.** If `f : Z ⟶ T` is isomorphic, as an object of the slice over `T`, to the base change of
`Y : Over U` along `p : T ⟶ U` in the sense of `CategoryTheory.Over.pullback`, then `f` is the base
change of the structure morphism of `Y` along `p` in the sense of a cartesian square.

This is the shape in which the essential-surjectivity half of Stacks 07SK returns its model, and
the shape in which the three property-descent statements over an affine base consume it. -/
private theorem exists_isPullback_of_overIso {T U Z : A} {f : Z ⟶ T} (Y : Over U) (p : T ⟶ U)
    (e : Over.mk f ≅ (Over.pullback p).obj Y) :
    ∃ g : Z ⟶ Y.left, IsPullback g f Y.hom p := by
  have hw : (Over.forget T).map e.hom ≫ pullback.snd Y.hom p = f := by
    simpa only [Over.forget_map, Over.pullback_obj_hom, Over.mk_hom] using Over.w e.hom
  exact ⟨(Over.forget T).map e.hom ≫ pullback.fst Y.hom p,
    IsPullback.of_iso_pullback
      ⟨by rw [Category.assoc, pullback.condition, ← Category.assoc, hw]⟩
      ((Over.forget T).mapIso e) rfl hw⟩

end OverComparison

section StageModels

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The Yoneda image of an affine object of the big fppf site is an algebraic space. -/
private theorem isAlgebraicSpace_yoneda_affine (T : BigAffineFppf B S hS) :
    IsAlgebraicSpace B S hS (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj T)) :=
  isAlgebraicSpace_yoneda B S hS _

/-- A finitely presented family over the Yoneda image of an affine object of the big fppf site has
quasi-compact source. -/
private theorem isQuasiCompactSpace_of_isFinitePresentation_affine {T : BigAffineFppf B S hS}
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : Z ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj T)}
    (hf : Space.IsFinitePresentation B S hS f) : Space.IsQuasiCompactSpace B S hS Z :=
  Space.isQuasiCompactSpace_of_isFinitePresentation B S hS f (isAlgebraicSpace_yoneda_affine T)
    (Space.isQuasiCompactSpace_yoneda_of_isAffine B S hS _ T.property) hf

variable {I : Type u} [Category.{u} I] {D : I ⥤ BigAffineFppf B S hS}

/-- **The data a stage family must carry to be fed to the descent statements, and the family over
the vertex re-presented as its base change.** Let `fi` be a finitely presented family on an
algebraic space over the stage `i`, `fk` its base change along the transition `s : k ⟶ i`, and `f`
the base change of `fi` along the leg of the cone at `i`. Then `fk` is again a finitely presented
family on an algebraic space with quasi-compact source, and `f` is the base change of `fk` along the
leg of the cone at `k`.

Quasi-compactness of the source is read off finite presentation of `fk` over the affine stage, by
`isQuasiCompactSpace_of_isFinitePresentation_affine`. The cone leg at `i` factors
through the leg at `k` followed by the transition, so the square over the leg at `i` is the
horizontal paste of the one sought with the one presenting `fk`; the square sought is recovered by
`CategoryTheory.IsPullback.of_right'`. -/
private theorem modelData_of_isPullback {c : Cone D} {i k : I} (s : k ⟶ i)
    {Zi Zk Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {fi : Zi ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj i))}
    {fk : Zk ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj k))}
    {q : Zk ⟶ Zi}
    (hpb : IsPullback fk q
      (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map s))) fi)
    (hZi : IsAlgebraicSpace B S hS Zi)
    (hfpi : Space.IsFinitePresentation B S hS fi)
    {f : Z ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj c.pt)} {g : Z ⟶ Zi}
    (hsq : IsPullback g f fi
      (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i)))) :
    IsAlgebraicSpace B S hS Zk ∧ Space.IsFinitePresentation B S hS fk ∧
      Space.IsQuasiCompactSpace B S hS Zk ∧ ∃ g' : Z ⟶ Zk, IsPullback g' f fk
        (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app k))) := by
  have halgp : IsAlgebraicSpace B S hS
      (pullback (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map s))) fi) :=
    isAlgebraicSpace_pullback B S hS _ fi (isAlgebraicSpace_yoneda_affine (D.obj k)) hZi
      (isAlgebraicSpace_yoneda_affine (D.obj i))
  have halgk : IsAlgebraicSpace B S hS Zk := halgp.of_iso hpb.isoPullback.symm
  have hfpk : Space.IsFinitePresentation B S hS fk :=
    Space.IsFinitePresentation.of_isPullback B S hS halgk hZi
      (isAlgebraicSpace_yoneda_affine (D.obj k)) (isAlgebraicSpace_yoneda_affine (D.obj i))
      hpb.flip hfpi
  have hfac : yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app k)) ≫
      yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map s)) =
      yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, c.w s]
  rw [← hfac] at hsq
  exact ⟨halgk, hfpk, isQuasiCompactSpace_of_isFinitePresentation_affine hfpk,
    _, IsPullback.of_right' hsq hpb.flip⟩

end StageModels

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Descent of finitely presented, flat and proper families of algebraic spaces along an affine
cofiltered limit, at a small index category.** This is the third and last geometric input of
**Stacks 0D1I**, and it is proved outright here: over the vertex of a cofiltered cone of affine
objects of the big fppf site whose cone of underlying schemes is a limit, a finitely presented,
flat and proper algebraic space is the base change of such a one over a stage.

The four inputs are applied in the order: finite presentation (the size-free Stacks 07SK),
separatedness (the size-free Stacks 0851), properness (the size-free Stacks 08K1) and flatness
(the size-free Stacks 08K0). Separatedness of the family over the vertex, which starts the second
step, is the first conjunct of its properness; separatedness at the stage the second step produces
is what the third step requires of its starting family; and properness is carried across the last
transition by `AlgebraicGeometry.Space.isProper_pullback_fst`. See the "Implementation notes" of
the module docstring for why no other order does with one transport, and the "Index universes"
section for why the condition is established at `v = w = u`. -/
theorem properFlatFamilyDescendsAlongAffineLimit :
    ProperFlatFamilyDescendsAlongAffineLimit.{u, u, u} B S hS := by
  intro I _ _ D c hc Z hZalg f hfp hfl hpr
  -- (a) finite presentation descends: a finitely presented model at a stage `i`
  obtain ⟨i, Yi, hYialg, hYifp, ⟨e⟩⟩ :=
    Space.exists_model_of_finitePresentation_affineBase B S hS B.contains_terminal D c hc
      (Over.mk f) hZalg hfp
  obtain ⟨g₀, hsqi⟩ := exists_isPullback_of_overIso Yi
    (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) e
  -- (b) separatedness descends, from separatedness of the family over the vertex
  obtain ⟨k₁, s₁, Z₁, f₁, q₁, hpb₁, hsep₁⟩ :=
    Space.exists_isSeparated_isPullback_of_isSeparated_limit B S hS D hc i Yi.hom hYialg
      (isQuasiCompactSpace_of_isFinitePresentation_affine hYifp)
      hYifp.2.2 f _ hsqi.flip hpr.1
  obtain ⟨halg₁, hfp₁, hqc₁, g₁, hsq₁⟩ := modelData_of_isPullback s₁ hpb₁ hYialg hYifp hsqi
  -- (c) properness descends, with separatedness at the starting stage from (b)
  obtain ⟨k₂, s₂, Z₂, f₂, q₂, hpb₂, hpr₂⟩ :=
    Space.exists_isProper_isPullback_of_isProper_limit B S hS B.contains_terminal D hc k₁ f₁
      halg₁ hqc₁ (Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hfp₁.1)
      hsep₁ f g₁ hsq₁.flip hpr
  obtain ⟨halg₂, hfp₂, hqc₂, g₂, hsq₂⟩ := modelData_of_isPullback s₂ hpb₂ halg₁ hfp₁ hsq₁
  -- (d) flatness descends
  obtain ⟨k₃, s₃, Z₃, f₃, q₃, hpb₃, hfl₃⟩ :=
    Space.exists_isFlat_isPullback_of_isFlat_limit B S hS D hc k₂ f₂ halg₂ hqc₂ hfp₂.1 f g₂
      hsq₂.flip hfl
  obtain ⟨halg₃, hfp₃, -, g₃, hsq₃⟩ := modelData_of_isPullback s₃ hpb₃ halg₂ hfp₂ hsq₂
  -- properness is carried across the last transition, being stable under base change
  have hpr₃ : Space.IsProper B S hS f₃ := by
    rw [← hpb₃.isoPullback_hom_fst]
    exact (Space.isProper_isIso_comp_iff B S hS hpb₃.isoPullback.hom _).2
      (Space.isProper_pullback_fst B S hS halg₂ (isAlgebraicSpace_yoneda_affine (D.obj k₂))
        (isAlgebraicSpace_yoneda_affine (D.obj k₃)) f₂ _ hpr₂)
  exact ⟨k₃, Z₃, halg₃, f₃, g₃, hfp₃, hfl₃, hpr₃, hsq₃⟩

end AlgebraicGeometry

end
