module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSource.Precomposition
public import StacksFrontier.AlgebraicGeometry.Morphisms.SmoothMorphisms.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Comp
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties
public import StacksCore.Tactic.StacksAttribute

/-!
# The largest open locus of a source-local morphism property

Let `P` be a property of morphisms of schemes which is local on the source for the fppf,
syntomic, smooth, or étale topology. For a morphism `f : X ⟶ Y` there is a largest open
`W ⊆ X` such that the restriction of `f` to `W` has `P`, and this open commutes with
inverse image along a morphism of the corresponding class.

## Main definitions

* `AlgebraicGeometry.largestOpen` is the supremum of the opens of the source on which the
  restricted morphism has the property.

## Main results

* `AlgebraicGeometry.largestOpen_isGreatest_fppf`,
  `AlgebraicGeometry.largestOpen_isGreatest_syntomic`,
  `AlgebraicGeometry.largestOpen_isGreatest_smooth` and
  `AlgebraicGeometry.largestOpen_isGreatest_etale` state that this open is itself a locus for
  the property, and is the greatest such open.
* `AlgebraicGeometry.preimage_largestOpen_fppf`,
  `AlgebraicGeometry.preimage_largestOpen_syntomic`,
  `AlgebraicGeometry.preimage_largestOpen_smooth` and
  `AlgebraicGeometry.preimage_largestOpen_etale` state compatibility with inverse image along
  a morphism of the corresponding class.

## Implementation notes

The open itself does not depend on the topology, so it is defined once; the eight results
then cover the four choices of topology in the source separately, as the source lemma does.
In the fppf case the class of morphisms is flat and locally of finite presentation, not
necessarily quasi-compact, matching Mathlib's `AlgebraicGeometry.Scheme.fppfPrecoverage`.

Both halves are proved once, for an abstract precoverage `AlgebraicGeometry.Scheme.precoverage Q`
and the class `Q` defining it, in `largestOpen_isGreatest_aux` and `preimage_largestOpen_aux`.
The hypotheses of those two auxiliaries are exactly what the four topologies supply: that `Q`
contains the open immersions, that `Q`-morphisms are open maps, and — for the second — that `Q`
is stable under composition and base change. Stability under precomposition by a `Q`-morphism,
which the source takes from Tag 04QV, is *derived* rather than assumed: the pair consisting of
the given `Q`-morphism and the identity is a `Q`-covering of the target, because the identity is
an open immersion. That is `AlgebraicGeometry.precomp_of_precoverage`, imported from
`StacksFrontier.AlgebraicGeometry.Descent.LocalOnSource.Precomposition`, which is where Tag 04QV
lives; it is not restated here.

Locality on the source is Mathlib's
`CategoryTheory.MorphismProperty.IsLocalAtSource` for the corresponding precoverage.

## References

* [Stacks Project, Tag 0CEY](https://stacks.math.columbia.edu/tag/0CEY)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0CEY.** The largest open of the source of `f : X ⟶ Y` on which the
restriction of `f` has the property `P`, defined as the supremum of all opens `U` of `X` with
`P (U.ι ≫ f)`.

That this open is itself such a locus requires `P` to be local on the source for one of the
four topologies of the source lemma; see `largestOpen_isGreatest_fppf` and its variants. -/
@[stacks 0CEY "open locus"]
def largestOpen (P : MorphismProperty Scheme.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) : X.Opens :=
  sSup {U : X.Opens | P (U.ι ≫ f)}

/-- The greatest-element statement of Tag 0CEY, for the precoverage attached to a class `Q`
containing the open immersions. -/
private theorem largestOpen_isGreatest_aux (P Q : MorphismProperty Scheme.{u})
    (K : Precoverage Scheme.{u}) [P.IsLocalAtSource K]
    (hK : K = Scheme.precoverage Q)
    (hOpen : ∀ {A B : Scheme.{u}} (i : A ⟶ B), IsOpenImmersion i → Q i)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsGreatest {U : X.Opens | P (U.ι ≫ f)} (largestOpen P f) := by
  let S : Set X.Opens := {U | P (U.ι ≫ f)}
  let W : X.Opens := sSup S
  show IsGreatest S W
  refine ⟨?_, fun _ => le_sSup⟩
  let a : (i : S) → i.1.toScheme ⟶ W.toScheme := fun i => X.homOfLE (le_sSup i.2)
  have hcover : Presieve.ofArrows (fun i : S => i.1.toScheme) a ∈ K W.toScheme := by
    rw [hK, Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun i => hOpen (a i) inferInstance⟩
    obtain ⟨U, hU, hxU⟩ := TopologicalSpace.Opens.mem_sSup.mp x.2
    exact ⟨⟨U, hU⟩, ⟨x.1, hxU⟩, Subtype.ext (by simp [a])⟩
  apply MorphismProperty.IsLocalAtSource.of_forall_comp (P := P) (K := K) hcover
  rintro _ _ ⟨i⟩
  show P ((a i ≫ W.ι) ≫ f)
  rw [show a i ≫ W.ι = i.1.ι by simp [a]]
  exact i.2

/-- The inverse-image statement of Tag 0CEY, for the precoverage attached to a class `Q` which
contains the open immersions, consists of open maps, and is stable under composition and base
change. -/
private theorem preimage_largestOpen_aux (P Q : MorphismProperty Scheme.{u})
    (K : Precoverage Scheme.{u}) [P.IsLocalAtSource K]
    [Q.IsStableUnderComposition] [Q.IsStableUnderBaseChange]
    (hK : K = Scheme.precoverage Q)
    (hOpen : ∀ {A B : Scheme.{u}} (i : A ⟶ B), IsOpenImmersion i → Q i)
    (hOpenMap : ∀ {A B : Scheme.{u}} (g : A ⟶ B), Q g → IsOpenMap g)
    {X' X Y : Scheme.{u}} (g : X' ⟶ X) (hg : Q g) (f : X ⟶ Y) :
    g ⁻¹ᵁ largestOpen P f = largestOpen P (g ≫ f) := by
  have hPre : ∀ {A B C : Scheme.{u}} (a : A ⟶ B) (f : B ⟶ C), Q a → P f → P (a ≫ f) := by
    intro A B C a f' ha hf
    have hQ : P.IsLocalAtSource (Scheme.precoverage Q) := hK ▸ ‹P.IsLocalAtSource K›
    exact precomp_of_precoverage Q P hQ a f' ha (hOpen (𝟙 B) inferInstance) hf
  let W : X.Opens := largestOpen P f
  let W' : X'.Opens := largestOpen P (g ≫ f)
  have hW := largestOpen_isGreatest_aux P Q K hK hOpen f
  have hW' := largestOpen_isGreatest_aux P Q K hK hOpen (g ≫ f)
  apply le_antisymm
  · let A : X'.Opens := g ⁻¹ᵁ W
    let a : A.toScheme ⟶ W.toScheme := g ∣_ W
    have ha : Q a := MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_morphismRestrict g W).flip hg
    exact hW'.2 (by
      simpa [a, A, Category.assoc, morphismRestrict_ι] using hPre a (W.ι ≫ f) ha hW.1)
  · intro x hx
    let h : W'.toScheme ⟶ X := W'.ι ≫ g
    have hQh : Q h := MorphismProperty.comp_mem Q W'.ι g (hOpen W'.ι inferInstance) hg
    let U : X.Opens := ⟨Set.range h.base, (hOpenMap h hQh).isOpen_range⟩
    have hsub : Set.range h ⊆ Set.range U.ι := by simp [U]
    let q : W'.toScheme ⟶ U.toScheme := IsOpenImmersion.lift U.ι h hsub
    have hfac : q ≫ U.ι = h := IsOpenImmersion.lift_fac U.ι h hsub
    have hQq : Q q := MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsOpenImmersion.isPullback_lift_id h U.ι hsub).flip hQh
    have hqSurj : Function.Surjective q.base := by
      intro y
      obtain ⟨z, hz⟩ := y.property
      refine ⟨z, ?_⟩
      apply U.ι.isOpenEmbedding.injective
      calc
        U.ι (q z) = h z := by simpa using congrArg (fun k : W'.toScheme ⟶ X => k z) hfac
        _ = U.ι y := hz
    have hcov : Presieve.ofArrows (fun _ : Unit => W'.toScheme) (fun _ => q) ∈ K U.toScheme := by
      rw [hK, Scheme.ofArrows_mem_precoverage_iff]
      exact ⟨fun y => ⟨(), hqSurj y⟩, fun _ => hQq⟩
    have hPU : P (U.ι ≫ f) := by
      apply MorphismProperty.IsLocalAtSource.of_forall_comp (P := P) (K := K) hcov
      rintro Z b ⟨⟨⟩⟩
      rw [← Category.assoc, hfac]
      exact hW'.1
    exact (hW.2 hPU) ⟨⟨x, hx⟩, rfl⟩

/-- **Stacks Project, Tag 0CEY** for the fppf topology. For `P` local on the source in the fppf
topology, `largestOpen P f` is a locus for `P` and is the greatest open that is one. -/
@[stacks 0CEY "fppf largest locus"]
theorem largestOpen_isGreatest_fppf (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtSource Scheme.fppfPrecoverage] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsGreatest {U : X.Opens | P (U.ι ≫ f)} (largestOpen P f) :=
  largestOpen_isGreatest_aux P (@Flat ⊓ @LocallyOfFinitePresentation)
    Scheme.fppfPrecoverage rfl (fun _ _ => ⟨inferInstance, inferInstance⟩) f

/-- **Stacks Project, Tag 0CEY** for the syntomic topology. For `P` local on the source in the
syntomic topology, `largestOpen P f` is a locus for `P` and is the greatest open that is one. -/
@[stacks 0CEY "syntomic largest locus"]
theorem largestOpen_isGreatest_syntomic (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtSource (Scheme.precoverage (@Syntomic.{u}))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsGreatest {U : X.Opens | P (U.ι ≫ f)} (largestOpen P f) :=
  largestOpen_isGreatest_aux P (@Syntomic.{u})
    (Scheme.precoverage (@Syntomic.{u})) rfl (fun i _ => syntomic_of_isOpenImmersion i) f

/-- **Stacks Project, Tag 0CEY** for the smooth topology. For `P` local on the source in the
smooth topology, `largestOpen P f` is a locus for `P` and is the greatest open that is one. -/
@[stacks 0CEY "smooth largest locus"]
theorem largestOpen_isGreatest_smooth (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtSource (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u}))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsGreatest {U : X.Opens | P (U.ι ≫ f)} (largestOpen P f) :=
  largestOpen_isGreatest_aux P (@Smooth : MorphismProperty Scheme.{u})
    (Scheme.precoverage @Smooth) rfl (fun _ _ => inferInstance) f

/-- **Stacks Project, Tag 0CEY** for the étale topology. For `P` local on the source in the
étale topology, `largestOpen P f` is a locus for `P` and is the greatest open that is one. -/
@[stacks 0CEY "étale largest locus"]
theorem largestOpen_isGreatest_etale (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtSource Scheme.etalePrecoverage] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsGreatest {U : X.Opens | P (U.ι ≫ f)} (largestOpen P f) :=
  largestOpen_isGreatest_aux P (@Etale : MorphismProperty Scheme.{u})
    Scheme.etalePrecoverage rfl (fun _ _ => inferInstance) f

/-- **Stacks Project, Tag 0CEY** for the fppf topology: the largest locus of an fppf-local
property pulls back to the largest locus of the composite along a flat morphism locally of
finite presentation. -/
@[stacks 0CEY "fppf inverse image"]
theorem preimage_largestOpen_fppf (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtSource Scheme.fppfPrecoverage]
    {X' X Y : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y)
    [Flat g] [LocallyOfFinitePresentation g] :
    g ⁻¹ᵁ largestOpen P f = largestOpen P (g ≫ f) := by
  have : MorphismProperty.IsStableUnderComposition
    (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderComposition.inf
      (P := @Flat) (Q := @LocallyOfFinitePresentation)
  have : MorphismProperty.IsStableUnderBaseChange
    (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.inf
      (P := @Flat) (Q := @LocallyOfFinitePresentation)
  exact preimage_largestOpen_aux P (@Flat ⊓ @LocallyOfFinitePresentation)
    Scheme.fppfPrecoverage rfl (fun _ _ => ⟨inferInstance, inferInstance⟩)
    (fun i hi => by
      have : Flat i := hi.1
      have : LocallyOfFinitePresentation i := hi.2
      exact i.isOpenMap)
    g ⟨inferInstance, inferInstance⟩ f

/-- **Stacks Project, Tag 0CEY** for the syntomic topology: the largest locus of a
syntomic-local property pulls back to the largest locus of the composite along a syntomic
morphism. -/
@[stacks 0CEY "syntomic inverse image"]
theorem preimage_largestOpen_syntomic (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtSource (Scheme.precoverage (@Syntomic.{u}))]
    {X' X Y : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y) (hg : Syntomic g) :
    g ⁻¹ᵁ largestOpen P f = largestOpen P (g ≫ f) :=
  preimage_largestOpen_aux P (@Syntomic.{u})
    (Scheme.precoverage (@Syntomic.{u})) rfl (fun i _ => syntomic_of_isOpenImmersion i)
    (fun i hi => by
      have : Flat i := flat hi
      have : LocallyOfFinitePresentation i := locallyOfFinitePresentation hi
      exact i.isOpenMap)
    g hg f

/-- **Stacks Project, Tag 0CEY** for the smooth topology: the largest locus of a smooth-local
property pulls back to the largest locus of the composite along a smooth morphism. -/
@[stacks 0CEY "smooth inverse image"]
theorem preimage_largestOpen_smooth (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtSource (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u}))]
    {X' X Y : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y) [Smooth g] :
    g ⁻¹ᵁ largestOpen P f = largestOpen P (g ≫ f) :=
  preimage_largestOpen_aux P (@Smooth : MorphismProperty Scheme.{u})
    (Scheme.precoverage @Smooth) rfl (fun _ _ => inferInstance)
    (fun i _ => i.isOpenMap)
    g inferInstance f

/-- **Stacks Project, Tag 0CEY** for the étale topology: the largest locus of an étale-local
property pulls back to the largest locus of the composite along an étale morphism. -/
@[stacks 0CEY "étale inverse image"]
theorem preimage_largestOpen_etale (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtSource Scheme.etalePrecoverage]
    {X' X Y : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y) [Etale g] :
    g ⁻¹ᵁ largestOpen P f = largestOpen P (g ≫ f) := by
  have : MorphismProperty.IsStableUnderComposition @Etale :=
    ⟨fun f' g' hf hg => Etale.etale_comp g' (f := f')⟩
  exact preimage_largestOpen_aux P (@Etale : MorphismProperty Scheme.{u})
    Scheme.etalePrecoverage rfl (fun _ _ => inferInstance)
    (fun i _ => i.isOpenMap)
    g inferInstance f

end AlgebraicGeometry

end
