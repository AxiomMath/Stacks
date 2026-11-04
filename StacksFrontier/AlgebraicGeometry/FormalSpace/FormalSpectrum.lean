module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.PreservesLimits
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SetTheoreticColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The affine formal spectrum (Stacks 0AIF)

Let `S` be a scheme contained in a big fppf site `B` and let `A` be a weakly admissible
topological ring over `S`. **Stacks 0AIF** defines the *formal spectrum*

`Spf A = colim Spec (A ⧸ I)`,

the colimit over the weak ideals of definition `I ⊆ A`, taken in the fppf sheaves over `S`, and
records that the construction is contravariantly functorial in continuous ring maps over `S`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.QuotientSystem`: what it means for a topological ring to be a
  ring *over* `S` for this purpose — a structure morphism `Spec (A ⧸ I) ⟶ S` for each weak ideal
  of definition, compatible with the quotient maps, each `Spec (A ⧸ I)` lying in `B`.
* `AlgebraicGeometry.FormalSpace.formalSpectrum`: **Stacks 0AIF**, the construction.
* `AlgebraicGeometry.FormalSpace.ContinuousHom`: a continuous ring map over `S`.
* `AlgebraicGeometry.FormalSpace.formalSpectrumMap`: **Stacks 0AIF**, `Spf` of a continuous map.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_thickeningColimit_formalSpectrum`: the formal spectrum
  is a directed colimit of affine schemes over `S` along thickenings.
* `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_formalSpectrum`: the formal
  spectrum is an affine formal algebraic space over `S`.
* `AlgebraicGeometry.FormalSpace.existsUnique_formalSpectrumMap`: the induced map on formal
  spectra exists and is unique with its prescribed effect on every quotient stage.
* `AlgebraicGeometry.FormalSpace.formalSpectrumMap_id` and
  `AlgebraicGeometry.FormalSpace.formalSpectrumMap_comp`: `Spf` is a contravariant functor.

## Implementation notes

A topological ring over a possibly non-affine `S` has compatible maps from its quotient spectra
to `S` but need not have a map from `Spec A` itself, so the structure morphisms of the quotients
are the datum rather than a single morphism; that is what `QuotientSystem` records. Weak ideals
are ordered by reverse inclusion — the quotient grows as the ideal shrinks — so the quotient
spectra form a directed diagram, and its index is `OrderDual`. The colimit is taken in the sheaf
category, not in presheaves.

Two hypotheses deserve comment because they are *not* in the Stacks text.

The affine-formal-space statement asks additionally that the site contain the coproduct
`∐_I Spec (A ⧸ I)` (`QuotientSystem.HasLargeSite`). A site containing each quotient spectrum
need not contain a representable atlas for their colimit, and the set-theoretic condition of
Stacks 0AIS demands exactly such an atlas; `AlgebraicGeometry.FormalSpace` therefore gets it from
this hypothesis via `AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_colimit`.
Stacks can leave this implicit because its sites are indexed by a cutoff it is free to enlarge.
Only that one condition of Stacks 0AI7 needs it: the colimit-along-thickenings half holds for
every formal spectrum of a weakly admissible ring, and is
`AlgebraicGeometry.FormalSpace.exists_thickeningColimit_formalSpectrum`, which is what the
consumers that only factor a quasi-compact map through a stage — Stacks 0AIA, hence Stacks
0AN0 — are given instead.

Weak admissibility is not used in the *construction*, only in the functoriality: the
quotient-stage characterisation of `Spf φ` needs every weak ideal of definition of the source to
contain a weak ideal of definition pulled back from the target, which is where continuity and the
existence of a weak ideal of definition enter.

The transition morphisms of the canonical diagram are thickenings because an element of a weak
ideal of definition is topologically nilpotent, hence nilpotent modulo any smaller — therefore
open — ideal; this is the same argument that
`StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealPresentation` runs for Stacks 0AIC, and the
two presentations of this situation (`QuotientSystem` here,
`AlgebraicGeometry.FormalSpace.WeakIdealColimitPresentation` there) describe the same object from
the two directions: this file *builds* the colimit out of a ring, that one *recognises* a given
sheaf as such a colimit.

## References

* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
* [Stacks Project, Tag 0AMV](https://stacks.math.columbia.edu/tag/0AMV)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Filter

namespace AlgebraicGeometry.FormalSpace

universe u


private def isColimitCofanUliftYoneda
    {C : Type*} [Category C] (J : GrothendieckTopology C) [J.Subcanonical]
    {ι : Type*} (X : ι → C) {c : Cofan X}
    (hcov : Sieve.ofArrows X c.inj ∈ J c.pt) [∀ i, Mono (c.inj i)]
    (hempty : ∀ Y, IsInitial Y → ⊥ ∈ J Y)
    (hdisj : ∀ {i j} (_ : i ≠ j) {Y} (a : Y ⟶ X i) (b : Y ⟶ X j),
      a ≫ c.inj i = b ≫ c.inj j → Nonempty (IsInitial Y)) :
    IsColimit (Cofan.mk _ fun i => J.uliftYoneda.{u + 1}.map (c.inj i)) := by
  classical
  have hglue (s : Cofan fun i => J.uliftYoneda.{u + 1}.obj (X i)) :
      ∃! t : s.pt.obj.obj (Opposite.op c.pt),
        ∀ i, s.pt.obj.map (c.inj i).op t = J.uliftYonedaEquiv (s.inj i) := by
    apply (Presieve.isSheafFor_arrows_iff _ _).1
      ((Presieve.isSheafFor_iff_generate _).2 (s.pt.property.isSheafFor _ hcov))
    intro i j Y a b hab
    by_cases hij : i = j
    · subst j
      rw [(cancel_mono _).mp hab]
    · obtain ⟨hY⟩ := hdisj hij a b hab
      let := Types.isTerminalEquivUnique _ (Sheaf.isTerminalOfBotCover s.pt _ (hempty Y hY))
      exact Subsingleton.elim _ _
  refine Cofan.IsColimit.mk _
    (fun s => J.uliftYonedaEquiv.symm (hglue s).choose) ?_ ?_
  · intro s i
    apply J.uliftYonedaEquiv.injective
    change J.uliftYonedaEquiv (J.uliftYoneda.map (c.inj i) ≫
      J.uliftYonedaEquiv.symm (hglue s).choose) = _
    rw [← J.uliftYonedaEquiv_naturality, Equiv.apply_symm_apply]
    exact (hglue s).choose_spec.1 i
  · intro s m hm
    apply J.uliftYonedaEquiv.injective
    rw [Equiv.apply_symm_apply]
    apply (hglue s).choose_spec.2
    intro i
    rw [J.uliftYonedaEquiv_naturality]
    exact congrArg J.uliftYonedaEquiv (hm i)

private def over_initial_of_left_initial {C : Type*} [Category C]
    {S : C} (Y : Over S) (hY : IsInitial Y.left) : IsInitial Y := by
  letI : ∀ Z : Over S, Unique (Y ⟶ Z) := fun Z => {
    default := Over.homMk (hY.to Z.left) (hY.hom_ext _ _)
    uniq := fun f => by
      apply Over.OverMorphism.ext
      exact hY.hom_ext _ _ }
  exact IsInitial.ofUnique Y

attribute [local instance] sheaf_hasColimits

/-- The data making a topological ring a ring over `S` for the purposes of its
formal spectrum. Each quotient spectrum lies in the chosen big fppf site. -/
public structure QuotientSystem (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (A : Type u)
    [CommRing A] [TopologicalSpace A] where
  /-- For each weak ideal of definition `J`, the spectrum of `A ⧸ J` lies in the site `B`. -/
  inSite : ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
    B.Contains (Spec (.of (A ⧸ J.1)))
  /-- For each weak ideal of definition `J`, a structure morphism `Spec (A ⧸ J) ⟶ S`. -/
  overS : ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
    Spec (.of (A ⧸ J.1)) ⟶ S
  compatible : ∀ (J L : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
      (h : J.1 ≤ L.1),
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) ≫ overS J = overS L

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] [TopologicalSpace A]

private def weakIdealComapIntersection
    {C : Type u} [CommRing C] [TopologicalSpace C]
    [IsTopologicalRing A] [IsLinearTopology A A]
    (I : Ideal A) (hI : TopologicalRing.IsWeakIdealOfDefinition I)
    (f : A →+* C) (hf : Continuous f)
    (K : { I : Ideal C // TopologicalRing.IsWeakIdealOfDefinition I }) :
    { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I } :=
  ⟨I ⊓ Ideal.comap f K.1, by
    constructor
    · change IsOpen ((I : Set A) ∩ f ⁻¹' (K.1 : Set C))
      exact hI.1.inter (K.2.1.preimage hf)
    · intro x hx
      exact hI.2 x (Ideal.mem_inf.mp hx).1⟩

private theorem exists_weakIdeal_below_comap
    {C : Type u} [CommRing C] [TopologicalSpace C]
    [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A) (f : A →+* C)
    (hf : Continuous f)
    (K : { I : Ideal C // TopologicalRing.IsWeakIdealOfDefinition I }) :
    ∃ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ Ideal.comap f K.1 := by
  rcases hA.1 with ⟨I, hI⟩
  exact ⟨weakIdealComapIntersection I hI f hf K, inf_le_right⟩

private def weakIdealComapFunctor
    {C : Type u} [CommRing C] [TopologicalSpace C]
    [IsTopologicalRing A] [IsLinearTopology A A]
    (I : Ideal A) (hI : TopologicalRing.IsWeakIdealOfDefinition I)
    (f : A →+* C) (hf : Continuous f) :
    OrderDual { I : Ideal C // TopologicalRing.IsWeakIdealOfDefinition I } ⥤
      OrderDual { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I } where
  obj K := weakIdealComapIntersection I hI f hf K
  map {K L} g := homOfLE (by
    change I ⊓ Ideal.comap f L.1 ≤ I ⊓ Ideal.comap f K.1
    exact le_inf inf_le_left
      (inf_le_right.trans (Ideal.comap_mono (leOfHom g))))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The affine `S`-scheme attached to a weak ideal of definition. -/
public def QuotientSystem.stage (D : QuotientSystem B S hS A)
    (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :
    BigAffineFppf B S hS :=
  ⟨Over.mk (ObjectProperty.homMk (D.overS J) :
      B.obj (D.inSite J) ⟶ B.obj hS), by
    change IsAffine (Spec (.of (A ⧸ J.1)))
    infer_instance⟩

/-- The map of quotient spectra induced by an inclusion of weak ideals. -/
public def QuotientSystem.transition (D : QuotientSystem B S hS A)
    {J L : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }}
    (h : J.1 ≤ L.1) : D.stage L ⟶ D.stage J :=
  ObjectProperty.homMk <| Over.homMk (U := (D.stage L).1) (V := (D.stage J).1)
    (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))))
    (by apply ObjectProperty.hom_ext; exact D.compatible J L h)

/-- The diagram of affine quotient spectra indexed by weak ideals of definition
with the reverse inclusion order. -/
@[implicit_reducible] public def QuotientSystem.diagram (D : QuotientSystem B S hS A) :
    (OrderDual { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) ⥤
      BigAffineFppf B S hS where
  obj J := D.stage J
  map {J L} f := D.transition (leOfHom f)
  map_id J := by
    ext
    change Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.factor (leOfHom (𝟙 J)))) = 𝟙 _
    simp [Ideal.Quotient.factor_eq]
  map_comp {X Y Z} f g := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.factor (show X ≤ Z from leOfHom (f ≫ g)))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (show X ≤ Y from leOfHom f))) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
          (show Y ≤ Z from leOfHom g)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (Ideal.Quotient.factor_comp (leOfHom g) (leOfHom f)).symm

/-- The represented diagram of quotient spectra. -/
public abbrev formalSpectrumDiagram (D : QuotientSystem B S hS A) :=
  D.diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
    Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)

/-- The canonical cocone map from a quotient stage to the formal spectrum. -/
public abbrev formalSpectrumInclusion (D : QuotientSystem B S hS A)
    (J : OrderDual { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :
    (formalSpectrumDiagram D).obj J ⟶ colimit (formalSpectrumDiagram D) :=
  colimit.ι (formalSpectrumDiagram D) J

/-- The formal spectrum of a weakly admissible topological ring over `S`: the
fppf-sheaf colimit of its quotient spectra by weak ideals of definition. -/
@[stacks 0AIF "construction"]
public def formalSpectrum (D : QuotientSystem B S hS A) :
    Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)) :=
  colimit (formalSpectrumDiagram D)

/-- A big fppf site large enough to contain a single affine-formal-spectrum
atlas built from all the weak quotient spectra. -/
public abbrev QuotientSystem.HasLargeSite (_D : QuotientSystem B S hS A) : Prop :=
  B.Contains (∐ (fun J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I } ↦
    Spec (.of (A ⧸ J.1))))

/-- The transition morphisms of the canonical diagram of quotient spectra are thickenings: an
element of a weak ideal of definition is topologically nilpotent, hence nilpotent modulo any
smaller — therefore open — ideal, so the kernel of `A ⧸ L → A ⧸ J` lies in the nilradical and
the closed immersion `Spec (A ⧸ J) → Spec (A ⧸ L)` is surjective. -/
@[ega "I 10.7.4" "special case"]
public theorem QuotientSystem.isThickening_map_diagram
    [IsTopologicalRing A] [IsLinearTopology A A] (D : QuotientSystem B S hS A)
    {i j : OrderDual { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }}
    (f : i ⟶ j) :
    Stacks.Thickenings.IsThickening
      ((BigAffineFppf.toScheme B S hS).map (D.diagram.map f)) := by
  classical
  let J₁ : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I } := OrderDual.ofDual i
  let L₁ : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I } := OrderDual.ofDual j
  have hJL : L₁.1 ≤ J₁.1 := leOfHom f
  let q := Ideal.Quotient.factor hJL
  have hker : RingHom.ker q ≤ nilradical (A ⧸ L₁.1) := by
    rw [Ideal.Quotient.factor_ker hJL]
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    rw [Ideal.mem_comap, mem_nilradical]
    obtain ⟨n, hn⟩ := (J₁.2.2 x hx).exists_pow_mem_of_mem_nhds
      (L₁.2.1.mem_nhds (Ideal.zero_mem L₁.1))
    refine ⟨n, ?_⟩
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hn
  have hqSurj : Function.Surjective q := Ideal.Quotient.factor_surjective hJL
  have hSpecSurj : Function.Surjective (PrimeSpectrum.comap q) := by
    intro p
    let p' : PrimeSpectrum (A ⧸ J₁.1) :=
      ⟨p.asIdeal.map q,
        Ideal.map_isPrime_of_surjective hqSurj
          (hker.trans (nilradical_le_prime p.asIdeal))⟩
    refine ⟨p', ?_⟩
    apply PrimeSpectrum.ext
    show (p.asIdeal.map q).comap q = p.asIdeal
    rw [Ideal.comap_map_of_surjective q hqSurj p.asIdeal,
      ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr (hker.trans (nilradical_le_prime p.asIdeal))]
  let _ : Surjective (Spec.map (CommRingCat.ofHom q)) := ⟨hSpecSurj⟩
  have hclosed : IsClosedImmersion (Spec.map (CommRingCat.ofHom q)) :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom q) hqSurj
  show Stacks.Thickenings.IsThickening (Spec.map (CommRingCat.ofHom q))
  exact ⟨hclosed, Scheme.Hom.surjective _⟩

/-- Weak ideals of definition, ordered by reverse inclusion, indexed by `ULift (u + 1)`. -/
private def weakIdealUliftEquivalence (A : Type u) [CommRing A] [TopologicalSpace A] :
    OrderDual { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I } ≌
      ULift.{u + 1} (OrderDual { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :=
  OrderIso.equivalence { toEquiv := Equiv.ulift.symm, map_rel_iff' := Iff.rfl }

/-- The canonical diagram of quotient spectra, reindexed by `weakIdealUliftEquivalence`. -/
private def liftedDiagram (D : QuotientSystem B S hS A) :
    ULift.{u + 1} (OrderDual { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) ⥤
      BigAffineFppf B S hS :=
  (weakIdealUliftEquivalence A).inverse ⋙ D.diagram

private theorem isThickening_map_liftedDiagram
    [IsTopologicalRing A] [IsLinearTopology A A] (D : QuotientSystem B S hS A)
    ⦃i j : ULift.{u + 1} (OrderDual { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })⦄
    (f : i ⟶ j) :
    Stacks.Thickenings.IsThickening
      ((BigAffineFppf.toScheme B S hS).map ((liftedDiagram D).map f)) :=
  D.isThickening_map_diagram ((weakIdealUliftEquivalence A).inverse.map f)

/-- The intersection of two weak ideals of definition. -/
private def weakIdealInf (J J' : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :
    { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I } :=
  ⟨J.1 ⊓ J'.1, ⟨J.2.1.inter J'.2.1, fun x hx => J.2.2 x hx.1⟩⟩

private theorem isDirected_uliftWeakIdeal :
    IsDirected
      (ULift.{u + 1} (OrderDual { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }))
      (· ≤ ·) :=
  ⟨fun i j => ⟨ULift.up (weakIdealInf i.down j.down),
    (inf_le_left : i.down.1 ⊓ j.down.1 ≤ i.down.1),
    (inf_le_right : i.down.1 ⊓ j.down.1 ≤ j.down.1)⟩⟩

private theorem nonempty_uliftWeakIdeal [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A) :
    Nonempty
      (ULift.{u + 1} (OrderDual { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })) :=
  ⟨ULift.up ⟨hA.1.choose, hA.1.choose_spec⟩⟩

private theorem nonempty_iso_colimit_liftedDiagram (D : QuotientSystem B S hS A) :
    Nonempty (formalSpectrum D ≅ colimit (liftedDiagram D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) :=
  ⟨HasColimit.isoOfEquivalence (weakIdealUliftEquivalence A)
    (Functor.isoWhiskerRight (weakIdealUliftEquivalence A).unitIso.symm
      (D.diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))⟩

/-- **The colimit half of Stacks 0AI7 for a formal spectrum, with no condition on the site.**
The formal spectrum of a weakly admissible topological ring over `S` is a directed colimit of
affine schemes over `S` along thickenings, namely its canonical diagram of quotient spectra
with the index lifted to the universe in which such presentations are indexed. The size
condition `AlgebraicGeometry.FormalSpace.QuotientSystem.HasLargeSite` is needed only for the
set-theoretic condition of Stacks 0AIS, not for this. -/
public theorem exists_thickeningColimit_formalSpectrum
    [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A) :
    ∃ (I : Type (u + 1)) (pre : Preorder I),
      letI : Preorder I := pre
      Nonempty I ∧ IsDirected I (· ≤ ·) ∧
        ∃ D' : I ⥤ BigAffineFppf B S hS,
          (∀ ⦃i j : I⦄ (f : i ⟶ j),
            Stacks.Thickenings.IsThickening
              ((BigAffineFppf.toScheme B S hS).map (D'.map f))) ∧
            Nonempty (formalSpectrum D ≅ colimit (D' ⋙ BigAffineFppf.inclusion B S hS ⋙
              Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) := by
  exact ⟨_, _, nonempty_uliftWeakIdeal hA, isDirected_uliftWeakIdeal, liftedDiagram D,
    isThickening_map_liftedDiagram D, nonempty_iso_colimit_liftedDiagram D⟩

/-- The formal spectrum is affine as a formal algebraic space over the base. -/
@[stacks 0AIF "affine formal algebraic space"]
public theorem isAffineFormalAlgebraicSpace_formalSpectrum
    [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (D : QuotientSystem B S hS A) (hB : D.HasLargeSite) :
    IsAffineFormalAlgebraicSpace B S hS (formalSpectrum D) := by
  classical
  let J := BigFppfOver.topology B S hS
  let I₀ := { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }
  let I := ULift.{u + 1} (OrderDual I₀)
  have : Nonempty I := nonempty_uliftWeakIdeal hA
  have : IsDirected I (· ≤ ·) := isDirected_uliftWeakIdeal
  let d := liftedDiagram D
  have hX := nonempty_iso_colimit_liftedDiagram D
  let weakIndex : I → I₀ := fun i => OrderDual.ofDual i.down
  let eIndex : I ≃ I₀ := {
    toFun := weakIndex
    invFun := fun i => ULift.up (OrderDual.toDual i)
    left_inv := by intro i; cases i; rfl
    right_inv := by intro i; rfl }
  let X : I → Scheme.{u} := fun i => Spec (.of (A ⧸ (weakIndex i).1))
  let X₀ : I₀ → Scheme.{u} := fun i => Spec (.of (A ⧸ i.1))
  let : Small.{u} I := Small.mk' (Equiv.ulift : I ≃ OrderDual I₀)
  let eScheme : (∐ X₀) ≅ ∐ X := (Sigma.reindex eIndex X₀).symm
  have hSite : B.Contains (∐ X) := by
    show (∐ X).size < B.cutoff
    rw [← Scheme.size_congr eScheme]
    exact hB
  let U : BigFppfOver B S hS :=
    Over.mk (B.inclusion.preimage (X := B.obj hSite) (Y := B.obj hS)
      (show B.inclusion.obj (B.obj hSite) ⟶ B.inclusion.obj (B.obj hS) from
        Sigma.desc (f := X) fun i => D.overS (weakIndex i)))
  let Xsite : I → BigFppfOver B S hS := fun i =>
    (BigAffineFppf.inclusion B S hS).obj (d.obj i)
  let c : Cofan Xsite := Cofan.mk U fun i =>
    Over.homMk (B.inclusion.preimage (X := (Xsite i).left) (Y := U.left)
      (show B.inclusion.obj (Xsite i).left ⟶ B.inclusion.obj U.left from Sigma.ι X i)) (by
        apply B.inclusion.map_injective
        rw [B.inclusion.map_comp, B.inclusion.map_preimage]
        show Sigma.ι X i ≫ B.inclusion.map
          (B.inclusion.preimage (X := B.obj hSite) (Y := B.obj hS)
            (Sigma.desc (f := X) fun i => D.overS (weakIndex i))) = D.overS (weakIndex i)
        exact (congrArg (fun t => Sigma.ι X i ≫ t) (B.inclusion.map_preimage _)).trans
          (Sigma.ι_desc (f := X) (fun i => D.overS (weakIndex i)) i))
  let E : Covering B.Schemes := ⟨B.obj hSite, {
    I₀ := I
    X := fun i => B.obj (D.inSite (weakIndex i))
    f := fun i => B.inclusion.preimage (X := B.obj (D.inSite (weakIndex i)))
      (Y := B.obj hSite) (show B.inclusion.obj (B.obj (D.inSite (weakIndex i))) ⟶
        B.inclusion.obj (B.obj hSite) from Sigma.ι X i) }⟩
  have hEfp : IsFppfCovering E := by
    show E.2.presieve₀ ∈ Scheme.fppfPrecoverage.comap B.inclusion E.1
    rw [Precoverage.mem_comap_iff]
    have hsigma : (AlgebraicGeometry.sigmaOpenCover X).presieve₀ ∈
        Scheme.fppfPrecoverage (∐ X) :=
      Scheme.zariskiPrecoverage_le_fppfPrecoverage _
        (AlgebraicGeometry.sigmaOpenCover X).mem₀
    have hpres : (AlgebraicGeometry.sigmaOpenCover X).presieve₀ =
        Presieve.ofArrows (fun i => B.inclusion.obj (E.2.X i))
          (fun i => B.inclusion.map (E.2.f i)) := by
      show Presieve.ofArrows X (Sigma.ι X) = _
      dsimp only [E]
      simp only [B.inclusion.map_preimage]
      rfl
    have hmap : E.2.presieve₀.map B.inclusion =
        Presieve.ofArrows (fun i => B.inclusion.obj (E.2.X i))
          (fun i => B.inclusion.map (E.2.f i)) := by
      simp [PreZeroHypercover.presieve₀, Presieve.map_ofArrows]
    have hpres' : (AlgebraicGeometry.sigmaOpenCover X).presieve₀ =
        E.2.presieve₀.map B.inclusion := hpres.trans hmap.symm
    show E.2.presieve₀.map B.inclusion ∈ Scheme.fppfPrecoverage (∐ X)
    rw [← hpres']
    exact hsigma
  obtain ⟨E', hE', hComb⟩ := B.fppf_has_representative E hEfp
  rcases E' with ⟨E't, E'fam⟩
  change (∃ hTarget : E.1 = E't,
    PreZeroHypercover.CombinatoriallyEquivalent (hTarget ▸ E.2) E'fam) at hComb
  rcases hComb with ⟨hTarget, hComb⟩
  cases hTarget
  have hE'cover : Sieve.generate E'fam.presieve₀ ∈ B.topology E.1 := by
    exact Precoverage.generate_mem_toGrothendieck
      (show E'fam.presieve₀ ∈ B.precoverage E.1 from ⟨E'fam, rfl, hE'⟩)
  have hEcover : Sieve.generate E.2.presieve₀ ∈ B.topology E.1 := by
    rw [PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hComb]
    exact hE'cover
  have hcov : Sieve.ofArrows Xsite c.inj ∈ J U := by
    show Sieve.overEquiv U (Sieve.ofArrows Xsite c.inj) ∈ B.topology U.left
    show Sieve.functorPushforward (Over.forget (B.obj hS))
      (Sieve.ofArrows Xsite c.inj) ∈ B.topology U.left
    rw [Sieve.functorPushforward_ofArrows]
    exact hEcover
  let : B.topology.Subcanonical := BigFppfSite.subcanonical_topology B
  let : J.Subcanonical := by
    show (B.topology.over (B.obj hS)).Subcanonical
    infer_instance
  let eH : J.uliftYoneda.{u + 1} ≅ Sheaf.sheafifiedYoneda J :=
    (Functor.isoWhiskerLeft J.uliftYoneda
      (sheafificationNatIso.{u, u + 1, u + 1, u + 2} J (Type (u + 1)))) ≪≫
      Functor.isoWhiskerRight J.uliftYonedaCompSheafToPresheaf
        (presheafToSheaf J (Type (u + 1)))
  have hempty : ∀ (Y : BigFppfOver B S hS), IsInitial Y → ⊥ ∈ J Y := by
    intro Y hY
    let E₀ : PreZeroHypercover Y.left := PreZeroHypercover.empty Y.left
    let hEmptyTarget : B.Contains (∅ : Scheme.{u}) := by
      show (∅ : Scheme.{u}).size < B.cutoff
      have hsize : (∅ : Scheme.{u}).size ≤ Cardinal.aleph0 := by
        unfold Scheme.size
        refine max_le le_rfl (max_le ?_ (ciSup_le' fun U => ?_))
        · have : Subsingleton (∅ : Scheme.{u}).affineOpens :=
            ⟨fun _ _ => Subtype.ext
              (TopologicalSpace.Opens.ext (by ext x; exact isEmptyElim x))⟩
          exact (Cardinal.le_one_iff_subsingleton.mpr this).trans Cardinal.one_le_aleph0
        · have : Subsingleton Γ((∅ : Scheme.{u}), U.1) := inferInstance
          exact (Cardinal.le_one_iff_subsingleton.mpr this).trans Cardinal.one_le_aleph0
      exact lt_of_le_of_lt hsize B.aleph0_lt_cutoff
    let emptyOver : BigFppfOver B S hS :=
      Over.mk (B.inclusion.preimage (X := B.obj hEmptyTarget) (Y := B.obj hS)
        (Scheme.emptyTo (B.inclusion.obj (B.obj hS))))
    have hEmptyLeft : IsInitial (B.obj hEmptyTarget) := by
      apply IsInitial.isInitialOfObj B.inclusion (B.obj hEmptyTarget)
      exact AlgebraicGeometry.emptyIsInitial
    have hEmptyOver : IsInitial emptyOver :=
      over_initial_of_left_initial emptyOver hEmptyLeft
    let e : Y ≅ emptyOver := hY.uniqueUpToIso hEmptyOver
    let eScheme : B.inclusion.obj Y.left ≅ (∅ : Scheme.{u}) :=
      B.inclusion.mapIso ((Over.forget (B.obj hS)).mapIso e)
    have : IsEmpty (B.inclusion.obj Y.left) := eScheme.hom.base.hom.1.isEmpty
    have hE₀ : B.IsCovering ⟨Y.left, E₀⟩ := by
      constructor
      · show E₀.presieve₀ ∈ Scheme.fppfPrecoverage.comap B.inclusion Y.left
        rw [Precoverage.mem_comap_iff, PreZeroHypercover.presieve₀_empty]
        simpa [Scheme.fppfPrecoverage] using
          (Scheme.bot_mem_precoverage
            (@Flat ⊓ @LocallyOfFinitePresentation) (B.inclusion.obj Y.left))
      · simp [E₀, PreZeroHypercover.empty]
    have hbot : ⊥ ∈ B.topology Y.left := by
      have hgen : Sieve.generate E₀.presieve₀ ∈ B.precoverage.toGrothendieck Y.left :=
        Precoverage.generate_mem_toGrothendieck
          (show E₀.presieve₀ ∈ B.precoverage Y.left from ⟨E₀, rfl, hE₀⟩)
      simpa [E₀, PreZeroHypercover.presieve₀_empty] using hgen
    show Sieve.overEquiv Y ⊥ ∈ B.topology Y.left
    simpa [Sieve.overEquiv] using hbot
  have hcUlift : IsColimit (Cofan.mk (J.uliftYoneda.{u + 1}.obj U)
      (fun i => J.uliftYoneda.{u + 1}.map (c.inj i))) :=
    let : ∀ i, Mono (c.inj i) := fun i => by
      have hleft : Mono ((c.inj i).left) := by
        apply Functor.mono_of_mono_map B.inclusion
        let ιi : B.inclusion.obj (Xsite i).left ⟶ B.inclusion.obj U.left := Sigma.ι X i
        have : Small.{u} ((Set.range (fun _ : Unit => i))ᶜ : Set I) :=
          small_of_injective Subtype.val_injective
        have hιi : Mono ιi := by
          dsimp only [ιi]
          exact MonoCoprod.mono_ι X i
        have hmap : B.inclusion.map (B.inclusion.preimage ιi) = ιi :=
          B.inclusion.map_preimage ιi
        show Mono (B.inclusion.map (B.inclusion.preimage ιi))
        rw [hmap]
        exact hιi
      exact Over.mono_of_mono_left _
    isColimitCofanUliftYoneda J Xsite (c := c) hcov hempty (by
      intro i j hij Y a b hab
      have hinitScheme : IsInitial (B.inclusion.obj Y.left) := by
        apply IsInitial.ofCoproductDisjointOfCommSq hij
          (coproductIsCoproduct X) (B.inclusion.map a.left) (B.inclusion.map b.left)
        show B.inclusion.map a.left ≫ Sigma.ι X i =
          B.inclusion.map b.left ≫ Sigma.ι X j
        have heq : B.inclusion.map (a.left ≫ B.inclusion.preimage
              (X := (Xsite i).left) (Y := U.left) (Sigma.ι X i)) =
            B.inclusion.map (b.left ≫ B.inclusion.preimage
              (X := (Xsite j).left) (Y := U.left) (Sigma.ι X j)) :=
          congrArg (fun f => B.inclusion.map ((Over.forget (B.obj hS)).map f)) hab
        have key : ∀ (k : I) (t : Y.left ⟶ (Xsite k).left),
            B.inclusion.map (t ≫ B.inclusion.preimage (X := (Xsite k).left) (Y := U.left)
              (Sigma.ι X k)) = B.inclusion.map t ≫ Sigma.ι X k := fun k t =>
          (B.inclusion.map_comp _ _).trans
            (congrArg (fun z => B.inclusion.map t ≫ z) (B.inclusion.map_preimage _))
        exact ((key i a.left).symm.trans heq).trans (key j b.left)
      have hinitLeft : IsInitial Y.left := by
        apply IsInitial.isInitialOfObj B.inclusion Y.left
        exact hinitScheme
      exact ⟨over_initial_of_left_initial Y hinitLeft⟩)
  let F : Sheaf J (Type (u + 1)) :=
    ∐ fun i : I => (Sheaf.sheafifiedYoneda J).obj (Xsite i)
  let F₀ : Sheaf J (Type (u + 1)) := ∐ fun i : I => J.uliftYoneda.{u + 1}.obj (Xsite i)
  let eF : F ≅ F₀ := Sigma.mapIso (fun i => (eH.app (Xsite i)).symm)
  let eFU : F ≅ J.uliftYoneda.{u + 1}.obj U :=
    (eF.trans ((coproductIsCoproduct (fun i : I => J.uliftYoneda.{u + 1}.obj (Xsite i))
      ).coconePointUniqueUpToIso hcUlift))
  have hU : ∃ (V : BigFppfOver B S hS)
      (G : Sheaf J (Type (u + 1))), Nonempty (G.obj ≅ (uliftYoneda.{u + 1}).obj V) ∧
      Nonempty (G ≅ ∐ fun i : I => (Sheaf.sheafifiedYoneda J).obj (Xsite i)) := by
    refine ⟨U, F, ?_, ⟨Iso.refl _⟩⟩
    exact ⟨(sheafToPresheaf J (Type (u + 1))).mapIso eFU ≪≫
      J.uliftYonedaCompSheafToPresheaf.app U⟩
  have hthick := isThickening_map_liftedDiagram D
  exact ⟨satisfiesSetTheoreticCondition_of_colimit
    B S hS d hthick (formalSpectrum D) hX hU,
    I, inferInstance, inferInstance, inferInstance, d, hthick, hX⟩

variable {C : Type u} [CommRing C] [TopologicalSpace C]

/-- A continuous map of topological rings over the base scheme. The
compatibility is checked on all quotient maps for which one ideal maps into
the other. -/
public structure ContinuousHom (D : QuotientSystem B S hS A)
    (E : QuotientSystem B S hS C) where
  /-- The underlying ring homomorphism `A →+* C`. -/
  toRingHom : A →+* C
  continuous : Continuous toRingHom
  overS : ∀ (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
      (K : { I : Ideal C // TopologicalRing.IsWeakIdealOfDefinition I })
      (h : J.1 ≤ Ideal.comap toRingHom K.1),
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 toRingHom h)) ≫
      D.overS J = E.overS K

/-- The morphism of affine quotient schemes induced by a continuous map over
`S`, whenever the source ideal maps into the target ideal. -/
public def ContinuousHom.stageMap {D : QuotientSystem B S hS A}
    {E : QuotientSystem B S hS C} (f : ContinuousHom D E)
    (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
    (K : { I : Ideal C // TopologicalRing.IsWeakIdealOfDefinition I })
    (h : J.1 ≤ Ideal.comap f.toRingHom K.1) : E.stage K ⟶ D.stage J :=
  ObjectProperty.homMk <| Over.homMk (U := (E.stage K).1) (V := (D.stage J).1)
    (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom
      (Ideal.quotientMap K.1 f.toRingHom h))))
    (by apply ObjectProperty.hom_ext; exact f.overS J K h)

/-- Morphisms between affine `S`-schemes are equal when their underlying scheme maps are. -/
private theorem stage_hom_ext {X Y : BigAffineFppf B S hS} {f g : X ⟶ Y}
    (h : f.hom.left.hom = g.hom.left.hom) : f = g := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  exact h

/-- Spectra of ring maps out of a quotient are equal if the maps agree on representatives. -/
private theorem spec_map_ofHom_quotient_ext {R T : Type u} [CommRing R] [CommRing T] {I : Ideal R}
    {f g : R ⧸ I →+* T} (h : ∀ a, f (Ideal.Quotient.mk I a) = g (Ideal.Quotient.mk I a)) :
    Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom g) :=
  congrArg (fun φ => Spec.map (CommRingCat.ofHom φ)) (Ideal.Quotient.ringHom_ext (RingHom.ext h))

private theorem continuousHom_stageMap_natural
    {D : QuotientSystem B S hS A} {E : QuotientSystem B S hS C}
    [IsTopologicalRing A] [IsLinearTopology A A]
    (f : ContinuousHom D E)
    (I : Ideal A) (hI : TopologicalRing.IsWeakIdealOfDefinition I)
    {K L : OrderDual { I : Ideal C // TopologicalRing.IsWeakIdealOfDefinition I }}
    (g : K ⟶ L) :
    E.diagram.map g ≫
        f.stageMap (weakIdealComapIntersection I hI f.toRingHom f.continuous
          (OrderDual.ofDual L)) (OrderDual.ofDual L)
          (inf_le_right) =
      f.stageMap (weakIdealComapIntersection I hI f.toRingHom f.continuous
          (OrderDual.ofDual K)) (OrderDual.ofDual K)
          inf_le_right ≫
        D.diagram.map ((weakIdealComapFunctor I hI f.toRingHom f.continuous).map g) := by
  classical
  let ψ := weakIdealComapFunctor I hI f.toRingHom f.continuous
  have hLK : (OrderDual.ofDual L).1 ≤ (OrderDual.ofDual K).1 := leOfHom g
  have hJK : (OrderDual.ofDual (ψ.obj L)).1 ≤
      (OrderDual.ofDual (ψ.obj K)).1 := leOfHom (ψ.map g)
  change weakIdealComapIntersection I hI f.toRingHom f.continuous
      (OrderDual.ofDual L) ≤
    weakIdealComapIntersection I hI f.toRingHom f.continuous
      (OrderDual.ofDual K) at hJK
  change I ⊓ Ideal.comap f.toRingHom (OrderDual.ofDual L).1 ≤
      I ⊓ Ideal.comap f.toRingHom (OrderDual.ofDual K).1 at hJK
  dsimp only [QuotientSystem.diagram, QuotientSystem.transition,
    ContinuousHom.stageMap, weakIdealComapFunctor]
  refine stage_hom_ext ?_
  show Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.factor hLK)) ≫
      Spec.map (CommRingCat.ofHom
        (Ideal.quotientMap (OrderDual.ofDual L).1 f.toRingHom inf_le_right)) =
    Spec.map (CommRingCat.ofHom
        (Ideal.quotientMap (OrderDual.ofDual K).1 f.toRingHom inf_le_right)) ≫
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.factor hJK))
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  refine spec_map_ofHom_quotient_ext fun a => ?_
  simp [Ideal.Quotient.factor_mk, Ideal.quotientMap_mk]

private theorem continuousHom_stageMap_comp_transition
    {D : QuotientSystem B S hS A} {E : QuotientSystem B S hS C}
    (f : ContinuousHom D E)
    {J J' : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }}
    {K : { I : Ideal C // TopologicalRing.IsWeakIdealOfDefinition I }}
    (hJ : J'.1 ≤ J.1) (h : J.1 ≤ Ideal.comap f.toRingHom K.1)
    (h' : J'.1 ≤ Ideal.comap f.toRingHom K.1) :
    f.stageMap J K h ≫ D.transition hJ = f.stageMap J' K h' := by
  dsimp only [ContinuousHom.stageMap, QuotientSystem.transition]
  refine stage_hom_ext ?_
  show Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 f.toRingHom h)) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hJ)) =
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 f.toRingHom h'))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact spec_map_ofHom_quotient_ext fun a => by
    simp [Ideal.Quotient.factor_mk, Ideal.quotientMap_mk]

private theorem stageMap_colimit_eq_of_le
    {D : QuotientSystem B S hS A} {E : QuotientSystem B S hS C}
    (f : ContinuousHom D E)
    {J J' : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }}
    {K : { I : Ideal C // TopologicalRing.IsWeakIdealOfDefinition I }}
    (hJ : J'.1 ≤ J.1) (h : J.1 ≤ Ideal.comap f.toRingHom K.1)
    (h' : J'.1 ≤ Ideal.comap f.toRingHom K.1) :
    (BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        (f.stageMap J K h) ≫ formalSpectrumInclusion D (OrderDual.toDual J) =
    (BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        (f.stageMap J' K h') ≫ formalSpectrumInclusion D (OrderDual.toDual J') := by
  let H := BigAffineFppf.inclusion B S hS ⋙
    Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  have hw := colimit.w (formalSpectrumDiagram D)
    (homOfLE hJ : OrderDual.toDual J ⟶ OrderDual.toDual J')
  change H.map (D.transition hJ) ≫ formalSpectrumInclusion D (OrderDual.toDual J') =
    formalSpectrumInclusion D (OrderDual.toDual J) at hw
  show H.map _ ≫ _ = H.map _ ≫ _
  refine (congrArg (fun t => H.map (f.stageMap J K h) ≫ t) hw.symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun t => t ≫ formalSpectrumInclusion D (OrderDual.toDual J'))
    (H.map_comp (f.stageMap J K h) (D.transition hJ)).symm).trans ?_
  exact congrArg (fun t => H.map t ≫ formalSpectrumInclusion D (OrderDual.toDual J'))
    (continuousHom_stageMap_comp_transition f hJ h h')

private theorem stageMap_colimit_eq
    {D : QuotientSystem B S hS A} {E : QuotientSystem B S hS C}
    (f : ContinuousHom D E)
    (J J' : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
    (K : { I : Ideal C // TopologicalRing.IsWeakIdealOfDefinition I })
    (h : J.1 ≤ Ideal.comap f.toRingHom K.1)
    (h' : J'.1 ≤ Ideal.comap f.toRingHom K.1) :
    (BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        (f.stageMap J K h) ≫ formalSpectrumInclusion D (OrderDual.toDual J) =
    (BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        (f.stageMap J' K h') ≫ formalSpectrumInclusion D (OrderDual.toDual J') := by
  let L := weakIdealInf J J'
  have hL : L.1 ≤ Ideal.comap f.toRingHom K.1 := inf_le_left.trans h
  exact (stageMap_colimit_eq_of_le f (J' := L) inf_le_left h hL).trans
    (stageMap_colimit_eq_of_le f (J' := L) inf_le_right h' hL).symm

private theorem exists_formalSpectrumMap
    {D : QuotientSystem B S hS A} {E : QuotientSystem B S hS C}
    [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (f : ContinuousHom D E) :
    ∃ (I : Ideal A) (hI : TopologicalRing.IsWeakIdealOfDefinition I)
      (φ : formalSpectrum E ⟶ formalSpectrum D),
      (∀ (K : { I : Ideal C // TopologicalRing.IsWeakIdealOfDefinition I }),
        formalSpectrumInclusion E (OrderDual.toDual K) ≫ φ =
          (Sheaf.sheafifiedYoneda
            (BigFppfOver.topology B S hS)).map
              ((BigAffineFppf.inclusion B S hS).map
                (f.stageMap
                  (weakIdealComapIntersection I hI f.toRingHom f.continuous K)
                  K inf_le_right)) ≫
            formalSpectrumInclusion D
              (OrderDual.toDual
                (weakIdealComapIntersection I hI f.toRingHom f.continuous K))) ∧
      (∀ (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
        (K : { I : Ideal C // TopologicalRing.IsWeakIdealOfDefinition I })
        (h : J.1 ≤ Ideal.comap f.toRingHom K.1),
        formalSpectrumInclusion E (OrderDual.toDual K) ≫ φ =
          (Sheaf.sheafifiedYoneda
            (BigFppfOver.topology B S hS)).map
              ((BigAffineFppf.inclusion B S hS).map
                (f.stageMap J K h)) ≫
          formalSpectrumInclusion D (OrderDual.toDual J)) := by
  classical
  rcases hA.1 with ⟨I, hI⟩
  let ψ := weakIdealComapFunctor I hI f.toRingHom f.continuous
  let H := BigAffineFppf.inclusion B S hS ⋙
    Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let α : E.diagram ⟶ ψ ⋙ D.diagram := {
    app := fun K => f.stageMap
      (weakIdealComapIntersection I hI f.toRingHom f.continuous (OrderDual.ofDual K))
      (OrderDual.ofDual K) inf_le_right
    naturality := fun K L g => continuousHom_stageMap_natural f I hI g }
  let β : formalSpectrumDiagram E ⟶ ψ ⋙ formalSpectrumDiagram D := Functor.whiskerRight α H
  let c : Cocone (formalSpectrumDiagram E) := {
    pt := formalSpectrum D
    ι := β ≫ Functor.whiskerLeft ψ (colimit.cocone (formalSpectrumDiagram D)).ι }
  let φ := colimit.desc (formalSpectrumDiagram E) c
  have hcanon (K : { I : Ideal C // TopologicalRing.IsWeakIdealOfDefinition I }) :
      formalSpectrumInclusion E (OrderDual.toDual K) ≫ φ =
        H.map (f.stageMap (weakIdealComapIntersection I hI f.toRingHom f.continuous K)
          K inf_le_right) ≫ formalSpectrumInclusion D
            (OrderDual.toDual (weakIdealComapIntersection I hI f.toRingHom f.continuous K)) := by
    show colimit.ι (formalSpectrumDiagram E) (OrderDual.toDual K) ≫
      colimit.desc (formalSpectrumDiagram E) c = _
    rw [colimit.ι_desc]
    rfl
  refine ⟨I, hI, φ, hcanon, ?_⟩
  intro J K h
  exact (hcanon K).trans (stageMap_colimit_eq f _ J K inf_le_right h)

/-- The map of formal spectra is uniquely characterized by its effect on every
quotient stage. This is the universal-property construction of `Spf(f)`. -/
@[stacks 0AIF "quotient-stage characterization"]
public theorem existsUnique_formalSpectrumMap
    {D : QuotientSystem B S hS A} {E : QuotientSystem B S hS C}
    [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (f : ContinuousHom D E) :
    ∃! φ : formalSpectrum E ⟶ formalSpectrum D,
      ∀ (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
        (K : { I : Ideal C // TopologicalRing.IsWeakIdealOfDefinition I })
        (h : J.1 ≤ Ideal.comap f.toRingHom K.1),
        formalSpectrumInclusion E (OrderDual.toDual K) ≫ φ =
          (Sheaf.sheafifiedYoneda
            (BigFppfOver.topology B S hS)).map
              ((BigAffineFppf.inclusion B S hS).map
                (f.stageMap J K h)) ≫
        formalSpectrumInclusion D (OrderDual.toDual J) := by
  classical
  rcases exists_formalSpectrumMap hA f with ⟨I, hI, φ, hφ, hfull⟩
  refine ⟨φ, hfull, ?_⟩
  intro ψ hψ
  apply colimit.hom_ext
  intro K
  let K' := OrderDual.ofDual K
  let J := weakIdealComapIntersection I hI f.toRingHom f.continuous K'
  have hJK : J.1 ≤ Ideal.comap f.toRingHom K'.1 := inf_le_right
  exact (hψ J K' hJK).trans (hφ K').symm

/-- The canonical contravariant map on formal spectra. -/
@[stacks 0AIF "functorial map"]
public noncomputable def formalSpectrumMap
    {D : QuotientSystem B S hS A} {E : QuotientSystem B S hS C}
    [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (f : ContinuousHom D E) : formalSpectrum E ⟶ formalSpectrum D :=
  Classical.choose (existsUnique_formalSpectrumMap hA f)

/-- The defining effect of the canonical map on quotient stages. -/
public theorem formalSpectrumMap_spec
    {D : QuotientSystem B S hS A} {E : QuotientSystem B S hS C}
    [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (f : ContinuousHom D E)
    (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
    (K : { I : Ideal C // TopologicalRing.IsWeakIdealOfDefinition I })
    (h : J.1 ≤ Ideal.comap f.toRingHom K.1) :
    formalSpectrumInclusion E (OrderDual.toDual K) ≫ formalSpectrumMap hA f =
      (Sheaf.sheafifiedYoneda
        (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map
            (f.stageMap J K h)) ≫
        formalSpectrumInclusion D (OrderDual.toDual J) :=
  (Classical.choose_spec (existsUnique_formalSpectrumMap hA f)).1 J K h

/-- The formal-spectrum map of the identity homomorphism is the identity. -/
@[stacks 0AIF "identity law"]
public theorem formalSpectrumMap_id
    {D : QuotientSystem B S hS A}
    [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (f : ContinuousHom D D) (hf : f.toRingHom = RingHom.id A) :
    formalSpectrumMap hA f = 𝟙 (formalSpectrum D) := by
  apply colimit.hom_ext
  intro Jd
  let J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I } := OrderDual.ofDual Jd
  show formalSpectrumInclusion D (OrderDual.toDual J) ≫ formalSpectrumMap hA f =
    formalSpectrumInclusion D (OrderDual.toDual J) ≫ 𝟙 (formalSpectrum D)
  have hJJ : J.1 ≤ Ideal.comap f.toRingHom J.1 := by
    intro x hx
    show f.toRingHom x ∈ J.1
    rw [hf]
    exact hx
  have hstage : f.stageMap J J hJJ = 𝟙 (D.stage J) := by
    dsimp only [ContinuousHom.stageMap]
    refine stage_hom_ext ?_
    show Spec.map (CommRingCat.ofHom
      (Ideal.quotientMap J.1 f.toRingHom hJJ)) = 𝟙 _
    rw [← Spec.map_id, ← CommRingCat.ofHom_id]
    exact spec_map_ofHom_quotient_ext fun a => by simp [Ideal.quotientMap_mk, hf]
  have hspec : colimit.ι (formalSpectrumDiagram D) (OrderDual.toDual J) ≫ formalSpectrumMap hA f =
      (Sheaf.sheafifiedYoneda
        (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map
            (f.stageMap J J hJJ)) ≫
        colimit.ι (formalSpectrumDiagram D) (OrderDual.toDual J) :=
    formalSpectrumMap_spec hA f J J hJJ
  rw [hspec, hstage]
  simp only [CategoryTheory.Functor.map_id]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- Formal spectrum reverses composition of continuous maps over the base. -/
@[stacks 0AIF "composition law"]
public theorem formalSpectrumMap_comp
    {D : QuotientSystem B S hS A} {E : QuotientSystem B S hS C}
    {G : Type u} [CommRing G] [TopologicalSpace G]
    {F : QuotientSystem B S hS G}
    [IsTopologicalRing A] [IsLinearTopology A A]
    [IsTopologicalRing C] [IsLinearTopology C C]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (hC : TopologicalRing.IsWeaklyAdmissible C)
    (f : ContinuousHom D E) (g : ContinuousHom E F)
    (gf : ContinuousHom D F)
    (hgf : gf.toRingHom = g.toRingHom.comp f.toRingHom) :
    formalSpectrumMap hC g ≫ formalSpectrumMap hA f =
      formalSpectrumMap hA gf := by
  apply colimit.hom_ext
  intro L
  obtain ⟨K, hKL⟩ :=
    exists_weakIdeal_below_comap hC g.toRingHom g.continuous L
  obtain ⟨J, hJK⟩ :=
    exists_weakIdeal_below_comap hA f.toRingHom f.continuous K
  have hJL : J.1 ≤ Ideal.comap gf.toRingHom L.1 := by
    intro x hx
    show gf.toRingHom x ∈ L.1
    rw [hgf]
    exact hKL (hJK hx)
  have hstage :
      g.stageMap K L hKL ≫ f.stageMap J K hJK = gf.stageMap J L hJL := by
    dsimp only [ContinuousHom.stageMap]
    refine stage_hom_ext ?_
    show Spec.map (CommRingCat.ofHom
        (Ideal.quotientMap L.1 g.toRingHom hKL)) ≫
      Spec.map (CommRingCat.ofHom
        (Ideal.quotientMap K.1 f.toRingHom hJK)) =
      Spec.map (CommRingCat.ofHom
        (Ideal.quotientMap L.1 gf.toRingHom hJL))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact spec_map_ofHom_quotient_ext fun a => by simp [Ideal.quotientMap_mk, hgf]
  let H := BigAffineFppf.inclusion B S hS
  let G := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  have h1 : colimit.ι (formalSpectrumDiagram F) L ≫ formalSpectrumMap hC g =
      G.map (H.map (g.stageMap K L hKL)) ≫
        colimit.ι (formalSpectrumDiagram E) (OrderDual.toDual K) :=
    formalSpectrumMap_spec hC g K L hKL
  have h2 : colimit.ι (formalSpectrumDiagram E) (OrderDual.toDual K) ≫
      formalSpectrumMap hA f =
        G.map (H.map (f.stageMap J K hJK)) ≫
          colimit.ι (formalSpectrumDiagram D) (OrderDual.toDual J) :=
    formalSpectrumMap_spec hA f J K hJK
  have h3 : colimit.ι (formalSpectrumDiagram F) L ≫ formalSpectrumMap hA gf =
      G.map (H.map (gf.stageMap J L hJL)) ≫
        colimit.ι (formalSpectrumDiagram D) (OrderDual.toDual J) :=
    formalSpectrumMap_spec hA gf J L hJL
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun t => t ≫ formalSpectrumMap hA f) h1).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun t => G.map (H.map (g.stageMap K L hKL)) ≫ t) h2).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun t => t ≫ colimit.ι (formalSpectrumDiagram D) (OrderDual.toDual J))
    ((G.map_comp _ _).symm.trans (congrArg G.map (H.map_comp _ _).symm))).trans ?_
  exact (congrArg (fun t => G.map (H.map t) ≫
    colimit.ι (formalSpectrumDiagram D) (OrderDual.toDual J)) hstage).trans h3.symm

end AlgebraicGeometry.FormalSpace

end
