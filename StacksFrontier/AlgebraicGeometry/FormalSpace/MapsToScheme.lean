module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MapsToAffine
public import StacksFrontier.CategoryTheory.Sites.Density
public import StacksFrontier.Topology.Algebra.AdicTopology.Completion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Maps from an affine formal spectrum to a scheme (Stacks 0AQG)

Let `A` be a weakly admissible topological `S`-algebra such that `A ⧸ I` is a *local* ring for
*some* weak ideal of definition `I`, and let `X` be any scheme over `S`. **Stacks 0AQG** says
that restriction along the quotient maps

`Mor_S(Spec A, X) ⟶ Mor_S(Spf A, X)`

is a bijection — the affineness hypothesis on `X` in Stacks 0AQF is dropped.

The Stacks proof: since `Spec (A ⧸ I)` is local, a morphism `Spf A ⟶ X` carries it into an
affine open `U ⊆ X`; that forces `Spec (A ⧸ J)` into `U` for *every* weak ideal of definition
`J`; so Stacks 0AQF applies with target `U`.

Three steps of that argument are run here that the Stacks text leaves to the reader, and they are
work rather than decoration.

*Every* quotient is local, not just `A ⧸ I`. A weak ideal of definition consists of
topologically nilpotent elements, so it lies in the Jacobson radical (this is **Stacks 0DCZ**,
`TopologicalRing.henselianPair_of_isWeaklyAdmissible`); a ring with a local quotient by an ideal
inside the Jacobson radical is itself local; and a proper quotient of a local ring is local, a
weak ideal of definition being proper because `1` is not topologically nilpotent. That is
`weakQuotient_isLocalRing`, and without it the phrase "for every ideal of definition `J`" in the
source has nothing to stand on.

*One* affine open works for the whole family. Each `Spec (A ⧸ J)` lands in *some* affine open,
but 0AQF needs a single target; the closed points of all the `Spec (A ⧸ J)` agree, because
`A ⧸ (I ⊓ J)` surjects onto both `A ⧸ I` and `A ⧸ J` and `I ⊓ J` is again a weak ideal of
definition, so the affine open chosen for `I` receives them all
(`compatible_quotient_maps_agree_at_closedPoints`,
`compatible_quotient_maps_factor_through_affine_open`).

*Injectivity*, which Stacks explicitly omits ("We omit the proof of injectivity"). It is proved
here, in `restriction_map_bijective`: two morphisms `Spec A ⟶ X` over `S` with the same
restriction agree on the stage `I`, hence factor through the same affine open, and 0AQF's
bijection for that affine target identifies them.

## Main results

* `AlgebraicGeometry.FormalSpace.existsUnique_equiv_specHom_formalSpectrumHom`: **Stacks 0AQG**.

## Implementation notes

The statement is phrased as the *unique existence of an equivalence with a prescribed
quotient-stage behaviour* rather than as bijectivity of a separately named restriction function.
That is strictly more informative — it pins the equivalence, not just its existence — and it is
how a dependent statement can use it without having to reconstruct which map is meant. Internally the
equivalence is `Equiv.ofBijective` applied to
`AlgebraicGeometry.FormalSpace.restrictToFormalSpectrum`, the same restriction that
`StacksFrontier.AlgebraicGeometry.FormalSpace.MapsToAffine` states Stacks 0AQF about, so the
uniqueness clause is what identifies the two.

As in Stacks 0AQF, the morphism `p : Spec A ⟶ S` and its compatibility `hp` with the quotient
structure morphisms are explicit hypotheses, because
`AlgebraicGeometry.FormalSpace.QuotientSystem` records only the structure morphisms of the
quotients. Only `X` and the quotient spectra are required to lie in the chosen big fppf site.

## References

* [Stacks Project, Tag 0AQG](https://stacks.math.columbia.edu/tag/0AQG)
* [Stacks Project, Tag 0AQF](https://stacks.math.columbia.edu/tag/0AQF)
* [Stacks Project, Tag 0DCZ](https://stacks.math.columbia.edu/tag/0DCZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Filter
open scoped Topology

namespace AlgebraicGeometry.FormalSpace

universe u


private noncomputable def sheafifiedYonedaIsoUliftYoneda
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [J.Subcanonical] :
    Sheaf.sheafifiedYoneda J ≅ GrothendieckTopology.uliftYoneda.{u + 1} J := by
  let Gl := presheafToSheaf J (Type (u + 1))
  let Gr := sheafToPresheaf J (Type (u + 1))
  let adj : Gl ⊣ Gr := sheafificationAdjunction J (Type (u + 1))
  letI : IsIso adj.counit := inferInstance
  exact
    (Functor.isoWhiskerRight
      (GrothendieckTopology.uliftYonedaCompSheafToPresheaf.{u + 1} J).symm Gl) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (asIso adj.counit) ≪≫ Functor.rightUnitor _

private noncomputable def sheafifiedYoneda_fullyFaithful
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [J.Subcanonical] : (Sheaf.sheafifiedYoneda J).FullyFaithful :=
  (GrothendieckTopology.fullyFaithfulUliftYoneda.{u + 1} J).ofIso
    (sheafifiedYonedaIsoUliftYoneda J).symm

private noncomputable def schemeHomOfSheafHom
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [J.Subcanonical] {X Y : C}
    (f : (Sheaf.sheafifiedYoneda J).obj X ⟶
      (Sheaf.sheafifiedYoneda J).obj Y) : X ⟶ Y :=
  (sheafifiedYoneda_fullyFaithful J).preimage f

private lemma local_of_quotient_jacobson {A : Type*} [CommRing A] {I : Ideal A}
    (hI : I ≤ (⊥ : Ideal A).jacobson) [IsLocalRing (A ⧸ I)] : IsLocalRing A := by
  let : IsLocalHom (Ideal.Quotient.mk I) := isLocalHom_of_le_jacobson_bot I hI
  exact RingHom.domain_isLocalRing (Ideal.Quotient.mk I)

private lemma weakIdeal_le_jacobson {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (J : Ideal A) (hJ : TopologicalRing.IsWeakIdealOfDefinition J) :
    J ≤ (⊥ : Ideal A).jacobson :=
  (TopologicalRing.henselianPair_of_isWeaklyAdmissible A hA J hJ).le_jacobson

private lemma weakIdeal_ne_top {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [T2Space A] [Nontrivial A]
    (J : Ideal A) (hJ : TopologicalRing.IsWeakIdealOfDefinition J) : J ≠ ⊤ := by
  intro htop
  have ht : IsTopologicallyNilpotent (1 : A) := hJ.2 1 (by simp [htop])
  change Filter.Tendsto (fun n : ℕ ↦ (1 : A) ^ n) atTop (𝓝 0) at ht
  have ht' : Filter.Tendsto (fun _ : ℕ ↦ (1 : A)) atTop (𝓝 0) := by
    simp only [one_pow] at ht
    exact ht
  have h10 : (1 : A) = 0 := tendsto_nhds_unique tendsto_const_nhds ht'
  exact one_ne_zero h10

private lemma quotient_isLocalRing {A : Type*} [CommRing A] [IsLocalRing A]
    (J : Ideal A) (hJ : J ≠ ⊤) : IsLocalRing (A ⧸ J) := by
  let : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective

private lemma weakQuotient_isLocalRing {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (I J : Ideal A) (hI : TopologicalRing.IsWeakIdealOfDefinition I)
    (hJ : TopologicalRing.IsWeakIdealOfDefinition J) [IsLocalRing (A ⧸ I)] :
    IsLocalRing (A ⧸ J) := by
  let : T2Space A := hA.2.2
  let : IsLocalRing A :=
    local_of_quotient_jacobson (weakIdeal_le_jacobson hA I hI)
  exact quotient_isLocalRing J (weakIdeal_ne_top J hJ)

private lemma weakIdeal_inf {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A]
    {I J : Ideal A} (hI : TopologicalRing.IsWeakIdealOfDefinition I)
    (hJ : TopologicalRing.IsWeakIdealOfDefinition J) :
    TopologicalRing.IsWeakIdealOfDefinition (I ⊓ J) := by
  refine ⟨hI.1.inter hJ.1, ?_⟩
  intro x hx
  exact hI.2 x (Ideal.mem_inf.mp hx).1

private lemma factor_through_affine_open_of_closedPoint
    {R : Type*} [CommRing R] [IsLocalRing R] (X : Scheme)
    (f : Spec (.of R) ⟶ X) (U : X.affineOpens)
    (hx : f (IsLocalRing.closedPoint R) ∈ U.1) :
    ∃ g : Spec (.of R) ⟶ U.1.toScheme,
      g ≫ Scheme.Opens.ι U.1 = f := by
  have hpre : f ⁻¹ᵁ U.1 = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem f hx
  have hrange : Set.range f ⊆ Set.range (Scheme.Opens.ι U.1) := by
    rintro x ⟨y, rfl⟩
    have hy : y ∈ f ⁻¹ᵁ U.1 := by rw [hpre]; trivial
    exact ⟨⟨f y, hy⟩, rfl⟩
  refine ⟨IsOpenImmersion.lift (Scheme.Opens.ι U.1) f hrange, ?_⟩
  exact IsOpenImmersion.lift_fac _ _ _

/-- Every point of a scheme lies in some affine open. -/
private lemma exists_affineOpen_mem (X : Scheme) (x : X) : ∃ U : X.affineOpens, x ∈ U.1 := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact ⟨⟨U, hU⟩, hxU⟩

private lemma affineOpen_contains_of_contains
    (B : BigFppfSite.{u}) {X : Scheme.{u}}
    (hX : B.Contains X) (U : X.affineOpens) :
    B.Contains U.1.toScheme := by
  change U.1.toScheme.size < B.cutoff
  exact (Scheme.size_coe_opens_le X U.1).trans_lt hX

private lemma compatible_quotient_maps_agree_at_closedPoints
    {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (I : Ideal A) (hI : TopologicalRing.IsWeakIdealOfDefinition I)
    [IsLocalRing (A ⧸ I)] (X : Scheme.{u})
    (f : ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec (.of (A ⧸ J.1)) ⟶ X)
    (hf : ∀ (J L : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
      (h : J.1 ≤ L.1),
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) ≫ f J = f L)
    (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
    [IsLocalRing (A ⧸ J.1)] :
    f J (IsLocalRing.closedPoint (A ⧸ J.1)) =
      f ⟨I, hI⟩ (IsLocalRing.closedPoint (A ⧸ I)) := by
  let K : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I } :=
    ⟨I ⊓ J.1, TopologicalRing.isWeakIdealOfDefinition_inf_of_isOpen_right hI J.2.1⟩
  let : IsLocalRing (A ⧸ K.1) := weakQuotient_isLocalRing hA I K.1 hI K.2
  have hKJ : K.1 ≤ J.1 := inf_le_right
  have hKI : K.1 ≤ I := inf_le_left
  have key : ∀ (L : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
      [IsLocalRing (A ⧸ L.1)] (h : K.1 ≤ L.1),
      f L (IsLocalRing.closedPoint (A ⧸ L.1)) = f K (IsLocalRing.closedPoint (A ⧸ K.1)) := by
    intro L _ h
    let : IsLocalHom (Ideal.Quotient.factor h) :=
      IsLocalHom.of_surjective _ (Ideal.Quotient.factor_surjective h)
    rw [← hf K L h]
    change f K ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)))
      (IsLocalRing.closedPoint (A ⧸ L.1))) = _
    rw [AlgebraicGeometry.Spec_closedPoint]
  exact (key J hKJ).trans (key ⟨I, hI⟩ hKI).symm

private lemma compatible_quotient_maps_factor_through_affine_open
    {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (I : Ideal A) (hI : TopologicalRing.IsWeakIdealOfDefinition I)
    [IsLocalRing (A ⧸ I)] (X : Scheme.{u})
    (f : ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec (.of (A ⧸ J.1)) ⟶ X)
    (hf : ∀ (J L : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
      (h : J.1 ≤ L.1),
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) ≫ f J = f L)
    (U : X.affineOpens)
    (hx : f ⟨I, hI⟩ (IsLocalRing.closedPoint (A ⧸ I)) ∈ U.1) :
    ∃ g : ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
        Spec (.of (A ⧸ J.1)) ⟶ U.1.toScheme,
      (∀ J, g J ≫ Scheme.Opens.ι U.1 = f J) ∧
      (∀ (J L : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
        (h : J.1 ≤ L.1),
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) ≫ g J = g L) := by
  have hex : ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ g : Spec (.of (A ⧸ J.1)) ⟶ U.1.toScheme, g ≫ Scheme.Opens.ι U.1 = f J := fun J => by
    let : IsLocalRing (A ⧸ J.1) := weakQuotient_isLocalRing hA I J.1 hI J.2
    exact factor_through_affine_open_of_closedPoint (R := A ⧸ J.1) X (f J) U
      (compatible_quotient_maps_agree_at_closedPoints hA I hI X f hf J ▸ hx)
  choose g hg using hex
  refine ⟨g, hg, fun J L h => ?_⟩
  apply (cancel_mono (Scheme.Opens.ι U.1)).1
  rw [Category.assoc, hg J, hg L]
  exact hf J L h

private noncomputable def affineOpenOverObject
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : Scheme.{u}} (hX : B.Contains X) (xS : X ⟶ S)
    (U : X.affineOpens) : BigAffineFppf B S hS := by
  let hU : B.Contains U.1.toScheme := affineOpen_contains_of_contains B hX U
  refine ⟨Over.mk ((ObjectProperty.homMk (Scheme.Opens.ι U.1) :
    B.obj hU ⟶ B.obj hX) ≫ (ObjectProperty.homMk xS : B.obj hX ⟶ B.obj hS)), ?_⟩
  change IsAffine U.1.toScheme
  infer_instance

private noncomputable def affineStageOverMap
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {A : Type u} [CommRing A] [TopologicalSpace A]
    (D : QuotientSystem B S hS A)
    {X : Scheme.{u}} (hX : B.Contains X) (xS : X ⟶ S)
    (U : X.affineOpens) (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
    (q : Spec (.of (A ⧸ J.1)) ⟶ U.1.toScheme)
    (hq : q ≫ Scheme.Opens.ι U.1 ≫ xS = D.overS J) :
    (BigAffineFppf.inclusion B S hS).obj (D.stage J) ⟶
      (BigAffineFppf.inclusion B S hS).obj
        (affineOpenOverObject B S hS hX xS U) :=
  Over.homMk (ObjectProperty.homMk q) (ObjectProperty.hom_ext _ hq)

private noncomputable def affineOpenOverMap
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : Scheme.{u}} (hX : B.Contains X) (xS : X ⟶ S)
    (U : X.affineOpens) :
    (BigAffineFppf.inclusion B S hS).obj
      (affineOpenOverObject B S hS hX xS U) ⟶
    Over.mk (ObjectProperty.homMk xS : B.obj hX ⟶ B.obj hS) := by
  let hU : B.Contains U.1.toScheme := affineOpen_contains_of_contains B hX U
  refine Over.homMk (ObjectProperty.homMk (Scheme.Opens.ι U.1) :
    B.obj hU ⟶ B.obj hX) ?_
  apply ObjectProperty.hom_ext
  rfl

private noncomputable def formalStageHom
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {A : Type u} [CommRing A] [TopologicalSpace A]
    (D : QuotientSystem B S hS A)
    (X : BigFppfOver B S hS)
    (e : formalSpectrum D ⟶
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj X)
    (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :
    (BigAffineFppf.inclusion B S hS).obj (D.stage J) ⟶ X := by
  letI : (BigFppfOver.topology B S hS).Subcanonical :=
    bigFppfOver_subcanonical B S hS
  exact schemeHomOfSheafHom (BigFppfOver.topology B S hS)
    (formalSpectrumInclusion D (OrderDual.toDual J) ≫ e)

private theorem formalStageHom_commutes_with_base
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {A : Type u} [CommRing A] [TopologicalSpace A]
    (D : QuotientSystem B S hS A) {J : { I : Ideal A //
      TopologicalRing.IsWeakIdealOfDefinition I }}
    (X : BigFppfOver B S hS) (e : formalSpectrum D ⟶
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj X) :
    (BigFppfOver.toScheme B S hS).map (formalStageHom D X e J) ≫
      B.inclusion.map X.hom = D.overS J := by
  have hw := congrArg (B.inclusion.map) (formalStageHom D X e J).w
  convert hw using 1
  rfl

private theorem sheafifiedYoneda_map_formalStageHom
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {A : Type u} [CommRing A] [TopologicalSpace A]
    (D : QuotientSystem B S hS A)
    (X : BigFppfOver B S hS)
    (e : formalSpectrum D ⟶
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj X)
    (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
      (formalStageHom D X e J) =
      formalSpectrumInclusion D (OrderDual.toDual J) ≫ e := by
  let : (BigFppfOver.topology B S hS).Subcanonical :=
    bigFppfOver_subcanonical B S hS
  exact (sheafifiedYoneda_fullyFaithful
    (BigFppfOver.topology B S hS)).homEquiv.right_inv _

private theorem formalStageHom_compatible
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {A : Type u} [CommRing A] [TopologicalSpace A]
    (D : QuotientSystem B S hS A)
    (X : BigFppfOver B S hS)
    (e : formalSpectrum D ⟶
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj X)
    (J L : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) (h : J.1 ≤ L.1) :
    (BigAffineFppf.inclusion B S hS).map (D.transition h) ≫
        formalStageHom D X e J = formalStageHom D X e L := by
  let : (BigFppfOver.topology B S hS).Subcanonical :=
    bigFppfOver_subcanonical B S hS
  apply (sheafifiedYoneda_fullyFaithful
    (BigFppfOver.topology B S hS)).map_injective
  rw [Functor.map_comp, sheafifiedYoneda_map_formalStageHom,
    sheafifiedYoneda_map_formalStageHom]
  exact congrArg (fun z => z ≫ e) (colimit.w (formalSpectrumDiagram D)
    (homOfLE h : OrderDual.toDual L ⟶ OrderDual.toDual J))

private theorem formalStageHom_scheme_compatible
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {A : Type u} [CommRing A] [TopologicalSpace A]
    (D : QuotientSystem B S hS A)
    (X : BigFppfOver B S hS)
    (e : formalSpectrum D ⟶
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj X)
    (J L : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) (h : J.1 ≤ L.1) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) ≫
      (BigFppfOver.toScheme B S hS).map (formalStageHom D X e J) =
    (BigFppfOver.toScheme B S hS).map (formalStageHom D X e L) := by
  convert congrArg (fun f => (BigFppfOver.toScheme B S hS).map f)
    (formalStageHom_compatible D X e J L h) using 1
  rfl

private theorem formalMap_factors_through_affineOpen
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (D : QuotientSystem B S hS A)
    (I : Ideal A) (hI : TopologicalRing.IsWeakIdealOfDefinition I)
    [IsLocalRing (A ⧸ I)] (X : Scheme.{u}) (hX : B.Contains X)
    (xS : X ⟶ S)
    (e : formalSpectrum D ⟶
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        (Over.mk (ObjectProperty.homMk xS : B.obj hX ⟶ B.obj hS)))
    (U : X.affineOpens)
    (hx : (BigFppfOver.toScheme B S hS).map
        (formalStageHom D
          (Over.mk (ObjectProperty.homMk xS : B.obj hX ⟶ B.obj hS)) e ⟨I, hI⟩)
        (IsLocalRing.closedPoint (A ⧸ I)) ∈ U.1) :
    ∃ eU : formalSpectrum D ⟶
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
          ((BigAffineFppf.inclusion B S hS).obj
            (affineOpenOverObject B S hS hX xS U)),
      eU ≫ (Sheaf.sheafifiedYoneda
        (BigFppfOver.topology B S hS)).map
          (affineOpenOverMap B S hS hX xS U) = e := by
  let Xo : BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk xS : B.obj hX ⟶ B.obj hS)
  let : (BigFppfOver.topology B S hS).Subcanonical :=
    bigFppfOver_subcanonical B S hS
  let f : ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec (.of (A ⧸ J.1)) ⟶ X :=
    fun J => (BigFppfOver.toScheme B S hS).map (formalStageHom D Xo e J)
  have hf : ∀ (J L : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
      (h : J.1 ≤ L.1),
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) ≫ f J = f L :=
    formalStageHom_scheme_compatible D Xo e
  obtain ⟨g, hg, hgg⟩ := compatible_quotient_maps_factor_through_affine_open
    hA I hI X f hf U (by
      convert hx using 1 <;> rfl)
  let target : BigAffineFppf B S hS := affineOpenOverObject B S hS hX xS U
  let targetObj : BigFppfOver B S hS :=
    (BigAffineFppf.inclusion B S hS).obj target
  let q : ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
      (BigAffineFppf.inclusion B S hS).obj (D.stage J) ⟶
      targetObj :=
    fun J => affineStageOverMap D hX xS U J (g J) (by
      calc
        g J ≫ Scheme.Opens.ι U.1 ≫ xS = f J ≫ xS := by
          simpa [Category.assoc] using congrArg (fun z => z ≫ xS) (hg J)
        _ = D.overS J := by
          convert formalStageHom_commutes_with_base (D := D) (J := J) Xo e using 1
          rfl)
  have hq : ∀ (J L : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
      (h : J.1 ≤ L.1),
      (BigAffineFppf.inclusion B S hS).map (D.transition h) ≫ q J = q L :=
    fun J L h => Over.OverMorphism.ext (ObjectProperty.hom_ext _ (hgg J L h))
  let u : targetObj ⟶ Xo :=
    affineOpenOverMap B S hS hX xS U
  let c : Cocone (formalSpectrumDiagram D) := by
    refine { pt := (Sheaf.sheafifiedYoneda
      (BigFppfOver.topology B S hS)).obj targetObj, ι := ?_ }
    refine { app := fun J => (Sheaf.sheafifiedYoneda
      (BigFppfOver.topology B S hS)).map (q J), naturality := ?_ }
    intro J L a
    let h : L.1 ≤ J.1 := leOfHom a
    change (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map (D.transition h)) ≫
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (q L) =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (q J)
    rw [← Functor.map_comp, hq L J h]
  refine ⟨colimit.desc _ c, colimit.hom_ext fun J => ?_⟩
  let J0 := OrderDual.ofDual J
  have hdesc := colimit.ι_desc c J
  change ((colimit.ι (formalSpectrumDiagram D) J ≫
    colimit.desc (formalSpectrumDiagram D) c) ≫ (Sheaf.sheafifiedYoneda
      (BigFppfOver.topology B S hS)).map u) = _
  have hqu : q J ≫ u = formalStageHom D Xo e J0 :=
    Over.OverMorphism.ext (ObjectProperty.hom_ext _ (hg J0))
  rw [hdesc, ← Functor.map_comp, hqu]
  convert sheafifiedYoneda_map_formalStageHom D Xo e J0 using 1
  rfl

private theorem restrictToFormalSpectrum_comp
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {A : Type u} [CommRing A] [TopologicalSpace A]
    (D : QuotientSystem B S hS A) (p : Spec (.of A) ⟶ S)
    (hp : ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ p = D.overS J)
    (X Y : BigFppfOver B S hS) (u : X ⟶ Y)
    (f : (Over.mk p : Over S) ⟶ (Over.post B.inclusion).obj X) :
    restrictToFormalSpectrum D p hp Y
        (f ≫ (Over.post B.inclusion).map u) =
      restrictToFormalSpectrum D p hp X f ≫
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map u := by
  refine colimit.hom_ext fun J => ?_
  change formalSpectrumInclusion D (OrderDual.toDual (OrderDual.ofDual J)) ≫ _ =
    formalSpectrumInclusion D (OrderDual.toDual (OrderDual.ofDual J)) ≫ _ ≫ _
  refine (restrictToFormalSpectrum_spec D p hp Y _ _).trans (Eq.trans ?_ (Category.assoc _ _ _))
  rw [restrictToFormalSpectrum_spec,
    show stageRestriction D p hp Y (f ≫ (Over.post B.inclusion).map u) (OrderDual.ofDual J) =
      stageRestriction D p hp X f (OrderDual.ofDual J) ≫ u from
      Over.OverMorphism.ext (ObjectProperty.hom_ext _ rfl)]
  exact Functor.map_comp _ _ _

private noncomputable def ordinaryHomAsBigFppfOver
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {A : Type u} [CommRing A] [TopologicalSpace A]
    (p : Spec (.of A) ⟶ S)
    (X : Scheme.{u}) (hX : B.Contains X) (xS : X ⟶ S)
    (f : (Over.mk p : Over S) ⟶ (Over.mk xS : Over S)) :
    (Over.mk p : Over S) ⟶ (Over.post B.inclusion).obj
      (Over.mk (ObjectProperty.homMk xS : B.obj hX ⟶ B.obj hS) :
        BigFppfOver B S hS) := by
  refine Over.homMk f.left ?_
  change f.left ≫ B.inclusion.map
    (ObjectProperty.homMk xS : B.obj hX ⟶ B.obj hS) = p
  exact f.w

private noncomputable def affineOpenFactorMap
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {A : Type u} [CommRing A] [TopologicalSpace A]
    (p : Spec (.of A) ⟶ S)
    (X : Scheme.{u}) (hX : B.Contains X) (xS : X ⟶ S)
    (f : (Over.mk p : Over S) ⟶ (Over.mk xS : Over S))
    (U : X.affineOpens)
    (g : Spec (.of A) ⟶ U.1.toScheme)
    (hg : g ≫ Scheme.Opens.ι U.1 = f.left) :
    (Over.mk p : Over S) ⟶ (Over.post B.inclusion).obj
      ((BigAffineFppf.inclusion B S hS).obj
        (affineOpenOverObject B S hS hX xS U)) := by
  refine Over.homMk g ?_
  change g ≫ Scheme.Opens.ι U.1 ≫ xS = p
  calc
    g ≫ Scheme.Opens.ι U.1 ≫ xS =
        (g ≫ Scheme.Opens.ι U.1) ≫ xS := by simp [Category.assoc]
    _ = f.left ≫ xS := by rw [hg]
    _ = p := f.w

private theorem restriction_map_bijective
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (D : QuotientSystem B S hS A)
    (p : Spec (.of A) ⟶ S)
    (hp : ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ p = D.overS J)
    (I : Ideal A) (hI : TopologicalRing.IsWeakIdealOfDefinition I)
    [IsLocalRing (A ⧸ I)]
    (X : Scheme.{u}) (hX : B.Contains X) (xS : X ⟶ S) :
    Function.Bijective (fun f : (Over.mk p : Over S) ⟶ (Over.mk xS : Over S) =>
      restrictToFormalSpectrum D p hp
        (Over.mk (ObjectProperty.homMk xS : B.obj hX ⟶ B.obj hS))
        (ordinaryHomAsBigFppfOver (hS := hS) p X hX xS f)) := by
  classical
  let Xo : BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk xS : B.obj hX ⟶ B.obj hS)
  let : (BigFppfOver.topology B S hS).Subcanonical :=
    bigFppfOver_subcanonical B S hS
  let r : ((Over.mk p : Over S) ⟶ (Over.mk xS : Over S)) →
      (formalSpectrum D ⟶
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj Xo) :=
    fun f => restrictToFormalSpectrum D p hp Xo
      (ordinaryHomAsBigFppfOver p X hX xS f)
  refine ⟨fun f g hfg => ?_, fun e => ?_⟩
  · let f' := ordinaryHomAsBigFppfOver (hS := hS) p X hX xS f
    let g' := ordinaryHomAsBigFppfOver (hS := hS) p X hX xS g
    have hstage : ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ f.left =
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ g.left := fun J => by
      have hh := congrArg (fun z => formalSpectrumInclusion D (OrderDual.toDual J) ≫ z) hfg
      rw [restrictToFormalSpectrum_spec, restrictToFormalSpectrum_spec] at hh
      exact congrArg (BigFppfOver.toScheme B S hS).map
        ((sheafifiedYoneda_fullyFaithful (BigFppfOver.topology B S hS)).map_injective hh)
    let : IsLocalRing A :=
      local_of_quotient_jacobson (weakIdeal_le_jacobson hA I hI)
    let : IsLocalHom (Ideal.Quotient.mk I) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have hpoint :
        f.left (IsLocalRing.closedPoint A) = g.left (IsLocalRing.closedPoint A) := by
      have hclosed : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
          (IsLocalRing.closedPoint (A ⧸ I)) = IsLocalRing.closedPoint A :=
        AlgebraicGeometry.Spec_closedPoint
      have hh := congrArg (fun k : Spec (.of (A ⧸ I)) ⟶ X => k (IsLocalRing.closedPoint (A ⧸ I)))
        (hstage ⟨I, hI⟩)
      change f.left (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
        (IsLocalRing.closedPoint (A ⧸ I))) = g.left (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk I)) (IsLocalRing.closedPoint (A ⧸ I))) at hh
      rwa [hclosed] at hh
    obtain ⟨U, hxU⟩ := exists_affineOpen_mem X (f.left (IsLocalRing.closedPoint A))
    have hgxU : g.left (IsLocalRing.closedPoint A) ∈ U.1 := hpoint ▸ hxU
    obtain ⟨fU, hfU⟩ := factor_through_affine_open_of_closedPoint
      (R := A) X f.left U hxU
    obtain ⟨gU, hgU⟩ := factor_through_affine_open_of_closedPoint
      (R := A) X g.left U hgxU
    let W := affineOpenOverObject B S hS hX xS U
    let W' := (BigAffineFppf.inclusion B S hS).obj W
    let fW := affineOpenFactorMap (hS := hS) p X hX xS f U fU hfU
    let gW := affineOpenFactorMap (hS := hS) p X hX xS g U gU hgU
    have hrestr :
        restrictToFormalSpectrum D p hp W' fW =
            restrictToFormalSpectrum D p hp W' gW := by
      refine colimit.hom_ext fun j => ?_
      let J0 := OrderDual.ofDual j
      have hquotU :
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J0.1)) ≫ fU =
            Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J0.1)) ≫ gU := by
        apply (cancel_mono (Scheme.Opens.ι U.1)).1
        rw [Category.assoc, Category.assoc, hfU, hgU]
        exact hstage J0
      have hstageU :
          stageRestriction D p hp W' fW J0 =
            stageRestriction D p hp W' gW J0 :=
        Over.OverMorphism.ext (ObjectProperty.hom_ext _ hquotU)
      exact (restrictToFormalSpectrum_spec D p hp W' fW J0).trans
        ((congrArg (Sheaf.sheafifiedYoneda
          (BigFppfOver.topology B S hS)).map hstageU).trans
          (restrictToFormalSpectrum_spec D p hp W' gW J0).symm)
    have hleft : fU = gU := congrArg Over.Hom.left
      ((bijective_map_into_affine hA D p hp W).1 hrestr)
    exact Over.OverMorphism.ext (by rw [← hfU, ← hgU, hleft])
  · let fJ : ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
        Spec (.of (A ⧸ J.1)) ⟶ X :=
      fun J => (BigFppfOver.toScheme B S hS).map
        (formalStageHom D Xo e J)
    obtain ⟨U, hxU⟩ := exists_affineOpen_mem X (fJ ⟨I, hI⟩ (IsLocalRing.closedPoint (A ⧸ I)))
    obtain ⟨eU, heU⟩ := formalMap_factors_through_affineOpen hA D I hI
      (A := A) X hX xS e U hxU
    let W := affineOpenOverObject B S hS hX xS U
    let W' := (BigAffineFppf.inclusion B S hS).obj W
    let inclusion : W' ⟶ Xo := affineOpenOverMap B S hS hX xS U
    obtain ⟨fW, hfW⟩ := (bijective_map_into_affine hA D p hp W).2 eU
    let fOrig : (Over.mk p : Over S) ⟶ (Over.mk xS : Over S) :=
      fW ≫ (Over.post B.inclusion).map inclusion
    refine ⟨fOrig, ?_⟩
    change restrictToFormalSpectrum D p hp Xo
      (ordinaryHomAsBigFppfOver p X hX xS fOrig) = e
    have hordinary :
        ordinaryHomAsBigFppfOver (hS := hS) p X hX xS fOrig =
          fW ≫ (Over.post B.inclusion).map inclusion := rfl
    rw [hordinary, restrictToFormalSpectrum_comp D p hp W' Xo inclusion fW, hfW, heU]

/-- The canonical bijection between maps from a spectrum and from its formal
spectrum to an `S`-scheme, characterized by restriction to every weak quotient.
-/
@[stacks 0AQG, sga "3 XV 1.4"]
public theorem existsUnique_equiv_specHom_formalSpectrumHom
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (D : QuotientSystem B S hS A)
    (p : Spec (.of A) ⟶ S)
    (hp : ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ p = D.overS J)
    (I : Ideal A) (hI : TopologicalRing.IsWeakIdealOfDefinition I)
    [IsLocalRing (A ⧸ I)]
    (X : Scheme.{u}) (hX : B.Contains X) (xS : X ⟶ S) :
    let Xo : BigFppfOver B S hS :=
      Over.mk (ObjectProperty.homMk xS : B.obj hX ⟶ B.obj hS)
    ∃! e : ((Over.mk p : Over S) ⟶ (Over.mk xS : Over S)) ≃
        (formalSpectrum D ⟶
          (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj Xo),
      ∀ (f : (Over.mk p : Over S) ⟶ (Over.mk xS : Over S))
    (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }),
        ∃ g : (BigAffineFppf.inclusion B S hS).obj (D.stage J) ⟶ Xo,
          B.inclusion.map g.left =
              Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ f.left ∧
            formalSpectrumInclusion D (OrderDual.toDual J) ≫ e f =
              (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map g := by
  classical
  let Xo : BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk xS : B.obj hX ⟶ B.obj hS)
  let : (BigFppfOver.topology B S hS).Subcanonical :=
    bigFppfOver_subcanonical B S hS
  let restrict : ((Over.mk p : Over S) ⟶ (Over.mk xS : Over S)) →
      (formalSpectrum D ⟶
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj Xo) :=
    fun f => restrictToFormalSpectrum D p hp Xo
      (ordinaryHomAsBigFppfOver (hS := hS) p X hX xS f)
  let e : ((Over.mk p : Over S) ⟶ (Over.mk xS : Over S)) ≃
      (formalSpectrum D ⟶
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj Xo) :=
    Equiv.ofBijective restrict (restriction_map_bijective hA D p hp I hI X hX xS)
  refine ⟨e, ?_, ?_⟩
  · intro f J
    let f' := ordinaryHomAsBigFppfOver (hS := hS) p X hX xS f
    let g := stageRestriction D p hp Xo f' J
    exact ⟨g, rfl, restrictToFormalSpectrum_spec D p hp Xo f' J⟩
  · intro e' he'
    refine Equiv.ext fun f => colimit.hom_ext fun j => ?_
    let J := OrderDual.ofDual j
    obtain ⟨g, hg, hge⟩ := he' f J
    have hg' : g = stageRestriction D p hp Xo
        (ordinaryHomAsBigFppfOver (hS := hS) p X hX xS f) J :=
      Over.OverMorphism.ext (ObjectProperty.hom_ext _ hg)
    change formalSpectrumInclusion D (OrderDual.toDual J) ≫ e' f =
      formalSpectrumInclusion D (OrderDual.toDual J) ≫
        restrictToFormalSpectrum D p hp Xo
          (ordinaryHomAsBigFppfOver (hS := hS) p X hX xS f)
    have hmid : (Sheaf.sheafifiedYoneda
        (BigFppfOver.topology B S hS)).map g =
          (Sheaf.sheafifiedYoneda
            (BigFppfOver.topology B S hS)).map
              (stageRestriction D p hp Xo
                (ordinaryHomAsBigFppfOver (hS := hS) p X hX xS f) J) := by
      rw [← hg']
    exact hge.trans (hmid.trans
      (restrictToFormalSpectrum_spec D p hp Xo
        (ordinaryHomAsBigFppfOver (hS := hS) p X hX xS f) J).symm)

end AlgebraicGeometry.FormalSpace

end
