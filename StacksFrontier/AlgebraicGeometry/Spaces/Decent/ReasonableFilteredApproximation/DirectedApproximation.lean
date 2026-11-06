module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.AlgebraicGeometry.Morphisms.LocalIso
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.EquivalenceRelation
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.RegularEpi
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.RingTheory.Algebraic.Cardinality
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankSections
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.DescentFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.FiniteSchemeFiltration
public import StacksFrontier.AlgebraicGeometry.Groupoids.FittingIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.UniversallyBoundedFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.Permanence
public import StacksFrontier.AlgebraicGeometry.Spaces.EquivalenceRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSmoothLocalCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationFromQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedAbsolute
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Reasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCover
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge
import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties
import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization
import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 03K0: directed approximations and the étale groupoid chart

The conclusion of Stacks 03K0 (`AlgebraicGeometry.Space.DirectedApproximation`), its
quasi-separated case by the constant system, the refutation of clause (1) as stated, the corrected
conclusion `AlgebraicGeometry.Space.CorrectedDirectedApproximation`, and the first step of the
proof: an affine surjective étale chart of a quasi-compact reasonable space with universally
bounded fibres, presented by an étale groupoid (Stacks 03H6, Stacks 03JL).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

section

/-! ### A retract of a quasi-separated algebraic space is quasi-separated -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A retract of a quasi-separated algebraic space is quasi-separated**, over the base `S`.
A morphism with a right inverse is a split monomorphism, hence a monomorphism, and the
diagonal of the source of a monomorphism is a base change of the diagonal of its target. -/
theorem isQuasiSeparatedOver_of_retract {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : F ⟶ G) (p : G ⟶ F) (hgp : g ≫ p = 𝟙 F)
    (hG : IsQuasiSeparatedOver B S hS G) : IsQuasiSeparatedOver B S hS F := by
  have _ : IsSplitMono g := IsSplitMono.mk' ⟨p, hgp⟩
  have _ : Mono g := IsSplitMono.mono g
  exact isQuasiSeparatedOver_of_mono B S hS g hG

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **A retract of a quasi-separated algebraic space is quasi-separated**, absolutely.
`AlgebraicGeometry.Space.viewOverIntegers` is a functor applied to the presheaf, so it
carries the retract over `S` to a retract over the terminal scheme, where
`AlgebraicGeometry.Space.isQuasiSeparatedOver_of_retract` applies. -/
theorem isAbsolutelyQuasiSeparated_of_retract {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : F ⟶ G) (p : G ⟶ F) (hgp : g ≫ p = 𝟙 F)
    (hG : IsAbsolutelyQuasiSeparated B S hS hZ G) :
    IsAbsolutelyQuasiSeparated B S hS hZ F := by
  let g₀ : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
  exact isQuasiSeparatedOver_of_retract B (⊤_ Scheme.{u}) hZ
    ((CategoryTheory.OverShriek.relocalizePresheafFunctor g₀).map g)
    ((CategoryTheory.OverShriek.relocalizePresheafFunctor g₀).map p)
    (by rw [← CategoryTheory.Functor.map_comp, hgp, CategoryTheory.Functor.map_id]) hG

/-! ### Constant diagrams over a filtered index category -/

variable {J : Type u} [Category.{u} J]

/-- All components of a cocone on a constant diagram over a filtered index category agree,
by naturality along a common upper bound of any two indices. -/
theorem cocone_const_ι_app_eq [IsFiltered J] {C : Type*} [Category C] {X : C}
    (s : Cocone ((Functor.const J).obj X)) (i j : J) : s.ι.app i = s.ι.app j := by
  have key : ∀ (a b : J) (_ : a ⟶ b), s.ι.app a = s.ι.app b := by
    intro a b f
    have h := s.ι.naturality f
    simpa using h.symm
  rw [key i _ (IsFiltered.leftToMax i j), key j _ (IsFiltered.rightToMax i j)]

/-- Over a filtered index category the identity cocone on a constant diagram is a colimit
cocone: a cocone on a constant diagram has all its components equal, by naturality along a
common upper bound of any two indices. -/
noncomputable def isColimit_constCocone_of_isFiltered [IsFiltered J] {C : Type*} [Category C]
    (X : C) : IsColimit (Cocone.mk X (𝟙 ((Functor.const J).obj X))) := by
  have : Nonempty J := IsFiltered.nonempty
  refine ⟨fun s => s.ι.app (Classical.arbitrary J), fun s i => ?_, fun s m hm => ?_⟩
  · simpa using (cocone_const_ι_app_eq s (Classical.arbitrary J) i)
  · simpa using (hm (Classical.arbitrary J))

/-! ### The conclusion of Stacks 03K0 -/

/-- **The conclusion of Stacks 03K0.** A *directed approximation* of a sheaf `X` on the big
fppf site of `S` is a filtered index category together with a diagram of algebraic spaces
over `S` which are quasi-compact and quasi-separated, and a colimit cocone with vertex `X`,
subject to the three further clauses of the source:

* `sections_surjective` and `sections_eventually_eq` are clause (1): the canonical map from
  the filtered colimit of the sets of sections over a quasi-compact test scheme `T` to the
  sections of `X` over `T` is surjective, respectively injective;
* `transition_surjective`, `transition_etale`, `coprojection_surjective` and
  `coprojection_etale` are clause (2);
* `stage_isRepresentable`, `transition_isLocalIso` and `coprojection_isLocalIso` are clause
  (3).

Clause (1) is stated here exactly as the source states it, over all quasi-compact test
schemes. As stated it is **false** for a general quasi-compact reasonable `X`; see the
module documentation and
`AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_directedApproximation`. -/
structure DirectedApproximation
    (X : Sheaf (BigFppfOver.topology B S hS) (Type u)) where
  /-- The index category of the system. -/
  index : Cat.{u, u}
  /-- The system is directed. -/
  isFiltered : IsFiltered index
  /-- The system itself. -/
  diagram : index ⥤ Sheaf (BigFppfOver.topology B S hS) (Type u)
  /-- The coprojections `X i ⟶ X`. -/
  coprojection : diagram ⟶ (Functor.const index).obj X
  /-- `X` is the colimit of the system, in sheaves. -/
  isColimit : IsColimit (Cocone.mk X coprojection)
  /-- Every stage is an algebraic space over `S`. -/
  stage_isAlgebraicSpace : ∀ i, IsAlgebraicSpace B S hS (diagram.obj i).obj
  /-- Every stage is quasi-compact. -/
  stage_isQuasiCompactSpace : ∀ i, IsQuasiCompactSpace B S hS (diagram.obj i).obj
  /-- Every stage is quasi-separated. -/
  stage_isAbsolutelyQuasiSeparated :
    ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (diagram.obj i).obj
  /-- Clause (1), surjectivity: every section of `X` over a quasi-compact test scheme comes
  from a section of some stage. -/
  sections_surjective : ∀ (T : BigFppfOver B S hS),
    CompactSpace ((BigFppfOver.toScheme B S hS).obj T) →
    ∀ ξ : X.obj.obj (op T), ∃ (i : index) (η : (diagram.obj i).obj.obj (op T)),
      (coprojection.app i).hom.app (op T) η = ξ
  /-- Clause (1), injectivity: two sections of stages over a quasi-compact test scheme with
  the same image in `X` are identified by a pair of transition maps. -/
  sections_eventually_eq : ∀ (T : BigFppfOver B S hS),
    CompactSpace ((BigFppfOver.toScheme B S hS).obj T) →
    ∀ (i j : index) (η : (diagram.obj i).obj.obj (op T))
      (θ : (diagram.obj j).obj.obj (op T)),
      (coprojection.app i).hom.app (op T) η = (coprojection.app j).hom.app (op T) θ →
      ∃ (k : index) (a : i ⟶ k) (b : j ⟶ k),
        (diagram.map a).hom.app (op T) η = (diagram.map b).hom.app (op T) θ
  /-- Clause (2): the transition morphisms are surjective. -/
  transition_surjective : ∀ (i j : index) (a : i ⟶ j),
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (diagram.map a).hom
  /-- Clause (2): the transition morphisms are étale. -/
  transition_etale : ∀ (i j : index) (a : i ⟶ j),
    IsEtale B S hS (diagram.map a).hom
  /-- Clause (2): the coprojections are surjective. -/
  coprojection_surjective : ∀ i,
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (coprojection.app i).hom
  /-- Clause (2): the coprojections are étale. -/
  coprojection_etale : ∀ i, IsEtale B S hS (coprojection.app i).hom
  /-- Clause (3): if `X` is a scheme then so is every stage. -/
  stage_isRepresentable : X.obj.IsRepresentable → ∀ i, (diagram.obj i).obj.IsRepresentable
  /-- Clause (3): if `X` is a scheme the transition morphisms are local isomorphisms. -/
  transition_isLocalIso : X.obj.IsRepresentable → ∀ (i j : index) (a : i ⟶ j),
    (MorphismProperty.inverseImage (@IsLocalIso.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (diagram.map a).hom
  /-- Clause (3): if `X` is a scheme the coprojections are local isomorphisms. -/
  coprojection_isLocalIso : X.obj.IsRepresentable → ∀ i,
    (MorphismProperty.inverseImage (@IsLocalIso.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (coprojection.app i).hom

/-! ### The quasi-separated case, by the constant system -/

/-- A property of morphisms of the site which holds for isomorphisms is inherited by the
identity of any presheaf, in the sense of `CategoryTheory.MorphismProperty.presheaf`: every
represented base change of an identity is an isomorphism.

This is the identity case of `AlgebraicGeometry.presheaf_of_isIso` of
`StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalMonomorphism`, restated here under a
different name so that this module need not import the theory of algebraic stacks for one
six-line lemma, and so that both modules can be imported at once. -/
theorem presheaf_id_of_isIso_presheaf (P : MorphismProperty (BigFppfOver B S hS))
    (hP : ∀ ⦃V W : BigFppfOver B S hS⦄ (h : V ⟶ W), IsIso h → P h)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : P.presheaf (𝟙 F) := by
  refine ⟨Functor.relativelyRepresentable.of_isIso yoneda _, ?_⟩
  intro A C g fst snd hpb
  have : IsIso (yoneda.map snd) := hpb.isIso_snd_of_isIso
  have : IsIso snd := Functor.FullyFaithful.isIso_of_isIso_map Yoneda.fullyFaithful snd
  exact hP snd ‹IsIso snd›

/-- The identity of a presheaf is surjective after every represented base change: such a base
change of an identity is an isomorphism, and an isomorphism of schemes is surjective. -/
theorem presheaf_surjective_id_presheaf
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (𝟙 F) := by
  refine presheaf_id_of_isIso_presheaf B S hS _ ?_ F
  intro V W h hh
  have := hh
  show Surjective ((BigFppfOver.toScheme B S hS).map h)
  infer_instance

/-- An isomorphism of schemes is a local isomorphism: `AlgebraicGeometry.IsLocalIso` contains
the identities and respects isomorphisms. -/
theorem isLocalIso_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] : IsLocalIso f := by
  have _ : MorphismProperty.RespectsIso (@IsLocalIso.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : MorphismProperty.ContainsIdentities (@IsLocalIso.{u} : MorphismProperty Scheme.{u}) :=
    (inferInstance :
      MorphismProperty.IsMultiplicative (@IsLocalIso.{u} : MorphismProperty Scheme.{u}))
      |>.toContainsIdentities
  exact MorphismProperty.of_isIso _ f

/-- The identity of a presheaf is a local isomorphism after every represented base change: such
a base change of an identity is an isomorphism, and an isomorphism of schemes is a local
isomorphism. -/
theorem presheaf_isLocalIso_id_presheaf
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    (MorphismProperty.inverseImage (@IsLocalIso.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (𝟙 F) := by
  refine presheaf_id_of_isIso_presheaf B S hS _ ?_ F
  intro V W h hh
  have := hh
  show IsLocalIso ((BigFppfOver.toScheme B S hS).map h)
  exact isLocalIso_of_isIso _

/-- The identity of a presheaf is étale after every represented base change: such a base
change of an identity is an isomorphism, and an isomorphism of schemes is étale. -/
private theorem presheaf_etale_id_presheaf (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (𝟙 F) := by
  refine presheaf_id_of_isIso_presheaf B S hS _ ?_ F
  intro V W h hh
  have := hh
  change Etale ((BigFppfOver.toScheme B S hS).map h)
  infer_instance

/-- **Stacks 03K0 for a quasi-separated space.** A quasi-compact, quasi-separated algebraic
space over `S` carries a directed approximation in the sense of the source, with clause (1)
in its original form over all quasi-compact test schemes: the constant system indexed by the
one-object category works, all of whose transition morphisms and coprojections are
identities.

By `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_directedApproximation` the
quasi-separatedness hypothesis is also *necessary* when `X` is a scheme, so the statement of
Stacks 03K0 is not available for a general quasi-compact reasonable `X`; the hypothesis is
the correction, and an approximation of a non-quasi-separated `X` exists only after clause
(1) is restricted to quasi-compact quasi-separated test schemes. -/
@[stacks 03K0 "correction: clause (1) as literally stated holds only for quasi-separated X,\
  and is proved here under that hypothesis"]
theorem exists_directedApproximation_of_isAbsolutelyQuasiSeparated
    (X : Sheaf (BigFppfOver.topology B S hS) (Type u))
    (hX : IsAlgebraicSpace B S hS X.obj)
    (hqc : IsQuasiCompactSpace B S hS X.obj)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.obj) :
    Nonempty (DirectedApproximation B S hS hZ X) := by
  classical
  have hJ : IsFiltered (Cat.of PUnit.{u + 1}) := inferInstanceAs (IsFiltered PUnit.{u + 1})
  refine ⟨{
    index := Cat.of PUnit.{u + 1}
    isFiltered := hJ
    diagram := (Functor.const (Cat.of PUnit.{u + 1})).obj X
    coprojection := 𝟙 _
    isColimit := isColimit_constCocone_of_isFiltered X
    stage_isAlgebraicSpace := fun _ => hX
    stage_isQuasiCompactSpace := fun _ => hqc
    stage_isAbsolutelyQuasiSeparated := fun _ => hqs
    sections_surjective := fun T _ ξ => ⟨PUnit.unit, ξ, rfl⟩
    sections_eventually_eq := fun T _ i j η θ h =>
      ⟨IsFiltered.max i j, IsFiltered.leftToMax i j, IsFiltered.rightToMax i j, by
        simpa using (by simpa using h : η = θ)⟩
    transition_surjective := fun i j a => by
      simpa using presheaf_surjective_id_presheaf B S hS X.obj
    transition_etale := fun i j a => by
      simpa using isEtale_id B S hS X.obj
    coprojection_surjective := fun i => by
      simpa using presheaf_surjective_id_presheaf B S hS X.obj
    coprojection_etale := fun i => by
      simpa using isEtale_id B S hS X.obj
    stage_isRepresentable := fun h _ => h
    transition_isLocalIso := fun _ i j a => by
      simpa using presheaf_isLocalIso_id_presheaf B S hS X.obj
    coprojection_isLocalIso := fun _ i => by
      simpa using presheaf_isLocalIso_id_presheaf B S hS X.obj }⟩

/-! ### Clause (1) as stated forces quasi-separatedness -/

/-- **Clause (1) of Stacks 03K0, as stated, forces `X` to be quasi-separated.** Let `X` be a
quasi-compact algebraic space which is a scheme, and suppose it carries a directed
approximation by quasi-separated algebraic spaces satisfying clause (1) in the form the
source states it, over every quasi-compact test scheme. Testing clause (1) on `T = X`
itself — legitimate, since `X` is a quasi-compact scheme over `S` — produces a section of
one coprojection `X i ⟶ X`, exhibiting `X` as a retract of the quasi-separated space `X i`;
so `X` is quasi-separated.

Consequently Stacks 03K0 is **false as stated**: a quasi-compact scheme which is not
quasi-separated is a quasi-compact reasonable algebraic space carrying no such system. The
repair supported by the source's own proof is to restrict clause (1) to test schemes that
are quasi-compact *and quasi-separated*. -/
@[stacks 03K0 "refutation of clause (1) as stated: it forces X quasi-separated, so the\
  correct clause (1) restricts to quasi-compact quasi-separated test schemes"]
theorem isAbsolutelyQuasiSeparated_of_directedApproximation
    (X : Sheaf (BigFppfOver.topology B S hS) (Type u))
    [hrep : X.obj.IsRepresentable]
    (hqc : IsQuasiCompactSpace B S hS X.obj)
    (A : DirectedApproximation B S hS hZ X) :
    IsAbsolutelyQuasiSeparated B S hS hZ X.obj := by
  classical
  -- `X` is represented by an object `T` of the site whose underlying scheme is compact
  set T := X.obj.reprX with hT
  set e : yoneda.obj T ≅ X.obj := X.obj.reprW with he
  have hTcompact : CompactSpace ((BigFppfOver.toScheme B S hS).obj T) :=
    compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS
      (IsQuasiCompactSpace.of_iso B S hS hqc e.symm)
  -- clause (1) applied to the test scheme `T` and the section of `X` given by the identity
  obtain ⟨i, η, hη⟩ := A.sections_surjective T hTcompact (e.hom.app (op T) (𝟙 T))
  -- the section of the coprojection obtained from `η` by Yoneda
  set p : (A.diagram.obj i).obj ⟶ yoneda.obj T :=
    (A.coprojection.app i).hom ≫ e.inv with hp
  have hpη : p.app (op T) η = 𝟙 T := by
    have h := congrArg (e.inv.app (op T)) hη
    simpa [hp, Iso.hom_inv_id_app] using h
  set g : yoneda.obj T ⟶ (A.diagram.obj i).obj := yonedaEquiv.symm η with hg
  have hgp : (e.inv ≫ g) ≫ (p ≫ e.hom) = 𝟙 X.obj := by
    have hyg : yonedaEquiv g = η := by rw [hg, Equiv.apply_symm_apply]
    have hone : (yonedaEquiv (𝟙 (yoneda.obj T)) : T ⟶ T) = 𝟙 T :=
      (yonedaEquiv_apply (𝟙 (yoneda.obj T))).trans rfl
    have h1 : g ≫ p = 𝟙 (yoneda.obj T) :=
      yonedaEquiv.injective (by rw [yonedaEquiv_comp, hyg, hone]; exact hpη)
    rw [Category.assoc, reassoc_of% h1, Iso.inv_hom_id]
  exact isAbsolutelyQuasiSeparated_of_retract B S hS hZ _ _ hgp
    (A.stage_isAbsolutelyQuasiSeparated i)

/-- **The statement of Stacks 03K0 for a quasi-compact scheme is equivalent to
quasi-separatedness.** Together with
`AlgebraicGeometry.Space.exists_directedApproximation_of_isAbsolutelyQuasiSeparated` this
pins down exactly when the source's statement is true for a representable space. -/
theorem nonempty_directedApproximation_iff
    (X : Sheaf (BigFppfOver.topology B S hS) (Type u))
    [X.obj.IsRepresentable]
    (hX : IsAlgebraicSpace B S hS X.obj)
    (hqc : IsQuasiCompactSpace B S hS X.obj) :
    Nonempty (DirectedApproximation B S hS hZ X) ↔
      IsAbsolutelyQuasiSeparated B S hS hZ X.obj :=
  ⟨fun ⟨A⟩ => isAbsolutelyQuasiSeparated_of_directedApproximation B S hS hZ X hqc A,
    fun hqs => exists_directedApproximation_of_isAbsolutelyQuasiSeparated B S hS hZ X hX hqc hqs⟩

/-- **The counterexample schema for Stacks 03K0 as stated.** A quasi-compact scheme over `S`
which is not quasi-separated admits no directed approximation with clause (1) in the
source's form. Such schemes exist: `AlgebraicGeometry.DoubledOriginData.scheme`, two copies
of `Spec k[X₀, X₁, …]` glued along the complement of the origin, is covered by two affine
opens (`AlgebraicGeometry.compactSpace_scheme`) and is not a quasi-separated space
(`AlgebraicGeometry.not_quasiSeparatedSpace_scheme`), because the intersection of those two
opens is the punctured spectrum. Every scheme is a reasonable algebraic space by
`AlgebraicGeometry.Space.isReasonableSpace_yoneda`, the composite `(θ) ⇒ (ζ) ⇒ (ε) ⇒ (δ)` of
the diagram of Stacks 03JX, so this is a quasi-compact reasonable algebraic space to which
Stacks 03K0 applies and for which its conclusion fails.

The statement proved here needs only the failure of quasi-separatedness; the witness is
substituted into it, and the hypotheses of 03K0 verified for that witness, in
`AlgebraicGeometry.Space.exists_quasiCompact_reasonable_isEmpty_directedApproximation` of
`StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReasonableFilteredApproximationCounterexample`,
which assumes nothing. -/
theorem isEmpty_directedApproximation_of_not_isAbsolutelyQuasiSeparated
    (X : Sheaf (BigFppfOver.topology B S hS) (Type u))
    [X.obj.IsRepresentable]
    (hqc : IsQuasiCompactSpace B S hS X.obj)
    (hns : ¬ IsAbsolutelyQuasiSeparated B S hS hZ X.obj) :
    IsEmpty (DirectedApproximation B S hS hZ X) :=
  ⟨fun A => hns (isAbsolutelyQuasiSeparated_of_directedApproximation B S hS hZ X hqc A)⟩

end

/-! ### Stacks 03K0 with clause (1) corrected, for a general reasonable space -/

/-- **The corrected conclusion of Stacks 03K0.** A *corrected directed approximation* of a
sheaf `X` on the big fppf site of `S` is a directed preorder (a thin filtered index category), a
diagram of quasi-compact quasi-separated algebraic spaces over `S`, and a colimit cocone
identified with `X`, subject to the three clauses of the source:

* `sections_surjective` and `sections_eventually_injective` are clause (1): the canonical map
  from the filtered colimit of the sets of sections over a test scheme `T` to the sections of
  `X` over `T` is surjective when `T` is quasi-compact and quasi-separated, respectively
  injective when `T` is quasi-compact;
* `transition_surjective`, `transition_etale`, `projection_surjective` and `projection_etale`
  are clause (2);
* `scheme_stages`, `scheme_transition_localIso` and `scheme_projection_localIso` are clause (3).

Clause (1) is the **corrected** one: for surjectivity the test scheme `T` is required to be
quasi-compact *and quasi-separated*. Over all quasi-compact `T`, which is what the source writes,
the clause is false — it forces `X` itself to be quasi-separated, by
`AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_directedApproximation`, where
`AlgebraicGeometry.Space.DirectedApproximation` carries clause (1) in the source's literal
form. The restriction to quasi-separated `T` is exactly what the source's own proof supports:
the section is lifted from a descent datum on `T' ×_T T'` for an affine étale cover `T' → T`,
and that fibre product is quasi-compact only when the diagonal of `T` is. -/
structure CorrectedDirectedApproximation
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type u)) where
  /-- The index category of the system. -/
  index : Cat.{0, u}
  /-- The system is directed. -/
  filtered : IsFiltered index
  /-- The index category is a preorder, so the system is indexed by a directed set. -/
  thin : Quiver.IsThin index
  /-- The system itself. -/
  diagram : index ⥤ Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type u)
  /-- The coprojections `X i ⟶ colim X i`. -/
  cocone : Cocone diagram
  /-- The vertex of the cocone is `X`. -/
  comparison : cocone.pt ≅ X
  /-- `X` is the colimit of the system, in sheaves. -/
  isColimit : IsColimit cocone
  /-- Every stage is an algebraic space over `S`. -/
  algebraicSpace : ∀ i, AlgebraicGeometry.IsAlgebraicSpace B S hS (diagram.obj i).obj
  /-- Every stage is quasi-compact. -/
  quasiCompact : ∀ i, AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS (diagram.obj i).obj
  /-- Every stage is quasi-separated. -/
  quasiSeparated : ∀ i,
    AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ (diagram.obj i).obj
  /-- Clause (1), corrected, surjectivity: every section of `X` over a quasi-compact
  quasi-separated test scheme comes from a section of some stage. -/
  sections_surjective :
    ∀ (T : AlgebraicGeometry.BigFppfOver B S hS),
      CompactSpace ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T) →
      QuasiSeparatedSpace ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T) →
      ∀ ξ : X.obj.obj (op T), ∃ (i : index) (η : (diagram.obj i).obj.obj (op T)),
        ((cocone.ι.app i ≫ comparison.hom).hom.app (op T)) η = ξ
  /-- Clause (1), injectivity, over **every** quasi-compact test scheme, as in the source: two
  sections of stages with the same image in `X` are identified by a pair of transition maps. -/
  sections_eventually_injective :
    ∀ (T : AlgebraicGeometry.BigFppfOver B S hS),
      CompactSpace ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T) →
      ∀ (i j : index) (η : (diagram.obj i).obj.obj (op T))
        (θ : (diagram.obj j).obj.obj (op T)),
        ((cocone.ι.app i ≫ comparison.hom).hom.app (op T)) η =
          ((cocone.ι.app j ≫ comparison.hom).hom.app (op T)) θ →
        ∃ (k : index) (f : i ⟶ k) (g : j ⟶ k),
          (diagram.map f).hom.app (op T) η =
            (diagram.map g).hom.app (op T) θ
  /-- Clause (2): the transition morphisms are surjective. -/
  transition_surjective : ∀ (i j : index) (f : i ⟶ j),
    IsSurjective B S hS (diagram.map f).hom
  /-- Clause (2): the transition morphisms are étale. -/
  transition_etale : ∀ (i j : index) (f : i ⟶ j),
    AlgebraicGeometry.Space.IsEtale B S hS (diagram.map f).hom
  /-- Clause (2): the coprojections `X i ⟶ X` are surjective. -/
  projection_surjective : ∀ i,
    IsSurjective B S hS (cocone.ι.app i ≫ comparison.hom).hom
  /-- Clause (2): the coprojections `X i ⟶ X` are étale. -/
  projection_etale : ∀ i,
    AlgebraicGeometry.Space.IsEtale B S hS (cocone.ι.app i ≫ comparison.hom).hom
  /-- Clause (3): if `X` is a scheme then so is every stage. -/
  scheme_stages : X.obj.IsRepresentable → ∀ i, (diagram.obj i).obj.IsRepresentable
  /-- Clause (3): if `X` is a scheme the transition morphisms are local isomorphisms. -/
  scheme_transition_localIso : X.obj.IsRepresentable →
    ∀ (i j : index) (f : i ⟶ j),
      (MorphismProperty.inverseImage
        (@IsLocalIso.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf (diagram.map f).hom
  /-- Clause (3): if `X` is a scheme the coprojections `X i ⟶ X` are local isomorphisms. -/
  scheme_projection_localIso : X.obj.IsRepresentable → ∀ i,
    (MorphismProperty.inverseImage
      (@IsLocalIso.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf
      (cocone.ι.app i ≫ comparison.hom).hom

namespace ReasonableApproximation


/-- The size cutoff of a big fppf site, as a property of schemes, is closed under isomorphisms,
because isomorphic schemes have equal `Scheme.size`. -/
local instance schemeCutoff_isClosedUnderIsomorphisms
    (B : AlgebraicGeometry.BigFppfSite.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms
      (fun X : Scheme.{u} ↦ X.size < B.cutoff) where
  of_iso {X Y} e h := by
    change X.size < B.cutoff at h
    rwa [← Scheme.size_congr e]

/-- The size cutoff of a big fppf site is closed under pullbacks: a pullback of two schemes of size
below the cutoff again has size below the cutoff. -/
local instance schemeCutoff_isClosedUnderLimitsOfShape_walkingCospan
    (B : AlgebraicGeometry.BigFppfSite.{u}) :
    ObjectProperty.IsClosedUnderLimitsOfShape
      (fun X : Scheme.{u} ↦ X.size < B.cutoff) WalkingCospan :=
  .mk' (by
    rintro _ ⟨F, hF⟩
    rw [Scheme.size_congr (HasLimit.isoOfNatIso (diagramIsoCospan F))]
    exact Scheme.size_pullback_lt _ _ (hF .left) (hF .right))

/-- The schemes below the cutoff of a big fppf site have a terminal object. -/
local instance schemeCutoff_hasTerminal (B : AlgebraicGeometry.BigFppfSite.{u}) :
    HasTerminal B.Schemes := inferInstance

/-- The schemes below the cutoff of a big fppf site have pullbacks. -/
local instance schemeCutoff_hasPullbacks (B : AlgebraicGeometry.BigFppfSite.{u}) :
    HasPullbacks B.Schemes := inferInstance

/-- **Stacks 03H6.** A quasi-compact algebraic space `X` over `S` admits a chart `φ : U ⟶ X` with
`U` an affine object of the site and `φ` surjective and étale. This is the first step of the
proof of Stacks 03K0. -/
theorem exists_affine_etale_surjective_chart
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS X) :
    ∃ (U : AlgebraicGeometry.BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X),
      IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U) ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf φ ∧
      AlgebraicGeometry.Space.IsEtale B S hS φ :=
  (AlgebraicGeometry.Space.isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover
    B S hS X hX).mp hqc

/-- **Stacks 03JL.** For a reasonable algebraic space `X`, an affine étale chart `φ : U ⟶ X` has
universally bounded fibres; this is the integer bound `N` used to shorten chains later on. -/
theorem affine_etale_chart_has_bounded_fibers
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hr : IsReasonableSpace B S hS X)
    (U : AlgebraicGeometry.BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X)
    (hU : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U))
    (hφ : AlgebraicGeometry.Space.IsEtale B S hS φ) :
    HasUniversallyBoundedFibers B S hS U φ := by
  have hφ' := hφ U (𝟙 (yoneda.obj U)) (presheaf_etale_id_presheaf B S hS _)
  exact hr U hU φ (by simpa using hφ')

/-- A quasi-compact reasonable algebraic space admits an affine étale surjective chart whose fibres
are universally bounded, combining Stacks 03H6 and Stacks 03JL. -/
private theorem exists_affine_etale_surjective_bounded_chart
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS X)
    (hr : IsReasonableSpace B S hS X) :
    ∃ (U : AlgebraicGeometry.BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X),
      IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U) ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf φ ∧
      AlgebraicGeometry.Space.IsEtale B S hS φ ∧
      HasUniversallyBoundedFibers B S hS U φ := by
  obtain ⟨U, φ, hU, hsurj, hφ⟩ :=
    exists_affine_etale_surjective_chart B S hS X hX hqc
  exact ⟨U, φ, hU, hsurj, hφ,
    affine_etale_chart_has_bounded_fibers B S hS X hr U φ hU hφ⟩

/-- The kernel pair of a chart exists inside the site: for `φ : yoneda.obj U ⟶ X` with `X` an
algebraic space there are `R` in the site and `s t : R ⟶ U` exhibiting `R` as `U ×_X U`. -/
private theorem exists_chart_kernel_pair
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (U : AlgebraicGeometry.BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X) :
    ∃ (R : AlgebraicGeometry.BigFppfOver B S hS) (s t : R ⟶ U),
      IsPullback (yoneda.map t) (yoneda.map s) φ φ := by
  let C := AlgebraicGeometry.BigFppfOver B S hS
  let : HasPullbacks C := inferInstance
  let : HasBinaryProducts C := hasBinaryProducts_of_hasTerminal_and_pullbacks C
  let hrep := hX.diagonal_representable.of_diag φ
  let R := hrep.pullback φ
  let t : R ⟶ U := yoneda.preimage (hrep.fst φ)
  let s : R ⟶ U := hrep.snd φ
  have ht : yoneda.map t = hrep.fst φ := by simp [t]
  refine ⟨R, s, t, ?_⟩
  simpa [s, ht] using hrep.isPullback φ

/-- The kernel pair `R = U ×_X U` of a chart with universally bounded fibres can be taken so that
the projection `s : R ⟶ U` again has universally bounded fibres. -/
private theorem exists_chart_kernel_pair_with_bounded_projection
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (U : AlgebraicGeometry.BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X)
    (hφ : HasUniversallyBoundedFibers B S hS U φ) :
    ∃ (R : AlgebraicGeometry.BigFppfOver B S hS) (s t : R ⟶ U),
      IsPullback (yoneda.map t) (yoneda.map s) φ φ ∧
      HasUniversallyBoundedFibers B S hS R (yoneda.map s) := by
  let : HasPullbacks (AlgebraicGeometry.BigFppfOver B S hS) := inferInstance
  let : HasBinaryProducts (AlgebraicGeometry.BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have hrep : yoneda.relativelyRepresentable φ :=
    (Functor.relativelyRepresentable.diag_iff).1 hX.diagonal_representable φ
  obtain ⟨R, i, p, hpull, hbound⟩ :=
    hasUniversallyBoundedFibers_baseChange B S hS φ hrep U φ hφ
  let t : R ⟶ U := yoneda.preimage i
  let s : R ⟶ U := yoneda.preimage p
  have ht : yoneda.map t = i := by simp [t]
  have hs : yoneda.map s = p := by simp [s]
  refine ⟨R, s, t, ?_, ?_⟩
  · simpa only [ht, hs] using hpull
  · simpa only [hs] using hbound

/-- Two morphisms `x y : T ⟶ U` identified by `f : yoneda.obj U ⟶ F` factor through a kernel pair
`R` of `f`, represented by an object of the site: Yoneda is fully faithful, so the lift supplied
by the pullback property comes from a morphism `T ⟶ R`. -/
theorem exists_lift_of_isPullback_yoneda
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {R U T : AlgebraicGeometry.BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ F) (a b : R ⟶ U)
    (hR : IsPullback (yoneda.map a) (yoneda.map b) f f) (x y : T ⟶ U)
    (hxy : yoneda.map x ≫ f = yoneda.map y ≫ f) :
    ∃ r : T ⟶ R, r ≫ a = x ∧ r ≫ b = y := by
  refine ⟨yoneda.preimage (hR.lift (yoneda.map x) (yoneda.map y) hxy), ?_, ?_⟩ <;>
    apply yoneda.map_injective <;>
    simp only [Functor.map_comp, Functor.map_preimage]
  · exact hR.lift_fst _ _ _
  · exact hR.lift_snd _ _ _

/-- If one projection of the kernel pair `R = U ×_X U` has universally bounded fibres, so does the
other: the lift swapping the two projections is an involution of `R` exchanging `s` and `t`. -/
private theorem kernelPair_other_projection_hasUniversallyBoundedFibers
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {R U : AlgebraicGeometry.BigFppfOver B S hS}
    (φ : yoneda.obj U ⟶ X) (s t : R ⟶ U)
    (hR : IsPullback (yoneda.map t) (yoneda.map s) φ φ)
    (hs : HasUniversallyBoundedFibers B S hS R (yoneda.map s)) :
    HasUniversallyBoundedFibers B S hS R (yoneda.map t) := by
  obtain ⟨σ, hσt, hσs⟩ := exists_lift_of_isPullback_yoneda φ t s hR s t hR.w.symm
  have hσsq_t : (σ ≫ σ) ≫ t = (𝟙 R) ≫ t := by
    calc
      (σ ≫ σ) ≫ t = σ ≫ (σ ≫ t) := Category.assoc _ _ _
      _ = σ ≫ s := by rw [hσt]
      _ = t := hσs
      _ = (𝟙 R) ≫ t := (Category.id_comp _).symm
  have hσsq_s : (σ ≫ σ) ≫ s = (𝟙 R) ≫ s := by
    calc
      (σ ≫ σ) ≫ s = σ ≫ (σ ≫ s) := Category.assoc _ _ _
      _ = σ ≫ t := by rw [hσs]
      _ = s := hσt
      _ = (𝟙 R) ≫ s := (Category.id_comp _).symm
  have hσsq : σ ≫ σ = 𝟙 R := by
    apply yoneda.map_injective
    apply hR.hom_ext
    · simpa only [Functor.map_comp] using congrArg yoneda.map hσsq_t
    · simpa only [Functor.map_comp] using congrArg yoneda.map hσsq_s
  let eσ : R ≅ R := ⟨σ, σ, hσsq, hσsq⟩
  rcases hs with ⟨n, hs⟩
  refine ⟨n, ?_⟩
  intro k hk T hT ξ
  obtain ⟨V, p, i, r, hr, hrank, hpull⟩ := hs k T hT ξ
  let yσ : yoneda.obj R ⟶ yoneda.obj R := yoneda.map σ
  let j : yoneda.obj V ⟶ yoneda.obj R := i ≫ yσ
  have hj : IsPullback j (yoneda.map p) (yoneda.map t) ξ := by
    apply hpull.of_iso (Iso.refl (yoneda.obj V)) (yoneda.mapIso eσ)
      (Iso.refl (yoneda.obj T)) (Iso.refl (yoneda.obj U))
    · show i ≫ yσ = i ≫ yσ
      rfl
    · simp
    · show yoneda.map s = yoneda.map σ ≫ yoneda.map t
      rw [← Functor.map_comp, hσt]
    · simp
  exact ⟨V, p, j, r, hr, hrank, hj⟩

/-- Both projections `s, t : R ⟶ U` of the kernel pair of an étale chart `φ` are étale, being base
changes of `φ` along `φ`. -/
private theorem chart_kernel_pair_projections_are_etale
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (U : AlgebraicGeometry.BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X)
    (hφ : AlgebraicGeometry.Space.IsEtale B S hS φ)
    (R : AlgebraicGeometry.BigFppfOver B S hS) (s t : R ⟶ U)
    (hR : IsPullback (yoneda.map t) (yoneda.map s) φ φ) :
    AlgebraicGeometry.Space.IsEtale B S hS (yoneda.map s) ∧
      AlgebraicGeometry.Space.IsEtale B S hS (yoneda.map t) := by
  let G := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) G
  have hφ' : P.presheaf φ := hφ U (𝟙 (yoneda.obj U)) (presheaf_etale_id_presheaf B S hS _)
  let : HasPullbacks (AlgebraicGeometry.BigFppfOver B S hS) := inferInstance
  let : PreservesLimitsOfShape WalkingCospan G := by
    apply comp_preservesLimitsOfShape
  have : MorphismProperty.IsStableUnderComposition
      (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    (inferInstance : MorphismProperty.IsMultiplicative
      (@Etale.{u} : MorphismProperty Scheme.{u})).toIsStableUnderComposition
  have : MorphismProperty.IsStableUnderBaseChange
      (@Etale.{u} : MorphismProperty Scheme.{u}) := inferInstance
  let : P.IsStableUnderBaseChange := ⟨by
    intro X₁ X₂ X₃ Y₁ f₁ f₂ g₁ g₂ hs hg
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @Etale) (hs.map G) hg⟩
  let : P.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage G
  let : P.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition P
  have hs : P.presheaf (yoneda.map s) :=
    (MorphismProperty.relative_map_iff (P := P)).2 (hφ'.property φ (yoneda.map t) s hR)
  have ht : P.presheaf (yoneda.map t) :=
    (MorphismProperty.relative_map_iff (P := P)).2 (hφ'.property φ (yoneda.map s) t hR.flip)
  constructor
  · intro V ψ hψ
    exact MorphismProperty.comp_mem P.presheaf ψ (yoneda.map s) hψ hs
  · intro V ψ hψ
    exact MorphismProperty.comp_mem P.presheaf ψ (yoneda.map t) hψ ht

/-- An étale chart `φ : yoneda.obj U ⟶ X` with universally bounded fibres has a kernel pair
`R = U ×_X U` which is an étale equivalence relation on `U` whose two projections both have
universally bounded fibres. -/
theorem exists_chart_etale_equivalence_relation
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (U : AlgebraicGeometry.BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X)
    (hφ : AlgebraicGeometry.Space.IsEtale B S hS φ)
    (hbounded : HasUniversallyBoundedFibers B S hS U φ) :
    ∃ (R : AlgebraicGeometry.BigFppfOver B S hS) (s t : R ⟶ U),
      IsPullback (yoneda.map t) (yoneda.map s) φ φ ∧
      IsEquivalenceRelation ((Over.post B.inclusion).map t)
        ((Over.post B.inclusion).map s) ∧
      AlgebraicGeometry.Space.IsEtale B S hS (yoneda.map s) ∧
      AlgebraicGeometry.Space.IsEtale B S hS (yoneda.map t) ∧
      HasUniversallyBoundedFibers B S hS R (yoneda.map s) ∧
      HasUniversallyBoundedFibers B S hS R (yoneda.map t) := by
  obtain ⟨R, s, t, hR, hbounded_s⟩ :=
    exists_chart_kernel_pair_with_bounded_projection B S hS X hX U φ hbounded
  have he := chart_kernel_pair_projections_are_etale B S hS X U φ hφ R s t hR
  exact ⟨R, s, t, hR,
    isEquivalenceRelation_of_isPullback B S hS φ t s hR, he.1, he.2,
    hbounded_s,
    kernelPair_other_projection_hasUniversallyBoundedFibers
      B S hS φ s t hR hbounded_s⟩

/-- **The presentation used throughout.** A quasi-compact reasonable algebraic space `X` is
`U / R` for an affine `U`, a surjective étale chart `φ : yoneda.obj U ⟶ X` and its kernel pair
`R = U ×_X U`, which is an étale equivalence relation on `U`; all of `φ`, `s` and `t` have
universally bounded fibres (Stacks 03H6 together with Stacks 03JL). -/
private theorem exists_bounded_affine_etale_groupoid
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS X)
    (hr : IsReasonableSpace B S hS X) :
    ∃ (U : AlgebraicGeometry.BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X)
      (R : AlgebraicGeometry.BigFppfOver B S hS) (s t : R ⟶ U),
      IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U) ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf φ ∧
      AlgebraicGeometry.Space.IsEtale B S hS φ ∧
      IsPullback (yoneda.map t) (yoneda.map s) φ φ ∧
      IsEquivalenceRelation ((Over.post B.inclusion).map t)
        ((Over.post B.inclusion).map s) ∧
      AlgebraicGeometry.Space.IsEtale B S hS (yoneda.map s) ∧
      AlgebraicGeometry.Space.IsEtale B S hS (yoneda.map t) ∧
      HasUniversallyBoundedFibers B S hS U φ ∧
      HasUniversallyBoundedFibers B S hS R (yoneda.map s) ∧
      HasUniversallyBoundedFibers B S hS R (yoneda.map t) := by
  obtain ⟨U, φ, hU, hsurj, hφ, hbounded⟩ :=
    exists_affine_etale_surjective_bounded_chart B S hS X hX hqc hr
  obtain ⟨R, s, t, hR, heq, hs, ht, hRs, hRt⟩ :=
    exists_chart_etale_equivalence_relation B S hS X hX U φ hφ hbounded
  exact ⟨U, φ, R, s, t, hU, hsurj, hφ, hR, heq, hs, ht, hbounded, hRs, hRt⟩

end ReasonableApproximation

end AlgebraicGeometry.Space

end
