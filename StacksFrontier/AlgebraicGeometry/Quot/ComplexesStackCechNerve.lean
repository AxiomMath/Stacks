module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackDescent
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeDerivedHomSheafDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleAffineKFlatModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfPretopology
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringBySimplicialObject

/-!
# The Čech nerve of a Čech covering in `Complexes_{X/Y}`

A Čech covering `C : CechCover T I` of a test scheme `T` in `Complexes_{X/Y}` has its index
type `I` in `Type (u + 1)`, while Stacks 0DLA is applied to an fppf hypercovering of `X_T` by
algebraic spaces whose terms are disjoint unions of members of the covering. This file supplies
that hypercovering:

* a refinement of the covering indexed by a type in `Type u`, whose members are schemes of the
  site mapping to members of the covering over `T`, and whose disjoint union `V` (a scheme of the
  site) maps to `T` by a single fppf covering morphism `q : V ⟶ T`;
* the base change `X ×_Y Č(V/T) ⟶ X_T` of the Čech nerve of `q`, an augmented simplicial
  algebraic space over `X_T`, with the certificates that it is an fppf hypercovering both in the
  sense of `CategoryTheory.MorphismProperty.IsHypercovering` for the fppf covering morphisms
  (the sense of Stacks 0DL9 in this library) and as a hypercovering augmentation for the big fppf
  pretopology of algebraic spaces (Stacks 09X8, the sense of Stacks 0DHF and 0GMF).

## Main definitions

* `AlgebraicGeometry.Space.ComplexesSituation.CechCover.SmallRefinement`: a refinement of a Čech
  covering indexed by a type in `Type u`, with its disjoint union and fppf covering morphism.
* `AlgebraicGeometry.Space.ComplexesSituation.CechCover.smallRefinement`: a chosen one.
* `AlgebraicGeometry.Space.ComplexesSituation.CechCover.SmallRefinement.nerve`: the base change
  `X ×_Y Č(V/T) ⟶ X_T` of its Čech nerve.

## Main results

* `AlgebraicGeometry.Space.singleton_mem_pretopologyBigFppfPretopology_of_isFppfCovering`: a
  one-member fppf covering is a covering of the big fppf pretopology.
* `AlgebraicGeometry.Space.isHypercoveringAugmentation_bigFppf_of_isHypercovering`: an fppf
  hypercovering is a hypercovering augmentation for the big fppf pretopology.
* `AlgebraicGeometry.Space.ComplexesSituation.CechCover.SmallRefinement.isHypercovering_nerve`
  and `.isHypercoveringAugmentation_nerve`: the nerve is an fppf hypercovering of `X_T`.

## References

* [Stacks Project, Tag 0DLA](https://stacks.math.columbia.edu/tag/0DLA)
* [Stacks Project, Tag 0DHF](https://stacks.math.columbia.edu/tag/0DHF)
* [Stacks Project, Tag 09X8](https://stacks.math.columbia.edu/tag/09X8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open Stacks.CategoryTheory.Hypercovering

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

/-! ### Fppf hypercoverings as hypercovering augmentations -/

section Augmentation

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A one-member fppf covering is a covering of the big fppf pretopology** of algebraic spaces
over the big fppf site of schemes `B`: the chosen representative of the one-member family is
combinatorially equivalent to it, so it has the same presieve. -/
theorem singleton_mem_pretopologyBigFppfPretopology_of_isFppfCovering
    {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hf : IsFppfCovering B S hS (fun _ : Unit => Y.1) (fun _ => f.hom)) :
    Presieve.singleton f ∈
      (bigFppfSpaceSiteOfSchemeSite B S hS).pretopologyBigFppfPretopology X := by
  let T := bigFppfSpaceSiteOfSchemeSite B S hS
  let E₀ : PreZeroHypercover.{u + 2} X := PreZeroHypercover.singleton.{u + 2} f
  have h₀ : IsFppfCoveringFamily B S hS ⟨X, E₀⟩ :=
    IsFppfCovering.reindex B S hS hf (σ := fun _ : PUnit.{u + 3} => ())
      (fun _ => ⟨PUnit.unit, rfl⟩)
  obtain ⟨E₁, hE₁, hCE⟩ := T.covering_representative ⟨X, E₀⟩ h₀
  rcases E₁ with ⟨X₁, E₁⟩
  rcases hCE with ⟨hU, hCE'⟩
  change X = X₁ at hU
  subst hU
  have hpres := PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hCE'
  refine ⟨E₁, ?_, hE₁⟩
  exact (PreZeroHypercover.presieve₀_singleton.{_, _, u + 2} f).symm.trans hpres

/-- **An fppf hypercovering is a hypercovering augmentation for the big fppf pretopology.** An
augmentation `U_• ⟶ X` of algebraic spaces whose degree-zero augmentation, degree-one matching
morphism `U₁ ⟶ U₀ ×_X U₀` and higher matching morphisms are fppf coverings is a hypercovering
of `X` in the big fppf site of algebraic spaces (Stacks 09X8): the matching morphisms are the
same morphisms, and each generates a covering by
`AlgebraicGeometry.Space.singleton_mem_pretopologyBigFppfPretopology_of_isFppfCovering`. -/
theorem isHypercoveringAugmentation_bigFppf_of_isHypercovering
    (A : SimplicialObject.Augmented (AlgebraicSpaces B S hS))
    (hA : (fppfCoveringMorphisms B S hS).IsHypercovering A) :
    IsHypercoveringAugmentation
      (bigFppfSpaceSiteOfSchemeSite B S hS).pretopologyBigFppfPretopology A.left A.hom :=
  ⟨singleton_mem_pretopologyBigFppfPretopology_of_isFppfCovering B S hS _ hA.map_zero,
    singleton_mem_pretopologyBigFppfPretopology_of_isFppfCovering B S hS _ hA.map_one,
    fun n hn => singleton_mem_pretopologyBigFppfPretopology_of_isFppfCovering B S hS _
      (hA.matching n hn)⟩

end Augmentation

/-! ### The Čech nerve of a morphism of schemes of the site, as algebraic spaces -/

section SchemeCechNerve

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The schemes of a big fppf site over `S` have finite limits (Stacks 022K). -/
local instance hasFiniteLimits_bigFppfOver_of_siteCategory :
    HasFiniteLimits (BigFppfOver B S hS) :=
  haveI : HasFiniteLimits B.Schemes := hasFiniteLimits_siteCategory (τ := .fppf) B
  inferInstance

/-- **The inclusion of schemes into algebraic spaces preserves wide fibre products**: followed
by the inclusion of algebraic spaces into presheaves it is the Yoneda embedding. -/
instance schemeSpaceFunctor_preservesLimitsOfShape_widePullbackShape (J : Type) :
    PreservesLimitsOfShape (WidePullbackShape J) (schemeSpaceFunctor B S hS) := by
  have : PreservesLimitsOfShape (WidePullbackShape J)
      (schemeSpaceFunctor B S hS ⋙ ObjectProperty.ι _) :=
    preservesLimitsOfShape_of_natIso
      (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl) :
        yoneda ≅ schemeSpaceFunctor B S hS ⋙ ObjectProperty.ι _)
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (ObjectProperty.ι _)

/-- The projection of a one-fold wide fibre product is an isomorphism. -/
theorem isIso_widePullback_π_fin_one {C : Type*} [Category* C] {V T₀ : C} (q : V ⟶ T₀)
    [HasWidePullback T₀ (fun _ : Fin 1 => V) fun _ => q] :
    IsIso (WidePullback.π (fun _ : Fin 1 => q) 0) := by
  refine ⟨WidePullback.lift q (fun _ => 𝟙 V) (fun _ => Category.id_comp _), ?_,
    WidePullback.lift_π _ _ _ _ _⟩
  apply WidePullback.hom_ext
  · intro j
    obtain rfl : j = 0 := Fin.fin_one_eq_zero j
    rw [Category.assoc, WidePullback.lift_π, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, WidePullback.lift_base, Category.id_comp, WidePullback.π_arrow]

variable {V T₀ : BigFppfOver B S hS} (q : V ⟶ T₀)

/-- **The Čech nerve of a morphism `q : V ⟶ T₀` of schemes of the site, as an augmented
simplicial algebraic space**: the Čech nerve of `q` formed among the schemes of the site, its
terms `V ×_{T₀} ⋯ ×_{T₀} V` regarded as algebraic spaces. -/
def schemeCechNerve : SimplicialObject.Augmented (AlgebraicSpaces B S hS) where
  left := (Arrow.mk q).cechNerve ⋙ schemeSpaceFunctor B S hS
  right := (schemeSpaceFunctor B S hS).obj T₀
  hom :=
    { app := fun n => (schemeSpaceFunctor B S hS).map
        (WidePullback.base (fun _ : Fin (n.unop.len + 1) => q))
      naturality := fun n m g => by
        change (schemeSpaceFunctor B S hS).map _ ≫ (schemeSpaceFunctor B S hS).map _ =
          (schemeSpaceFunctor B S hS).map _ ≫ 𝟙 _
        rw [← Functor.map_comp, Category.comp_id]
        congr 1
        apply WidePullback.lift_base }

/-- The wide fibre products of the Čech nerve of `q`, as limits of algebraic spaces. -/
def isLimitSchemeCechNerveCone (n : ℕ) :=
  isLimitOfPreserves (schemeSpaceFunctor B S hS)
    (limit.isLimit (WidePullbackShape.wideCospan T₀ (fun _ : Fin (n + 1) => V) fun _ => q))

/-- A vertex map of the Čech nerve of `q`, followed by the unique coordinate of the degree-zero
term, is the coordinate of the vertex. -/
theorem schemeCechNerve_vertexMap_π (n : ℕ) (i : Fin (n + 1)) :
    (schemeCechNerve q).vertexMap n i ≫
        (schemeSpaceFunctor B S hS).map (WidePullback.π (fun _ : Fin 1 => q) 0) =
      (schemeSpaceFunctor B S hS).map (WidePullback.π (fun _ : Fin (n + 1) => q) i) :=
  ((schemeSpaceFunctor B S hS).map_comp _ _).symm.trans
    (congrArg (schemeSpaceFunctor B S hS).map
      (Arrow.augmentedCechNerve_vertexMap_π (Arrow.mk q) n i))

/-- The augmentation of the Čech nerve of `q` in degree `n`. -/
theorem schemeCechNerve_hom_app (n : ℕ) :
    (schemeCechNerve q).hom.app (op ⦋n⦌) =
      (schemeSpaceFunctor B S hS).map (WidePullback.base (fun _ : Fin (n + 1) => q)) :=
  rfl

/-- The degree-zero augmentation of the Čech nerve of `q` is `q` after the unique coordinate. -/
theorem schemeCechNerve_hom_app_zero :
    (schemeCechNerve q).hom.app (op ⦋0⦌) =
      (schemeSpaceFunctor B S hS).map (WidePullback.π (fun _ : Fin 1 => q) 0) ≫
        (schemeSpaceFunctor B S hS).map q :=
  (congrArg (schemeSpaceFunctor B S hS).map (WidePullback.π_arrow _ _).symm).trans
    ((schemeSpaceFunctor B S hS).map_comp _ _)

/-- A morphism into the degree-`n` term of the Čech nerve of `q`, as an algebraic space, is
determined by its coordinates and its composite to `T₀`. -/
theorem schemeCechNerve_hom_ext {n : ℕ} {Q : AlgebraicSpaces B S hS}
    {g h : Q ⟶ (schemeSpaceFunctor B S hS).obj (widePullback T₀ (fun _ : Fin (n + 1) => V)
      fun _ => q)}
    (hb : g ≫ (schemeSpaceFunctor B S hS).map (WidePullback.base (fun _ : Fin (n + 1) => q)) =
      h ≫ (schemeSpaceFunctor B S hS).map (WidePullback.base (fun _ : Fin (n + 1) => q)))
    (hi : ∀ i, g ≫ (schemeSpaceFunctor B S hS).map (WidePullback.π (fun _ : Fin (n + 1) => q) i) =
      h ≫ (schemeSpaceFunctor B S hS).map (WidePullback.π (fun _ : Fin (n + 1) => q) i)) :
    g = h :=
  (isLimitSchemeCechNerveCone q n).hom_ext fun j => by
    rcases j with _ | j
    · exact hb
    · exact hi j

/-- The lift into the degree-`n` term of the Čech nerve of `q`, as an algebraic space, of
coordinates `g i : Q ⟶ V` over `T₀`. -/
def schemeCechNerveLift {n : ℕ} {Q : AlgebraicSpaces B S hS}
    (b : Q ⟶ (schemeSpaceFunctor B S hS).obj T₀)
    (g : Fin (n + 1) → (Q ⟶ (schemeSpaceFunctor B S hS).obj V))
    (w : ∀ i, g i ≫ (schemeSpaceFunctor B S hS).map q = b) :
    Q ⟶ (schemeSpaceFunctor B S hS).obj (widePullback T₀ (fun _ : Fin (n + 1) => V)
      fun _ => q) :=
  (isLimitSchemeCechNerveCone q n).lift
    (WidePullbackShape.mkCone (F := WidePullbackShape.wideCospan T₀ (fun _ : Fin (n + 1) => V)
      (fun _ => q) ⋙ schemeSpaceFunctor B S hS) b g w)

/-- The lift `schemeCechNerveLift q b g w`, followed by the base projection to `T₀`, is `b`. -/
@[reassoc (attr := simp)]
theorem schemeCechNerveLift_base {n : ℕ} {Q : AlgebraicSpaces B S hS}
    (b : Q ⟶ (schemeSpaceFunctor B S hS).obj T₀)
    (g : Fin (n + 1) → (Q ⟶ (schemeSpaceFunctor B S hS).obj V))
    (w : ∀ i, g i ≫ (schemeSpaceFunctor B S hS).map q = b) :
    schemeCechNerveLift q b g w ≫
      (schemeSpaceFunctor B S hS).map (WidePullback.base (fun _ : Fin (n + 1) => q)) = b :=
  (isLimitSchemeCechNerveCone q n).fac _ none

/-- The lift `schemeCechNerveLift q b g w`, followed by the `i`-th projection to `V`, is
`g i`. -/
@[reassoc (attr := simp)]
theorem schemeCechNerveLift_π {n : ℕ} {Q : AlgebraicSpaces B S hS}
    (b : Q ⟶ (schemeSpaceFunctor B S hS).obj T₀)
    (g : Fin (n + 1) → (Q ⟶ (schemeSpaceFunctor B S hS).obj V))
    (w : ∀ i, g i ≫ (schemeSpaceFunctor B S hS).map q = b) (i : Fin (n + 1)) :
    schemeCechNerveLift q b g w ≫
      (schemeSpaceFunctor B S hS).map (WidePullback.π (fun _ : Fin (n + 1) => q) i) = g i :=
  (isLimitSchemeCechNerveCone q n).fac _ (some i)

/-- **The terms of the Čech nerve of `q`, as algebraic spaces, are the self-products of its
degree-zero term** over `T₀`, through the vertex maps. -/
def isLimitVertexFanSchemeCechNerve (n : ℕ) :
    IsLimit (Fan.mk ((schemeCechNerve q).over.obj (op ⦋n⦌))
      ((schemeCechNerve q).overProj (schemeCechNerve q).vertexMap
        (schemeCechNerve q).vertexMap_comp_hom n)) := by
  have hw : ∀ (s : Fan fun _ : Fin (n + 1) => (schemeCechNerve q).over.obj (op ⦋0⦌))
      (i : Fin (n + 1)), ((s.proj i).left ≫
        (schemeSpaceFunctor B S hS).map (WidePullback.π (fun _ : Fin 1 => q) 0)) ≫
          (schemeSpaceFunctor B S hS).map q = s.pt.hom := fun s i =>
    (Category.assoc _ _ _).trans
      ((congrArg _ (schemeCechNerve_hom_app_zero q).symm).trans (Over.w (s.proj i)))
  refine Fan.IsLimit.mk _ (fun s => Over.homMk (schemeCechNerveLift q s.pt.hom _ (hw s))
    (schemeCechNerveLift_base q _ _ _)) (fun s i => ?_) (fun s m hm => ?_)
  · refine Over.OverMorphism.ext ?_
    change schemeCechNerveLift q s.pt.hom _ (hw s) ≫ (schemeCechNerve q).vertexMap n i =
      (s.proj i).left
    refine schemeCechNerve_hom_ext q (n := 0) ?_ fun j => ?_
    · exact (Category.assoc _ _ _).trans
        ((congrArg _ ((schemeCechNerve q).vertexMap_comp_hom n i)).trans
          ((schemeCechNerveLift_base q _ _ _).trans (Over.w (s.proj i)).symm))
    · obtain rfl : j = 0 := Fin.fin_one_eq_zero j
      exact (Category.assoc _ _ _).trans
        ((congrArg _ (schemeCechNerve_vertexMap_π q n i)).trans
          (schemeCechNerveLift_π q _ _ _ i))
  · refine Over.OverMorphism.ext ?_
    change m.left = schemeCechNerveLift q s.pt.hom _ (hw s)
    refine schemeCechNerve_hom_ext q ?_ fun j => ?_
    · exact (Over.w m).trans (schemeCechNerveLift_base q _ _ _).symm
    · refine ((congrArg (m.left ≫ ·) (schemeCechNerve_vertexMap_π q n j)).symm.trans
        ((Category.assoc _ _ _).symm.trans ?_)).trans (schemeCechNerveLift_π q _ _ _ j).symm
      exact congrArg (· ≫ _) (congrArg CommaMorphism.left (hm j))

/-- **The base change of the Čech nerve of an fppf covering of schemes is an fppf
hypercovering**: for `q : V ⟶ T₀` an fppf covering and `t : T₀ ⟶ Y`, the base change
`X ×_Y Č(V/T₀) ⟶ X_{T₀}` along `f : X ⟶ Y` is an fppf hypercovering of `X_{T₀}`. -/
theorem isHypercovering_augmentedBaseChange_schemeCechNerve {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (t : (schemeSpaceFunctor B S hS).obj T₀ ⟶ Y)
    (hq : fppfCoveringMorphisms B S hS ((schemeSpaceFunctor B S hS).map q)) :
    (fppfCoveringMorphisms B S hS).IsHypercovering
      (augmentedBaseChange f (schemeCechNerve q) t) := by
  refine MorphismProperty.isHypercovering_of_isLimit_vertexFan _ _
    (fun n => isLimitVertexFanAugmentedBaseChange f (schemeCechNerve q) t
      (fun k => isLimitVertexFanSchemeCechNerve q k) n) ?_
  refine fppfCoveringMorphisms_of_isPullback
    (isPullback_overBaseChangeMap f (augmentedOverHom (schemeCechNerve q) t _)) ?_
  have := isIso_widePullback_π_fin_one q
  have h := fppfCoveringMorphisms_comp _ _
    (fppfCoveringMorphisms_of_isIso
      ((schemeSpaceFunctor B S hS).map (WidePullback.π (fun _ : Fin 1 => q) 0))) hq
  rw [← Functor.map_comp, WidePullback.π_arrow] at h
  exact h

end SchemeCechNerve

/-! ### A refinement of a Čech covering indexed by a type in `Type u` -/

namespace ComplexesSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {D : ComplexesSituation B S hS}

namespace CechCover

variable {T : SchemesOver D.Y} {I : Type (u + 1)} (C : CechCover T I)

/-- **A refinement of a Čech covering indexed by a type in `Type u`.** Schemes `W k` of the site,
`k : ι` with `ι : Type u`, each mapping by `h k` to the member `T_{σ k}` of the covering, whose
disjoint union `V` (a coproduct of the underlying schemes, with the injections `j k`) maps to `T`
by a single fppf covering morphism `q`, compatibly with the members of the covering. -/
structure SmallRefinement where
  /-- The index type of the refinement. -/
  ι : Type u
  /-- The members of the refinement. -/
  W : ι → BigFppfOver B S hS
  /-- The disjoint union of the members. -/
  V : BigFppfOver B S hS
  /-- The injections into the disjoint union. -/
  j : ∀ k, W k ⟶ V
  /-- The disjoint union is the coproduct of the underlying schemes. -/
  isColimit : IsColimit (Cofan.mk ((BigFppfOver.toScheme B S hS).obj V)
    fun k => (BigFppfOver.toScheme B S hS).map (j k))
  /-- The morphism from the disjoint union to `T`. -/
  q : V ⟶ T.left
  /-- It is an fppf covering on its own. -/
  fppf : fppfCoveringMorphisms B S hS ((schemeSpaceFunctor B S hS).map q)
  /-- Its singleton sieve is a covering sieve of the big fppf site. -/
  covering : Sieve.ofArrows (fun _ : PUnit.{u + 1} => V) (fun _ => q) ∈
    BigFppfOver.topology B S hS T.left
  /-- The member of the covering each member of the refinement maps to. -/
  σ : ι → I
  /-- The morphisms to the members of the covering. -/
  h : ∀ k, W k ⟶ (C.X (σ k)).T.left
  /-- They lie over `T`. -/
  fac : ∀ k, h k ≫ (C.a (σ k)).left = j k ≫ q

/-- A flat, surjective morphism locally of finite presentation of schemes of the site is an fppf
covering morphism of the algebraic spaces they represent. -/
theorem fppfCoveringMorphisms_schemeSpaceFunctor_map {U W : BigFppfOver B S hS} (q : U ⟶ W)
    (hs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hf : Flat ((BigFppfOver.toScheme B S hS).map q))
    (hp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map q)) :
    fppfCoveringMorphisms B S hS ((schemeSpaceFunctor B S hS).map q) :=
  isFppfCovering_yoneda_map.{u, 0} B S hS (U := W) (fun _ : Unit => U) (fun _ => q)
    (fun _ => hf) (fun _ => hp) (fun x => by
      obtain ⟨y, hy⟩ := hs.surj x
      exact ⟨(), y, hy⟩)

/-- **A Čech covering has a refinement indexed by a type in `Type u`**: the fppf covering
`{a i : T i ⟶ T}` is refined by a single flat, surjective morphism locally of finite
presentation out of a disjoint union of schemes of the site, each mapping to a member
(`AlgebraicGeometry.Space.exists_flat_sigma_refinement_of_mem_topology`). -/
theorem nonempty_smallRefinement : Nonempty C.SmallRefinement := by
  obtain ⟨ι, W, V, j, q, g, hgS, hjq, ⟨hV⟩, hqs, hqf, hqp⟩ :=
    exists_flat_sigma_refinement_of_mem_topology T.left C.covers
  have hmem : ∀ k, ∃ (i : I) (h : W k ⟶ (C.X i).T.left), g k = h ≫ (C.a i).left :=
    fun k => (Sieve.mem_ofArrows_iff _ _ _).mp (hgS k)
  choose σ h hh using hmem
  exact ⟨{ ι := ι, W := W, V := V, j := j, isColimit := hV, q := q
           fppf := fppfCoveringMorphisms_schemeSpaceFunctor_map q hqs hqf hqp
           covering := BigFppfOver.ofArrows_mem_topology_of_flat_lfp B S hS
             (fun _ : PUnit.{u + 1} => V) (fun _ => q)
             (fun x => ⟨PUnit.unit, hqs.surj x⟩) (fun _ => hqf) (fun _ => hqp)
           σ := σ, h := h
           fac := fun k => (hh k).symm.trans (hjq k).symm }⟩

/-- A chosen refinement of a Čech covering indexed by a type in `Type u`. -/
def smallRefinement : C.SmallRefinement :=
  Classical.choice C.nonempty_smallRefinement

namespace SmallRefinement

variable {C} (R : C.SmallRefinement)

/-- The algebraic spaces over `S` have finite limits: a final object and fibre products. -/
local instance hasFiniteLimits_algebraicSpaces_of_hasTerminal_and_pullbacks :
    HasFiniteLimits (AlgebraicSpaces B S hS) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- **The Čech nerve of a refinement, base changed to `X`.** The base change
`X ×_Y Č(V/T) ⟶ X_T` along `f : X ⟶ Y` of the Čech nerve of the fppf covering `q : V ⟶ T`
(formed among the schemes of the site), an augmented simplicial algebraic space over `X_T`. -/
def nerve : SimplicialObject.Augmented (AlgebraicSpaces B S hS) :=
  augmentedBaseChange D.f (schemeCechNerve R.q) T.hom

/-- The base of the nerve is `X_T`. -/
theorem nerve_right : R.nerve.right = D.space T :=
  rfl

-- The schemes of a big fppf site over `S` have finite limits (Stacks 022K).
attribute [local instance] hasFiniteLimits_bigFppfOver_of_siteCategory

/-- The degree-`n` term `V ×_T ⋯ ×_T V` of the Čech nerve of a refinement, as a test scheme over
`Y`. -/
abbrev testScheme (n : ℕ) : SchemesOver D.Y :=
  CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map
    (WidePullback.base (fun _ : Fin (n + 1) => R.q)) ≫ T.hom)

/-- The augmentation `V ×_T ⋯ ×_T V ⟶ T` of the Čech nerve of a refinement, as a morphism of test
schemes over `Y`. -/
abbrev testSchemeHom (n : ℕ) : R.testScheme n ⟶ T :=
  CostructuredArrow.homMk (WidePullback.base (fun _ : Fin (n + 1) => R.q))

/-- The simplicial structure maps of the Čech nerve of a refinement, as morphisms of test
schemes over `Y`. -/
abbrev testSchemeMap {n m : ℕ} (g : ⦋n⦌ ⟶ ⦋m⦌) : R.testScheme m ⟶ R.testScheme n :=
  CostructuredArrow.homMk ((Arrow.mk R.q).cechNerve.map g.op) (by
    change (schemeSpaceFunctor B S hS).map _ ≫ (schemeSpaceFunctor B S hS).map _ ≫ T.hom = _
    rw [← Category.assoc, ← Functor.map_comp]
    congr 2
    apply WidePullback.lift_base)

/-- The terms of the nerve are the base changes `X_{V ×_T ⋯ ×_T V}`. -/
theorem nerve_left_obj (n : ℕ) : R.nerve.left.obj (op ⦋n⦌) = D.space (R.testScheme n) :=
  rfl

/-- The simplicial structure maps of the nerve are the morphisms of base changes induced by those
of the Čech nerve of the refinement. -/
theorem nerve_left_map {n m : ℕ} (g : ⦋n⦌ ⟶ ⦋m⦌) :
    R.nerve.left.map g.op = D.relativeMap (R.testSchemeMap g) :=
  rfl

/-- The augmentation of the nerve is the morphism of base changes induced by the augmentation
of the Čech nerve of the refinement. -/
theorem nerve_hom_app (n : ℕ) :
    R.nerve.hom.app (op ⦋n⦌) = D.relativeMap (R.testSchemeHom n) :=
  rfl

/-- **The nerve is an fppf hypercovering** of `X_T`, in the sense of the fppf covering morphisms
(the sense of Stacks 0DL9 in this library). -/
theorem isHypercovering_nerve : (fppfCoveringMorphisms B S hS).IsHypercovering R.nerve :=
  isHypercovering_augmentedBaseChange_schemeCechNerve R.q D.f T.hom R.fppf

/-- **The nerve is a hypercovering augmentation for the big fppf pretopology** of algebraic
spaces (Stacks 09X8), the sense of Stacks 0DHF and Stacks 0GMF. -/
theorem isHypercoveringAugmentation_nerve :
    IsHypercoveringAugmentation
      (bigFppfSpaceSiteOfSchemeSite B S hS).pretopologyBigFppfPretopology R.nerve.left
      R.nerve.hom :=
  isHypercoveringAugmentation_bigFppf_of_isHypercovering B S hS R.nerve R.isHypercovering_nerve

end SmallRefinement

end CechCover

end ComplexesSituation

end AlgebraicGeometry.Space

end
