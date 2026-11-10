module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Localization.Adjunction
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import StacksFrontier.CategoryTheory.Sites.LocalImageSheaf
public import StacksFrontier.Topology.Sheaves.Sheaf.Abelian

/-!
# Cohomology of abelian sheaves along a closed immersion

Let `i : Z ⟶ X` be a closed immersion of topological spaces. For every abelian sheaf `F` on
`Z` the cohomology `H^p(Z, F)` agrees with `H^p(X, i_* F)` in every degree, by a comparison
isomorphism that is natural in `F`.

## Main definitions

* `Stacks.ClosedImmersion.abelianSheafPushforward` is pushforward of abelian sheaves along a
  continuous map, with the site-sheaf instances made explicit.
* `Stacks.ClosedImmersion.constantSheafPushforwardHom` is the canonical map from the constant
  sheaf on the ambient space to the pushforward of the constant sheaf on the subspace.
* `Stacks.ClosedImmersion.cohomologyPushforwardComparison` is the derived global-sections
  comparison of an exact pushforward: apply it to an `Ext` class and precompose with the
  canonical map of constant sheaves.
* `Stacks.ClosedImmersion.HasCohomologyPushforwardIso` bundles exactness of a pushforward with
  invertibility of that comparison in every degree.
* `Stacks.ClosedImmersion.cohomologyPushforwardIso` is the resulting natural isomorphism
  `H^p(Z, -) ≅ H^p(X, i_* -)`.

## Main results

* `Stacks.ClosedImmersion.hasCohomologyPushforwardIso_of_isClosedEmbedding`: a closed embedding
  has exact pushforward and an invertible cohomology comparison.
* `Stacks.ClosedImmersion.cohomologyPushforwardIso_hom_apply` identifies the comparison in
  every degree with the map on `Ext` induced by the exact pushforward.
* `Stacks.ClosedImmersion.cohomologyPushforwardIso_hom_extClass` computes it on the class of a
  short exact sequence.

## Implementation notes

Sheaf cohomology is `Ext` out of the constant sheaf of integers, so the derived global-sections
comparison for the identity `Γ_Z = Γ_X ∘ i_*` is obtained by applying the exact pushforward to
an `Ext` class and precomposing with the canonical map of constant sheaves, the latter being
the adjoint of the unit of the constant-sheaf/global-sections adjunction on `Z`. This pins the
comparison down, signs included, in every degree.

Invertibility comes from an adjunction between exact functors. Pushforward along `i` is left
exact because on underlying presheaves it is precomposition with `Opens.map i`, and right exact
because it preserves epimorphisms: an epimorphism of abelian sheaves is locally surjective, and
a section of `i_* F` over an open `U` of `X` lifts locally — near a point of the image because
`i` is inducing, and over the complement of the image, which is open, because `i_* F` vanishes
there. That same support property produces a left adjoint of `i_*`. A sheaf on `X` is first
replaced by its reflection, obtained by killing the sections over every open contained in the
complement of the image and resheafifying; the reflection is supported on the image, hence is
the pushforward of a sheaf on `Z`, namely its restriction along the open-set extension functor
of the closed embedding. Killing sections preserves limits, checked one open at a time, and
sheafification is left exact, so the reflection and therefore the left adjoint are left exact.

An adjunction between exact functors lifts to the derived categories, and the degree-zero
single-object functor is fully faithful; so the bijectivity on morphisms of composition with
the canonical map of constant sheaves — which is the content of the two constant-sheaf
adjunctions — upgrades to invertibility of its derived adjunct, and thus to bijectivity on
`Ext` in every degree.

## References

* [Stacks Project, Tag 02UV](https://stacks.math.columbia.edu/tag/02UV)
* [Stacks Project, Tag 01AX](https://stacks.math.columbia.edu/tag/01AX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u w w'

namespace Stacks.ClosedImmersion

/-- The usual pushforward, with the site-sheaf category instances made explicit.
This is definitionally `TopCat.Sheaf.pushforward AddCommGrpCat i`. -/
public abbrev abelianSheafPushforward {X Z : TopCat.{u}} (i : Z ⟶ X) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{w} ⥤
      CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w} :=
  (Opens.map i).sheafPushforwardContinuous AddCommGrpCat.{w}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)

variable {X Z : TopCat.{u}}
    [hSheafZ : HasSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{w}]
    [hSheafX : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{w}]

/-- The canonical map of constant sheaves, adjoint to the unit of the
constant-sheaf/global-sections adjunction on the source. -/
public noncomputable def constantSheafPushforwardHom (i : Z ⟶ X) (A : AddCommGrpCat.{w}) :
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w}).obj A ⟶
      (abelianSheafPushforward.{u, w} i).obj
        ((constantSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{w}).obj A) :=
  ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{w}
    (isTerminalTop : IsTerminal (⊤ : Opens X))).homEquiv _ _).symm
      ((constantSheafAdj (Opens.grothendieckTopology Z) AddCommGrpCat.{w}
        (isTerminalTop : IsTerminal (⊤ : Opens Z))).unit.app A)

/-- Pushforward of abelian sheaves is additive. -/
public instance additive_abelianSheafPushforward (i : Z ⟶ X) :
    (abelianSheafPushforward.{u, w} i).Additive where
  map_add := by
    intro F G f g
    apply CategoryTheory.Sheaf.hom_ext
    ext U x
    rfl

variable
    [hExtZ : HasExt.{w'}
      (CategoryTheory.Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{w})]
    [hExtX : HasExt.{w'}
      (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w})]

-- The naturality square below is stated directly on `Abelian.Ext`; unification has to see
-- `((Sheaf.functorH J p).obj F)` as `Abelian.Ext _ F p` and `(Sheaf.functorH J p).map f` as
-- `Sheaf.H.map f p`, which are definitional but invisible at `implicit` transparency.
attribute [local implicit_reducible] CategoryTheory.Sheaf.functorH in
/-- The derived global-sections comparison for an exact pushforward, expressed
on Mathlib's `Ext` model of sheaf cohomology. -/
public noncomputable def cohomologyPushforwardComparison (i : Z ⟶ X)
    [PreservesFiniteLimits (abelianSheafPushforward.{u, w} i)]
    [PreservesFiniteColimits (abelianSheafPushforward.{u, w} i)] (p : ℕ) :
    (@CategoryTheory.Sheaf.functorH _ _ (Opens.grothendieckTopology Z)
      hSheafZ hExtZ p) ⟶
      abelianSheafPushforward.{u, w} i ⋙
        (@CategoryTheory.Sheaf.functorH _ _ (Opens.grothendieckTopology X)
          hSheafX hExtX p) where
  app F := AddCommGrpCat.ofHom
    (((@Abelian.Ext.mk₀ _ _ _ hExtX _ _
      (constantSheafPushforwardHom i (AddCommGrpCat.of (ULift.{w} ℤ)))).precomp.{w'} _
        (zero_add p)).comp
          ((abelianSheafPushforward.{u, w} i).mapExtAddHom.{w', w'} _ F p))
  naturality {F G} f := by
    apply AddCommGrpCat.ext
    intro x
    change (Abelian.Ext.mk₀ (constantSheafPushforwardHom i (AddCommGrpCat.of (ULift.{w} ℤ)))).comp
      ((x.comp (Abelian.Ext.mk₀ f) (add_zero p)).mapExactFunctor
        (abelianSheafPushforward.{u, w} i)) (zero_add p) =
      ((Abelian.Ext.mk₀ (constantSheafPushforwardHom i (AddCommGrpCat.of (ULift.{w} ℤ)))).comp
        (x.mapExactFunctor (abelianSheafPushforward.{u, w} i)) (zero_add p)).comp
          (Abelian.Ext.mk₀ ((abelianSheafPushforward.{u, w} i).map f)) (add_zero p)
    rw [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
      Abelian.Ext.comp_assoc_of_third_deg_zero]

/-- Exactness of pushforward together with invertibility of its canonical
cohomology comparison in every degree. -/
public structure HasCohomologyPushforwardIso (i : Z ⟶ X) : Prop where
  /-- Pushforward of abelian sheaves along `i` preserves finite limits. -/
  preservesFiniteLimits : PreservesFiniteLimits (abelianSheafPushforward.{u, w} i)
  /-- Pushforward of abelian sheaves along `i` preserves finite colimits. -/
  preservesFiniteColimits : PreservesFiniteColimits (abelianSheafPushforward.{u, w} i)
  /-- The comparison map `H^p(Z, F) ⟶ H^p(X, i_* F)` is an isomorphism for every `p`. -/
  isIso (p : ℕ) :
    letI := preservesFiniteLimits
    letI := preservesFiniteColimits
    IsIso (cohomologyPushforwardComparison (hExtZ := hExtZ) (hExtX := hExtX) i p)

open ZeroObject
attribute [local instance] Classical.propDecidable

private def complementOpen {X Z : TopCat.{u}} (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i) :
    Opens X := ⟨(Set.range i)ᶜ, hi.isClosed_range.isOpen_compl⟩

private abbrev closedPushforward {X Z : TopCat.{u}} (i : Z ⟶ X) :
    Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{w} ⥤
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w} :=
  (Opens.map i).sheafPushforwardContinuous _ _ _

private lemma closedPushforward_supported {X Z : TopCat.{u}} (i : Z ⟶ X)
    (hi : Topology.IsClosedEmbedding i)
    (G : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{w})
    (V : (Opens X)ᵒᵖ) (hV : V.unop ≤ complementOpen i hi) :
    IsZero (((closedPushforward i).obj G).obj.obj V) := by
  apply (TopCat.Sheaf.isTerminalOfEqEmpty G ?_).isZero
  exact le_antisymm (fun z hz => (hV hz ⟨z, rfl⟩).elim) bot_le

section LocalImage
universe v
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
private lemma sheafification_isZero [HasSheafify J AddCommGrpCat.{w}]
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (U : C)
    (hP : ∀ (V : C) (_ : V ⟶ U), IsZero (P.obj (op V))) :
    IsZero (((presheafToSheaf J AddCommGrpCat.{w}).obj P).obj.obj (op U)) := by
  let G := (presheafToSheaf J AddCommGrpCat.{w}).obj P
  have := Stacks.Sites.LocalImage.isLocallySurjective_toSheafify J P
  have hG : Presieve.IsSheaf J (G.obj ⋙ forget AddCommGrpCat.{w}) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      (Presheaf.isSheaf_comp_of_isSheaf J G.obj (forget AddCommGrpCat.{w}) G.property)
  have hz (s : G.obj.obj (op U)) : s = 0 := by
    apply (hG.isSeparated _ (Presheaf.imageSieve_mem J (toSheafify J P) s)).ext
    rintro V g ⟨t, ht⟩
    change G.obj.map g.op s = G.obj.map g.op 0
    have : Subsingleton (P.obj (op V)) := AddCommGrpCat.subsingleton_of_isZero (hP V g)
    rw [← ht, Subsingleton.elim t 0, map_zero, map_zero]
  exact AddCommGrpCat.isZero_iff_subsingleton.mpr ⟨fun a b => (hz a).trans (hz b).symm⟩

private lemma isLocallySurjective_map_abelianSheafPushforward
    {X Z : TopCat.{u}} (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i)
    {F G : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{w}} (f : F ⟶ G)
    [Sheaf.IsLocallySurjective f] :
    Sheaf.IsLocallySurjective ((abelianSheafPushforward.{u,w} i).map f) := by
  constructor
  intro U s
  change G.obj.obj (op ((Opens.map i).obj U)) at s
  change Presheaf.imageSieve (Functor.whiskerLeft (Opens.map i).op f.hom) s ∈ _
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  by_cases hxi : x ∈ Set.range i
  · obtain ⟨z, rfl⟩ := hxi
    have hs := Presheaf.imageSieve_mem (Opens.grothendieckTopology Z) f.hom s
    rw [Opens.mem_grothendieckTopology] at hs
    obtain ⟨V, g, ⟨t, ht⟩, hz⟩ := hs z hx
    let W := hi.isInducing.functor.obj V ⊓ U
    have hWV : (Opens.map i).obj W = V := by
      change (Opens.map i).obj (hi.isInducing.functorObj V) ⊓ (Opens.map i).obj U = V
      rw [hi.isInducing.map_functorObj, inf_eq_left.mpr g.le]
    refine ⟨W, homOfLE inf_le_right, ?_, ⟨?_, hx⟩⟩
    · refine ⟨F.obj.map (eqToHom hWV).op t, ?_⟩
      change f.hom.app _ (F.obj.map (eqToHom hWV).op t) =
        G.obj.map ((Opens.map i).map (homOfLE inf_le_right)).op s
      rw [← ConcreteCategory.comp_apply, f.hom.naturality, ConcreteCategory.comp_apply, ht,
        ← ConcreteCategory.comp_apply, ← G.obj.map_comp]
      congr 2
    · exact (hi.isInducing.mem_functorObj_iff V).mpr hz
  · have : Subsingleton (G.obj.obj (op ((Opens.map i).obj (complementOpen i hi ⊓ U)))) :=
      AddCommGrpCat.subsingleton_of_isZero
        (closedPushforward_supported i hi G (op _) inf_le_left)
    exact ⟨complementOpen i hi ⊓ U, homOfLE inf_le_right, ⟨0, Subsingleton.elim _ _⟩, ⟨hxi, hx⟩⟩

private lemma closedPushforward_preservesEpimorphisms
    {X Z : TopCat.{u}} [HasSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{w}]
    (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i) :
    (abelianSheafPushforward.{u,w} i).PreservesEpimorphisms := by
  constructor
  intro F G f hf
  have := Stacks.Sites.LocalImage.epi_localSurjective (Opens.grothendieckTopology Z) f
  have := isLocallySurjective_map_abelianSheafPushforward i hi f
  let : (Opens.grothendieckTopology X).HasSheafCompose (forget AddCommGrpCat.{w}) :=
    ⟨fun F hF => Presheaf.isSheaf_comp_of_isSheaf _ _ _ hF⟩
  exact Sheaf.epi_of_isLocallySurjective _

private lemma closedPushforward_preservesFiniteColimits
    {X Z : TopCat.{u}} [HasSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{w}]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{w}]
    (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i)
    [PreservesFiniteLimits (abelianSheafPushforward.{u, w} i)] :
    PreservesFiniteColimits (abelianSheafPushforward.{u,w} i) := by
  let T := abelianSheafPushforward.{u,w} i
  have := closedPushforward_preservesEpimorphisms i hi
  apply (T.preservesFiniteColimits_tfae.out 1 4).mp
  intro S hS
  have : Epi S.g := hS.epi_g
  have : PreservesLimitsOfShape WalkingParallelPair T :=
    PreservesFiniteLimits.preservesFiniteLimits _
  exact ⟨ShortComplex.exact_of_f_is_kernel _ (KernelFork.mapIsLimit _ hS.fIsKernel T),
    inferInstance⟩

end LocalImage
section KillSectionsOnAnOpen
variable {X : TopCat.{u}} (U : Opens X)
private def killObj (F : X.Presheaf AddCommGrpCat.{w}) (V : (Opens X)ᵒᵖ) : AddCommGrpCat.{w} :=
  if V.unop ≤ U then 0 else F.obj V

private lemma killObj_out (F : X.Presheaf AddCommGrpCat.{w}) (V : (Opens X)ᵒᵖ) (h : ¬ V.unop ≤ U) :
    killObj U F V = F.obj V := ite_eq_right h

private lemma killObj_zero (F : X.Presheaf AddCommGrpCat.{w}) (V : (Opens X)ᵒᵖ) (h : V.unop ≤ U) :
    IsZero (killObj U F V) := by
  rw [killObj, ite_eq_left h]
  exact isZero_zero _

private def killMap (F : X.Presheaf AddCommGrpCat.{w}) {V W : (Opens X)ᵒᵖ} (g : V ⟶ W) :
    killObj U F V ⟶ killObj U F W :=
  if hW : W.unop ≤ U then 0 else
    eqToHom (killObj_out U F V (fun hV => hW (g.unop.le.trans hV))) ≫ F.map g ≫
      eqToHom (killObj_out U F W hW).symm

private def killPresheaf (F : X.Presheaf AddCommGrpCat.{w}) : X.Presheaf AddCommGrpCat.{w} where
  obj := killObj U F
  map := killMap U F
  map_id V := by
    by_cases hV : V.unop ≤ U
    · exact (killObj_zero U F V hV).eq_of_tgt _ _
    · simp [killMap, hV]
  map_comp {V W T} f g := by
    by_cases hT : T.unop ≤ U
    · exact (killObj_zero U F T hT).eq_of_tgt _ _
    · have hW : ¬ W.unop ≤ U := fun h => hT (g.unop.le.trans h)
      simp [killMap, hT, hW]

-- Unification has to see `(killPresheaf U F).obj V` as `killObj U F V` (and likewise for the
-- maps): every `eqToHom (killObj_out …)` below is stated through `killObj`, and without this
-- the goals are ill-typed at `implicit` transparency, so `simp`/`rw` never start matching.
attribute [local implicit_reducible] killPresheaf

private def killπ (F : X.Presheaf AddCommGrpCat.{w}) : F ⟶ killPresheaf U F where
  app V := if hV : V.unop ≤ U then 0 else eqToHom (killObj_out U F V hV).symm
  naturality {V W} g := by
    by_cases hW : W.unop ≤ U
    · exact (killObj_zero U F W hW).eq_of_tgt _ _
    · have hV : ¬ V.unop ≤ U := fun h => hW (g.unop.le.trans h)
      change F.map g ≫ _ = _ ≫ killMap U F g
      simp [hV, hW, killMap]

private instance killπ_epi (F : X.Presheaf AddCommGrpCat.{w}) : Epi (killπ U F) := by
  have (V : (Opens X)ᵒᵖ) : Epi ((killπ U F).app V) := by
    by_cases hV : V.unop ≤ U
    · exact (killObj_zero U F V hV).epi _
    · dsimp [killπ]
      rw [dite_eq_right hV]
      infer_instance
  exact NatTrans.epi_of_epi_app _

private def killMapNat {F G : X.Presheaf AddCommGrpCat.{w}} (f : F ⟶ G) :
    killPresheaf U F ⟶ killPresheaf U G where
  app V := if hV : V.unop ≤ U then 0 else
    eqToHom (killObj_out U F V hV) ≫ f.app V ≫ eqToHom (killObj_out U G V hV).symm
  naturality {V W} g := by
    by_cases hW : W.unop ≤ U
    · exact (killObj_zero U G W hW).eq_of_tgt _ _
    · have hV : ¬ V.unop ≤ U := fun h => hW (g.unop.le.trans h)
      change killMap U F g ≫ _ = _ ≫ killMap U G g
      simp only [killMap, dite_eq_right hW, dite_eq_right hV, Category.assoc,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [f.naturality_assoc]

attribute [local implicit_reducible] killMapNat

private lemma killπ_naturality {F G : X.Presheaf AddCommGrpCat.{w}} (f : F ⟶ G) :
    killπ U F ≫ killMapNat U f = f ≫ killπ U G := by
  apply NatTrans.ext
  funext V
  by_cases hV : V.unop ≤ U
  · exact (killObj_zero U G V hV).eq_of_tgt _ _
  · simp [killπ, killMapNat, hV]

private def killFunctor : X.Presheaf AddCommGrpCat.{w} ⥤ X.Presheaf AddCommGrpCat.{w} where
  obj := killPresheaf U
  map := killMapNat U
  map_id F := by
    apply (cancel_epi (killπ U F)).mp
    simp [killπ_naturality]
  map_comp f g := by
    apply (cancel_epi (killπ U _)).mp
    rw [killπ_naturality, ← Category.assoc, killπ_naturality]
    simp only [Category.assoc, killπ_naturality]

private lemma killPreservesLimits : PreservesLimitsOfSize.{0,0} (killFunctor.{u,w} U) := by
  apply preservesLimits_of_evaluation
  intro V
  by_cases hV : V.unop ≤ U
  · constructor
    intro J inst
    constructor
    intro D
    constructor
    intro c hc
    exact ⟨{
      lift := fun s => (killObj_zero U c.pt V hV).from_ _
      fac := fun s j => (killObj_zero U (D.obj j) V hV).eq_of_tgt _ _
      uniq := fun s m hm => (killObj_zero U c.pt V hV).eq_of_tgt _ _ }⟩
  · let e : killFunctor U ⋙ (evaluation _ _).obj V ≅ (evaluation _ _).obj V :=
      NatIso.ofComponents (fun F => eqToIso (killObj_out U F V hV)) (by
        intro F G f
        change (killMapNat U f).app V ≫ eqToHom (killObj_out U G V hV) =
          eqToHom (killObj_out U F V hV) ≫ f.app V
        simp [killMapNat, hV])
    have : PreservesLimitsOfSize.{0,0}
        ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{w}).obj V) := ⟨by intros; infer_instance⟩
    exact preservesLimits_of_natIso e.symm

private def killLift {F G : X.Presheaf AddCommGrpCat.{w}}
    (hG : ∀ V : (Opens X)ᵒᵖ, V.unop ≤ U → IsZero (G.obj V)) (f : F ⟶ G) :
    killPresheaf U F ⟶ G where
  app V := if hV : V.unop ≤ U then 0 else eqToHom (killObj_out U F V hV) ≫ f.app V
  naturality {V W} g := by
    by_cases hW : W.unop ≤ U
    · exact (hG W hW).eq_of_tgt _ _
    · have hV : ¬ V.unop ≤ U := fun h => hW (g.unop.le.trans h)
      change killMap U F g ≫ _ = _ ≫ G.map g
      simp only [killMap, dite_eq_right hW, dite_eq_right hV, Category.assoc, eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp]
      rw [f.naturality]

private lemma killLift_fac {F G : X.Presheaf AddCommGrpCat.{w}}
    (hG : ∀ V : (Opens X)ᵒᵖ, V.unop ≤ U → IsZero (G.obj V)) (f : F ⟶ G) :
    killπ U F ≫ killLift U hG f = f := by
  apply NatTrans.ext
  funext V
  by_cases hV : V.unop ≤ U
  · exact (hG V hV).eq_of_tgt _ _
  · simp [killπ, killLift, hV]

end KillSectionsOnAnOpen

section Realization
variable {X Z : TopCat.{u}} (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i)
private lemma closedExt_inf (U V : Opens Z) :
    hi.isInducing.functor.obj (U ⊓ V) = hi.isInducing.functor.obj U ⊓ hi.isInducing.functor.obj V :=
  hi.isInducing.opensGI.gc.u_inf

private lemma closedExt_mem (U : Opens Z) {x : X} (hx : x ∉ Set.range i) :
    x ∈ hi.isInducing.functor.obj U := by
  have h : complementOpen i hi ≤ hi.isInducing.functorObj U :=
    hi.isInducing.le_functorObj_iff.mpr fun z hz => (hz ⟨z, rfl⟩).elim
  exact h hx

private lemma closedExt_iSup {ι : Type u} [Nonempty ι] (U : ι → Opens Z) :
    hi.isInducing.functor.obj (iSup U) = ⨆ a, hi.isInducing.functor.obj (U a) := by
  apply le_antisymm
  · intro x hx
    apply Opens.mem_iSup.mpr
    by_cases h : x ∈ Set.range i
    · obtain ⟨z, rfl⟩ := h
      obtain ⟨a, ha⟩ := Opens.mem_iSup.mp ((hi.isInducing.mem_functorObj_iff (iSup U)).mp hx)
      exact ⟨a, (hi.isInducing.mem_functorObj_iff (U a)).mpr ha⟩
    · exact ⟨Classical.arbitrary ι, closedExt_mem i hi _ h⟩
  · intro x hx
    obtain ⟨a, ha⟩ := Opens.mem_iSup.mp hx
    exact (hi.isInducing.functor.map (homOfLE (le_iSup U a))).le ha

private lemma realize_isSheaf (K : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w})
    (hK : IsZero (K.obj.obj (op (hi.isInducing.functor.obj ⊥)))) :
    Presheaf.IsSheaf (Opens.grothendieckTopology Z) (hi.isInducing.functor.op ⋙ K.obj) := by
  let R := hi.isInducing.functor
  let F : X.Presheaf (Type w) := K.obj ⋙ forget AddCommGrpCat.{w}
  have hF : F.IsSheaf := Presheaf.isSheaf_comp_of_isSheaf _ _ _ K.property
  apply Presheaf.isSheaf_of_isSheaf_comp _ (s := forget AddCommGrpCat.{w})
  apply TopCat.Presheaf.isSheaf_of_isSheafUniqueGluing_types
  intro ι U s hs
  by_cases hι : Nonempty ι
  · let W (a : ι) := R.obj (U a)
    have he : R.obj (iSup U) = iSup W := closedExt_iSup i hi U
    have hc : TopCat.Presheaf.IsCompatible F W s := by
      intro a b
      have e := closedExt_inf i hi (U a) (U b)
      have h' := congrArg (K.obj.map (eqToHom e.symm).op) (hs a b)
      change K.obj.map (eqToHom e.symm).op
          (K.obj.map (R.map (Opens.infLELeft (U a) (U b))).op (s a)) =
        K.obj.map (eqToHom e.symm).op
          (K.obj.map (R.map (Opens.infLERight (U a) (U b))).op (s b)) at h'
      exact (K.obj.map_comp_apply (R.map (Opens.infLELeft (U a) (U b))).op
        (eqToHom e.symm).op (s a)).trans (h'.trans
          (K.obj.map_comp_apply (R.map (Opens.infLERight (U a) (U b))).op
            (eqToHom e.symm).op (s b)).symm)
    obtain ⟨t, ht, huniq⟩ := hF.isSheafUniqueGluing_types s hc
    refine ⟨K.obj.map (eqToHom he).op t, ?_, ?_⟩
    · intro a
      change K.obj.map (R.map (Opens.leSupr U a)).op (K.obj.map (eqToHom he).op t) = s a
      rw [← ConcreteCategory.comp_apply, ← K.obj.map_comp]
      exact ht a
    · intro t' ht'
      have ht'' : TopCat.Presheaf.IsGluing F W s (K.obj.map (eqToHom he.symm).op t') := by
        intro a
        change K.obj.map (Opens.leSupr W a).op (K.obj.map (eqToHom he.symm).op t') = s a
        rw [← ConcreteCategory.comp_apply, ← K.obj.map_comp]
        exact ht' a
      have hh := congrArg (K.obj.map (eqToHom he).op) (huniq _ ht'')
      simpa only [← ConcreteCategory.comp_apply, ← K.obj.map_comp, ← op_comp, eqToHom_trans,
        eqToHom_refl, op_id, K.obj.map_id, ConcreteCategory.id_apply] using hh
  · have : IsEmpty ι := not_nonempty_iff.mp hι
    have : Subsingleton (K.obj.obj (op (R.obj (iSup U)))) :=
      AddCommGrpCat.subsingleton_of_isZero (by simpa only [iSup_of_empty U] using hK)
    exact ⟨0, isEmptyElim, fun _ _ => @Subsingleton.elim _ this _ _⟩

private lemma closedExt_map (U : Opens X) :
    hi.isInducing.functor.obj ((Opens.map i).obj U) = U ⊔ hi.isInducing.functor.obj ⊥ := by
  apply le_antisymm
  · intro x hx
    by_cases h : x ∈ Set.range i
    · obtain ⟨z, rfl⟩ := h
      exact Or.inl ((hi.isInducing.mem_functorObj_iff _).mp hx)
    · exact Or.inr (closedExt_mem i hi _ h)
  · exact sup_le (hi.isInducing.adjunction.unit.app U).le
      (hi.isInducing.functor.map (homOfLE bot_le)).le

private def realization
    (K : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w})
    (hK : ∀ U : Opens X, (Opens.map i).obj U = ⊥ → IsZero (K.obj.obj (op U))) :
    Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{w} :=
  ⟨hi.isInducing.functor.op ⋙ K.obj,
    realize_isSheaf i hi K (hK _ (hi.isInducing.map_functorObj ⊥))⟩

private lemma supported_map_isIso
    (K : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w})
    (hK : ∀ U : Opens X, (Opens.map i).obj U = ⊥ → IsZero (K.obj.obj (op U)))
    (V : Opens X) : IsIso (K.obj.map (hi.isInducing.adjunction.unit.app V).op) := by
  let W := hi.isInducing.functor.obj ⊥
  have hW : (Opens.map i).obj W = ⊥ := hi.isInducing.map_functorObj ⊥
  have hVW : (Opens.map i).obj (V ⊓ W) = ⊥ :=
    le_antisymm (((Opens.map i).map (homOfLE inf_le_right)).le.trans hW.le) bot_le
  have hpb := IsPullback.of_isLimit (TopCat.Sheaf.isLimitPullbackCone K V W)
  have : IsIso (K.obj.map (homOfLE (le_sup_left : V ≤ V ⊔ W)).op) :=
    hpb.isIso_fst_of_isIso (by exact (hK _ hW).isIso (hK _ hVW) _)
  have heq : K.obj.map (hi.isInducing.adjunction.unit.app V).op =
      K.obj.map (eqToHom (congrArg op (closedExt_map i hi V))) ≫
        K.obj.map (homOfLE (le_sup_left : V ≤ V ⊔ W)).op := by
    rw [← K.obj.map_comp]
    congr 1
  rw [heq]
  infer_instance

private def realizationPushforwardIso
    (K : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w})
    (hK : ∀ U : Opens X, (Opens.map i).obj U = ⊥ → IsZero (K.obj.obj (op U))) :
    ((Opens.map i).sheafPushforwardContinuous AddCommGrpCat.{w}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)).obj
        (realization i hi K hK) ≅ K := by
  let f : ((Opens.map i).sheafPushforwardContinuous AddCommGrpCat.{w}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)).obj
        (realization i hi K hK) ⟶ K :=
    ⟨{ app := fun U => K.obj.map (hi.isInducing.adjunction.unit.app U.unop).op
       naturality := by
         intro A B g
         change K.obj.map _ ≫ K.obj.map _ = K.obj.map _ ≫ K.obj.map _
         rw [← K.obj.map_comp, ← K.obj.map_comp]
         congr 1 }⟩
  have (U : (Opens X)ᵒᵖ) : IsIso (f.hom.app U) := supported_map_isIso i hi K hK U.unop
  have : IsIso f.hom := NatIso.isIso_of_isIso_app _
  have : IsIso ((sheafToPresheaf _ _).map f) := ‹IsIso f.hom›
  have : IsIso f := isIso_of_reflects_iso f (sheafToPresheaf _ _)
  exact asIso f

end Realization

section ExtOfAnAdjunction
universe v
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
private def complexAdj (adj : F ⊣ G) :
    F.mapHomologicalComplex (.up ℤ) ⊣ G.mapHomologicalComplex (.up ℤ) :=
  Adjunction.mkOfUnitCounit {
    unit := (Functor.mapHomologicalComplexIdIso C (.up ℤ)).inv ≫
      NatTrans.mapHomologicalComplex adj.unit (.up ℤ) ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv
    counit := (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ F)) (.up ℤ)).hom ≫
      NatTrans.mapHomologicalComplex adj.counit (.up ℤ) ≫
        (Functor.mapHomologicalComplexIdIso D (.up ℤ)).hom
    left_triangle := by
      ext K n
      simp
    right_triangle := by
      ext K n
      simp }

private def derivedAdj
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D] (adj : F ⊣ G) :
    F.mapDerivedCategory ⊣ G.mapDerivedCategory := by
  let : CatCommSq (F.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q DerivedCategory.Q
      F.mapDerivedCategory := ⟨F.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (G.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q DerivedCategory.Q
      G.mapDerivedCategory := ⟨G.mapDerivedCategoryFactors.symm⟩
  exact (complexAdj adj).localization DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso D (.up ℤ)) F.mapDerivedCategory
    G.mapDerivedCategory

/-- The equivalence on morphisms induced by a fully faithful functor acts as the functor.
This is definitional, but only at default transparency, so it is recorded as a rewrite rule
for the `simp only` calls below. -/
private lemma fullyFaithful_homEquiv_apply {A E : Type*} [Category A] [Category E]
    {S : A ⥤ E} (hS : S.FullyFaithful) {a b : A} (f : a ⟶ b) :
    hS.homEquiv f = S.map f := rfl

private lemma isIso_of_precomp_fullyFaithful
    {A E : Type*} [Category A] [Category E] (S : A ⥤ E) [S.Full] [S.Faithful]
    {a b : A} {k : E} (d : k ⟶ S.obj a) (e : k ≅ S.obj b)
    (h : ∀ y : A, Function.Bijective (fun f : a ⟶ y => d ≫ S.map f)) : IsIso d := by
  obtain ⟨g, hg⟩ := (h b).surjective e.hom
  change d ≫ S.map g = e.hom at hg
  let r := S.map g ≫ e.inv
  have hdr : d ≫ r = 𝟙 k := by simp [r, reassoc_of% hg]
  have hrd : r ≫ d = 𝟙 (S.obj a) := by
    have hh := (h a).injective (a₁ := S.preimage (r ≫ d)) (a₂ := 𝟙 a) (by
      rw [S.map_preimage, S.map_id, ← Category.assoc, hdr]
      simp)
    simpa only [S.map_preimage, S.map_id] using congrArg S.map hh
  exact ⟨⟨r, hdr, hrd⟩⟩

attribute [local instance] HasDerivedCategory.standard in
private lemma comparison_derived_adjunct_isIso
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : F ⊣ G) (A : D) (B : C) (c : B ⟶ G.obj A)
    (hzero : ∀ Y : D, Function.Bijective (fun f : A ⟶ Y => c ≫ G.map f)) :
    IsIso (((derivedAdj adj).homEquiv _ _).symm
      ((DerivedCategory.singleFunctor C 0).map c ≫
        (G.mapDerivedCategorySingleFunctor 0).inv.app A)) := by
  let SC := DerivedCategory.singleFunctor C 0
  let SD := DerivedCategory.singleFunctor D 0
  let da := derivedAdj adj
  let d := (da.homEquiv _ _).symm (SC.map c ≫ (G.mapDerivedCategorySingleFunctor 0).inv.app A)
  apply isIso_of_precomp_fullyFaithful SD d ((F.mapDerivedCategorySingleFunctor 0).app B)
  intro Y
  let e : (B ⟶ G.obj Y) ≃ (F.mapDerivedCategory.obj (SC.obj B) ⟶ SD.obj Y) :=
    (Functor.FullyFaithful.ofFullyFaithful SC).homEquiv.trans
      (((Iso.refl (SC.obj B)).homCongr ((G.mapDerivedCategorySingleFunctor 0).app Y).symm).trans
        (da.homEquiv _ _).symm)
  have he (f : A ⟶ Y) : d ≫ SD.map f = e (c ≫ G.map f) := by
    apply (da.homEquiv _ _).injective
    rw [da.homEquiv_naturality_right, Equiv.apply_symm_apply]
    dsimp [e]
    rw [Equiv.apply_symm_apply]
    simp only [Iso.homCongr, Iso.refl_inv, Category.id_comp, fullyFaithful_homEquiv_apply,
      SC.map_comp, Equiv.coe_fn_mk, Category.assoc]
    change SC.map c ≫ (G.mapDerivedCategorySingleFunctor 0).inv.app A ≫
      G.mapDerivedCategory.map (SD.map f) =
      SC.map c ≫ SC.map (G.map f) ≫ (G.mapDerivedCategorySingleFunctor 0).inv.app Y
    exact congrArg (SC.map c ≫ ·) ((G.mapDerivedCategorySingleFunctor 0).inv.naturality f).symm
  rw [show (fun f : A ⟶ Y => d ≫ SD.map f) = e ∘ (fun f => c ≫ G.map f) from funext he]
  exact e.bijective.comp (hzero Y)

attribute [local instance] HasDerivedCategory.standard in
private lemma extComparison_bijective
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [HasExt.{w} C] [HasExt.{w'} D]
    (adj : F ⊣ G) (A : D) (B : C) (c : B ⟶ G.obj A)
    (hzero : ∀ Y : D, Function.Bijective (fun f : A ⟶ Y => c ≫ G.map f))
    (Y : D) (p : ℕ) : Function.Bijective
      (fun x : Abelian.Ext.{w'} A Y p =>
        ((Abelian.Ext.mk₀ c).comp (x.mapExactFunctor G) (zero_add p) :
          Abelian.Ext.{w} B (G.obj Y) p)) := by
  let SC := DerivedCategory.singleFunctor C 0
  let SD := DerivedCategory.singleFunctor D 0
  let da := derivedAdj adj
  let d := (da.homEquiv _ _).symm (SC.map c ≫ (G.mapDerivedCategorySingleFunctor 0).inv.app A)
  have : IsIso d := comparison_derived_adjunct_isIso adj A B c hzero
  let t := (G.mapDerivedCategory.commShiftIso (p : ℤ)).app (SD.obj Y) ≪≫
    (shiftFunctor _ (p : ℤ)).mapIso ((G.mapDerivedCategorySingleFunctor 0).app Y)
  let e : Abelian.Ext.{w'} A Y p ≃ Abelian.Ext.{w} B (G.obj Y) p :=
    Abelian.Ext.homEquiv.trans (((asIso d).symm.homCongr (Iso.refl _)).trans
      ((da.homEquiv _ _).trans (((Iso.refl _).homCongr t).trans Abelian.Ext.homEquiv.symm)))
  have he (x : Abelian.Ext.{w'} A Y p) :
      e x = (Abelian.Ext.mk₀ c).comp (x.mapExactFunctor G) (zero_add p) := by
    apply Abelian.Ext.homEquiv.injective
    dsimp [e, Iso.homCongr]
    rw [Equiv.apply_symm_apply]
    simp only [Category.comp_id]
    rw [da.homEquiv_naturality_right]
    simp only [d, Equiv.apply_symm_apply]
    change 𝟙 _ ≫ ((SC.map c ≫ (G.mapDerivedCategorySingleFunctor 0).inv.app A) ≫
      G.mapDerivedCategory.map x.hom) ≫ t.hom = _
    change _ = ((Abelian.Ext.mk₀ c).comp (x.mapExactFunctor G) (zero_add p)).hom
    rw [Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom, ShiftedHom.mk₀_comp,
      Abelian.Ext.mapExactFunctor_hom]
    simp [t, SC, SD, ShiftedHom.map, Category.assoc]
  exact (show (fun x => (Abelian.Ext.mk₀ c).comp (x.mapExactFunctor G) (zero_add p)) = e from
    funext (fun x => (he x).symm)) ▸ e.bijective

end ExtOfAnAdjunction

section Reflector
variable {X Z : TopCat.{u}}
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{w}]
  [HasSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{w}]
  (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i)
private def closedReflector : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w} ⥤
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w} :=
  sheafToPresheaf _ _ ⋙ killFunctor (complementOpen i hi) ⋙ presheafToSheaf _ _

private def closedReflectorUnit : 𝟭 (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w}) ⟶
    closedReflector i hi where
  app F := ⟨killπ (complementOpen i hi) F.obj ≫
    toSheafify _ (killPresheaf (complementOpen i hi) F.obj)⟩
  naturality {F G} f := by
    apply Sheaf.hom_ext
    change f.hom ≫ (killπ.{u,w} (complementOpen i hi) G.obj ≫
      toSheafify (Opens.grothendieckTopology X) (killPresheaf (complementOpen i hi) G.obj)) =
      (killπ.{u,w} (complementOpen i hi) F.obj ≫
        toSheafify (Opens.grothendieckTopology X) (killPresheaf (complementOpen i hi) F.obj)) ≫
          sheafifyMap (Opens.grothendieckTopology X) (killMapNat (complementOpen i hi) f.hom)
    rw [Category.assoc, ← toSheafify_naturality]
    simpa only [Category.assoc] using
      congrArg (· ≫ toSheafify (Opens.grothendieckTopology X)
        (killPresheaf (complementOpen i hi) G.obj))
        (killπ_naturality (complementOpen i hi) f.hom).symm

omit [HasSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{w}] in
private lemma closedReflectorUnit_epi
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w}) :
    Epi ((closedReflectorUnit i hi).app F) := by
  constructor
  intro H f g h
  apply ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{w}).homEquiv
    _ H).injective
  apply (cancel_epi (killπ (complementOpen i hi) F.obj)).mp
  -- Both sides are `(killπ ≫ toSheafify) ≫ _`; composition of presheaves of abelian groups is
  -- associative definitionally, so the hypothesis applies on the nose.
  exact congrArg (fun k : F ⟶ H => k.hom) h

omit [HasSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{w}] in
private lemma closedReflector_supported
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w}) (V : Opens X)
    (hV : (Opens.map i).obj V = ⊥) :
    IsZero (((closedReflector i hi).obj F).obj.obj (op V)) := by
  apply sheafification_isZero
  intro W g
  apply killObj_zero
  rintro x hx ⟨z, rfl⟩
  have hz : z ∈ (Opens.map i).obj V := g.le hx
  rw [hV] at hz
  exact hz

omit [HasSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{w}] in
private lemma closedReflector_preservesFiniteLimits :
    PreservesFiniteLimits (closedReflector i hi) := by
  have : PreservesLimitsOfSize.{0,0} (killFunctor.{u,w} (complementOpen i hi)) :=
    killPreservesLimits _
  have : PreservesFiniteLimits (killFunctor.{u,w} (complementOpen i hi)) :=
    PreservesLimitsOfSize.preservesFiniteLimits _
  have : PreservesFiniteLimits (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w}) :=
    HasSheafify.isLeftExact
  exact comp_preservesFiniteLimits
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w}) _

private def closedPushforwardFullyFaithful : (closedPushforward.{u,w} i).FullyFaithful := by
  have hcounitApp (V : Opens Z) : IsIso (hi.isInducing.adjunction.counit.app V) :=
    ⟨⟨eqToHom (hi.isInducing.map_functorObj V).symm, Subsingleton.elim _ _,
      Subsingleton.elim _ _⟩⟩
  have : IsIso hi.isInducing.adjunction.counit := NatIso.isIso_of_isIso_app _
  have ff := Adjunction.fullyFaithfulROfIsIsoCounit hi.isInducing.adjunction
  have := ff.full
  have := ff.faithful
  let a := Adjunction.whiskerLeft AddCommGrpCat.{w} hi.isInducing.adjunction.op
  have hunit : IsIso a.unit := by
    have (P : (Opens Z)ᵒᵖ ⥤ AddCommGrpCat.{w}) : IsIso (a.unit.app P) := by
      have (V : (Opens Z)ᵒᵖ) : IsIso ((a.unit.app P).app V) := by
        change IsIso (P.map (hi.isInducing.adjunction.op.unit.app V))
        infer_instance
      exact NatIso.isIso_of_isIso_app _
    exact NatIso.isIso_of_isIso_app _
  have ffp : (TopCat.Presheaf.pushforward AddCommGrpCat.{w} i).FullyFaithful :=
    Adjunction.fullyFaithfulLOfIsIsoUnit a
  have hcomp : (closedPushforward.{u,w} i ⋙ sheafToPresheaf _ _).FullyFaithful :=
    (fullyFaithfulSheafToPresheaf _ _).comp ffp
  exact Functor.FullyFaithful.ofCompFaithful hcomp

private def reflectedObject (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w}) :
    Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{w} :=
  realization i hi ((closedReflector i hi).obj F) (closedReflector_supported i hi F)

private def reflectedObjectIso (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w}) :
    (closedPushforward i).obj (reflectedObject i hi F) ≅ (closedReflector i hi).obj F :=
  realizationPushforwardIso i hi ((closedReflector i hi).obj F) (closedReflector_supported i hi F)

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{w}]
  [HasSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{w}] in
private def killHomEquiv
    (F : X.Presheaf AddCommGrpCat.{w})
    (G : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{w}) :
    (killPresheaf (complementOpen i hi) F ⟶ ((closedPushforward i).obj G).obj) ≃
      (F ⟶ ((closedPushforward i).obj G).obj) where
  toFun f := killπ _ F ≫ f
  invFun f := killLift _ (closedPushforward_supported i hi G) f
  left_inv _ := (cancel_epi (killπ _ F)).mp (killLift_fac _ _ _)
  right_inv _ := killLift_fac _ _ _

private def reflectedHomEquiv
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w})
    (G : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{w}) :
    (reflectedObject i hi F ⟶ G) ≃ (F ⟶ (closedPushforward i).obj G) :=
  (closedPushforwardFullyFaithful i hi).homEquiv.trans
    (((reflectedObjectIso i hi F).homCongr (Iso.refl _)).trans
      (((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{w}).homEquiv
        _ _).trans ((killHomEquiv i hi F.obj G).trans
          { toFun := fun f => ⟨f⟩, invFun := fun f => f.hom, left_inv := fun _ => rfl,
            right_inv := fun _ => rfl })))

omit [HasSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{w}] in
private lemma reflectedHomEquiv_apply
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w})
    (G : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{w})
    (f : reflectedObject i hi F ⟶ G) :
    reflectedHomEquiv i hi F G f = (closedReflectorUnit i hi).app F ≫
      (reflectedObjectIso i hi F).inv ≫ (closedPushforward i).map f := by
  apply Sheaf.hom_ext
  rfl

omit [HasSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{w}] in
private lemma reflectedHomEquiv_naturality
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w})
    (G H : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{w})
    (g : G ⟶ H) (f : reflectedObject i hi F ⟶ G) :
    reflectedHomEquiv i hi F H (f ≫ g) =
      reflectedHomEquiv i hi F G f ≫ (closedPushforward i).map g := by
  simp only [reflectedHomEquiv_apply, Functor.map_comp, Category.assoc]

private def closedPullback := Adjunction.leftAdjointOfEquiv
  (reflectedHomEquiv i hi) (reflectedHomEquiv_naturality i hi)

-- `(closedPullback i hi).obj F` is `reflectedObject i hi F` by construction; unification needs
-- to see that when the two are compared as objects of `closedPullback ⋙ closedPushforward`
-- versus `closedPushforward` applied to the reflection.
attribute [local implicit_reducible] closedPullback
private def closedAdjunction : closedPullback i hi ⊣ closedPushforward.{u,w} i :=
  Adjunction.adjunctionOfEquivLeft (reflectedHomEquiv i hi) (reflectedHomEquiv_naturality i hi)

omit [HasSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{w}] in
private lemma closedAdjunction_unit
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w}) :
    (closedAdjunction i hi).unit.app F = (closedReflectorUnit i hi).app F ≫
      (reflectedObjectIso i hi F).inv := by
  change reflectedHomEquiv i hi F _ (𝟙 _) = _
  rw [reflectedHomEquiv_apply, CategoryTheory.Functor.map_id, Category.comp_id]

private def closedPullbackPushforwardIso :
    closedPullback i hi ⋙ closedPushforward i ≅ closedReflector i hi :=
  NatIso.ofComponents (reflectedObjectIso i hi) (by
    intro F H f
    have := closedReflectorUnit_epi i hi F
    have : Epi ((closedAdjunction i hi).unit.app F) := by
      rw [closedAdjunction_unit]
      infer_instance
    apply (cancel_epi ((closedAdjunction i hi).unit.app F)).mp
    rw [closedAdjunction_unit]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    have hn := (closedAdjunction i hi).unit.naturality f
    rw [closedAdjunction_unit, closedAdjunction_unit] at hn
    have hh := congrArg (fun k => k ≫ (reflectedObjectIso i hi H).hom) hn
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hh
    rw [← hh]
    exact (closedReflectorUnit i hi).naturality f)

omit [HasSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{w}] in
private lemma closedPullback_preservesFiniteLimits :
    PreservesFiniteLimits (closedPullback.{u,w} i hi) := by
  have := (closedPushforwardFullyFaithful.{u,w} i hi).full
  have := (closedPushforwardFullyFaithful.{u,w} i hi).faithful
  have := closedReflector_preservesFiniteLimits.{u,w} i hi
  have : PreservesFiniteLimits (closedPullback i hi ⋙ closedPushforward i) :=
    preservesFiniteLimits_of_natIso (closedPullbackPushforwardIso i hi).symm
  have : ReflectsFiniteLimits (closedPushforward i) :=
    ReflectsLimitsOfSize.reflectsFiniteLimits.{0, 0} _
  exact preservesFiniteLimits_of_reflects_of_preserves (closedPullback i hi) (closedPushforward i)
end Reflector

omit hExtZ hExtX hSheafZ in
private lemma preservesFiniteLimits_abelianSheafPushforward (i : Z ⟶ X) :
    PreservesFiniteLimits (abelianSheafPushforward.{u, w} i) := by
  let T := abelianSheafPushforward.{u, w} i
  let U := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w}
  have : PreservesFiniteLimits (T ⋙ U) := preservesFiniteLimits_of_natIso
    ((Opens.map i).sheafPushforwardContinuousCompSheafToPresheafIso AddCommGrpCat.{w}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)).symm
  exact preservesFiniteLimits_of_reflects_of_preserves T U

/-- Mate of a unit. Let `adjZ : LZ ⊣ P ⋙ RX` and `adjX : LX ⊣ RX` be adjunctions and let `c`
be a morphism `LX.obj a ⟶ P.obj (LZ.obj a)` whose `adjX`-adjunct is the unit of `adjZ` at `a`.
Then composing with `c` is a bijection `(LZ.obj a ⟶ F) → (LX.obj a ⟶ P.obj F)` for every `F`,
being the composite of the two hom-equivalences. -/
private lemma bijective_comp_map_of_adjunctions
    {E : Type*} [Category E] {A' : Type*} [Category A'] {B' : Type*} [Category B']
    {LZ : E ⥤ A'} {P : A' ⥤ B'} {RX : B' ⥤ E} {LX : E ⥤ B'}
    (adjZ : LZ ⊣ P ⋙ RX) (adjX : LX ⊣ RX) (a : E) (F : A')
    (c : LX.obj a ⟶ P.obj (LZ.obj a))
    (hc : adjX.homEquiv a (P.obj (LZ.obj a)) c = adjZ.unit.app a) :
    Function.Bijective (fun f : LZ.obj a ⟶ F => c ≫ P.map f) := by
  have he : (fun f : LZ.obj a ⟶ F => c ≫ P.map f) =
      ⇑((adjZ.homEquiv a F).trans (adjX.homEquiv a (P.obj F)).symm) := by
    funext f
    apply (adjX.homEquiv a (P.obj F)).injective
    rw [adjX.homEquiv_naturality_right, hc, Equiv.trans_apply, Equiv.apply_symm_apply,
      adjZ.homEquiv_unit, Functor.comp_map]
  rw [he]
  exact Equiv.bijective _

omit hExtZ hExtX in
private lemma constantSheafPushforwardHom_comp_bijective (i : Z ⟶ X) (A : AddCommGrpCat.{w})
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{w}) :
    Function.Bijective (fun f : (constantSheaf (Opens.grothendieckTopology Z)
      AddCommGrpCat.{w}).obj A ⟶ F =>
      constantSheafPushforwardHom.{u,w} i A ≫ (abelianSheafPushforward.{u,w} i).map f) := by
  -- The global-sections functor of `Z` *is* the one of `X` precomposed with the pushforward,
  -- because `(Opens.map i).obj ⊤ = ⊤`. Naming that once, in the type of `adjZ`, is the only
  -- place where the identification is used; everything else is formal adjunction yoga.
  exact bijective_comp_map_of_adjunctions
    (show constantSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{w} ⊣
        abelianSheafPushforward.{u, w} i ⋙
          (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{w}).obj (op ⊤) from
      constantSheafAdj (Opens.grothendieckTopology Z) AddCommGrpCat.{w}
        (isTerminalTop : IsTerminal (⊤ : Opens Z)))
    (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{w}
      (isTerminalTop : IsTerminal (⊤ : Opens X))) A F _ (Equiv.apply_symm_apply _ _)

/-- Closed embeddings have exact pushforward, and the derived global-sections
comparison is an isomorphism in every degree. -/
@[stacks 02UV "the canonical comparison is invertible"]
public theorem hasCohomologyPushforwardIso_of_isClosedEmbedding
    (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i) :
    HasCohomologyPushforwardIso (hExtZ := hExtZ) (hExtX := hExtX) i := by
  have := preservesFiniteLimits_abelianSheafPushforward i
  have := closedPushforward_preservesFiniteColimits i hi
  have := closedPullback_preservesFiniteLimits.{u,w} i hi
  have := (closedAdjunction.{u,w} i hi).isLeftAdjoint
  have : PreservesFiniteColimits (closedPullback.{u,w} i hi) := inferInstance
  have : (closedPullback.{u,w} i hi).Additive :=
    CategoryTheory.Functor.additive_of_preserves_binary_products _
  refine ⟨inferInstance, inferInstance, fun p => ?_⟩
  have (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{w}) :
      IsIso ((cohomologyPushforwardComparison (hExtZ := hExtZ) (hExtX := hExtX) i p).app F) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr <| extComparison_bijective (closedAdjunction i hi)
      _ _ (constantSheafPushforwardHom i (AddCommGrpCat.of (ULift.{w} ℤ)))
      (constantSheafPushforwardHom_comp_bijective i _) F p
  exact NatIso.isIso_of_isIso_app _

/-- For a closed embedding `i : Z ⟶ X`, cohomology of an abelian sheaf on `Z` is
canonically isomorphic, naturally in the sheaf, to the cohomology of its pushforward to `X`.
This is [Stacks Project, Tag 02UV](https://stacks.math.columbia.edu/tag/02UV). -/
@[stacks 02UV]
public noncomputable def cohomologyPushforwardIso
    [hExtZ : HasExt.{w'} (Z.Sheaf AddCommGrpCat.{w})]
    [hExtX : HasExt.{w'} (X.Sheaf AddCommGrpCat.{w})]
    (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i) (p : ℕ) :
    (@CategoryTheory.Sheaf.functorH _ _ (Opens.grothendieckTopology Z)
      hSheafZ hExtZ p :
      Z.Sheaf AddCommGrpCat.{w} ⥤ AddCommGrpCat.{w'}) ≅
      TopCat.Sheaf.pushforward AddCommGrpCat.{w} i ⋙
        (@CategoryTheory.Sheaf.functorH _ _ (Opens.grothendieckTopology X)
          hSheafX hExtX p :
          X.Sheaf AddCommGrpCat.{w} ⥤
            AddCommGrpCat.{w'}) := by
  let h := hasCohomologyPushforwardIso_of_isClosedEmbedding
    (hExtZ := hExtZ) (hExtX := hExtX) i hi
  let := h.preservesFiniteLimits
  let := h.preservesFiniteColimits
  exact @asIso _ _ _ _
    (cohomologyPushforwardComparison (hExtZ := hExtZ) (hExtX := hExtX) i p) (h.isIso p)

/-- Each component is the canonical derived comparison: apply exact pushforward
to the `Ext` class and precompose with the canonical map of constant integer sheaves. -/
public theorem cohomologyPushforwardIso_hom_apply
    (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i) (p : ℕ)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{w})
    (x : CategoryTheory.Sheaf.H.{w'} F p) :
    let h := hasCohomologyPushforwardIso_of_isClosedEmbedding
      (hExtZ := hExtZ) (hExtX := hExtX) i hi
    letI := h.preservesFiniteLimits
    letI := h.preservesFiniteColimits
    (cohomologyPushforwardIso (hExtZ := hExtZ) (hExtX := hExtX) i hi p).hom.app F x =
      (Abelian.Ext.mk₀ (constantSheafPushforwardHom i
        (AddCommGrpCat.of (ULift.{w} ℤ)))).comp
          (x.mapExactFunctor (abelianSheafPushforward.{u, w} i)) (zero_add p) :=
  rfl

/-- In degree one the comparison sends the class of an extension, pulled back
along a map from the constant integer sheaf, to the pushed-forward extension
pulled back along the induced map. -/
public theorem cohomologyPushforwardIso_hom_extClass
    (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i)
    (S : ShortComplex
      (CategoryTheory.Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{w}))
    (hS : S.ShortExact)
    (s : (constantSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{w}).obj
      (AddCommGrpCat.of (ULift.{w} ℤ)) ⟶ S.X₃) :
    let h := hasCohomologyPushforwardIso_of_isClosedEmbedding
      (hExtZ := hExtZ) (hExtX := hExtX) i hi
    letI := h.preservesFiniteLimits
    letI := h.preservesFiniteColimits
    (cohomologyPushforwardIso (hExtZ := hExtZ) (hExtX := hExtX) i hi 1).hom.app S.X₁
        ((Abelian.Ext.mk₀ s).comp hS.extClass (zero_add 1)) =
      (Abelian.Ext.mk₀ (constantSheafPushforwardHom i (AddCommGrpCat.of (ULift.{w} ℤ)) ≫
        (abelianSheafPushforward.{u, w} i).map s)).comp
          (hS.map_of_exact (abelianSheafPushforward.{u, w} i)).extClass
          (zero_add 1) := by
  dsimp only
  rw [cohomologyPushforwardIso_hom_apply, Abelian.Ext.mapExactFunctor_comp,
    Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mapExactFunctor_extClass,
    Abelian.Ext.mk₀_comp_mk₀_assoc]

end Stacks.ClosedImmersion

end
