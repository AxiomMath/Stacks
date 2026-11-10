module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekSubsheaf
public import StacksFrontier.AlgebraicGeometry.Etale.ProperSupportFiberDecomposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Pushforward
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BigSiteCoverings
public import StacksCore.Tactic.StacksAttribute

/-!
# Extension by zero is the proper-support direct image

Let `j : U ⟶ X` be a separated étale morphism of a big étale site and let `F` be an abelian
sheaf on the small étale site of `U`. Both the extension by zero `j_! F` and the proper-support
subsheaf `j_! F ⊆ j_* F` of Tag 0F4X are abelian subsheaves of the direct image `j_* F`, the
first through the canonical monomorphism of Tag 0F4L. This file identifies them: on every étale
test object the two have the same sections inside `j_* F`.

One inclusion is formal: a section of the extension by zero is locally a finite sum of sections
carried by graphs of morphisms to `U`, each graph is a closed immersion because `j` is
separated, and a closed immersion onto a fibre of the first projection is proper over the base.

The other inclusion is local. A section `s` of `j_* F` with proper support has, over each point
`x` of the test object, a support meeting the fibre over `x` in a finite set; the étale-local
structure of the separated étale morphism `U ×_X V ⟶ V` then produces an étale neighbourhood of
`x` over which `U ×_X V` splits into finitely many disjoint copies of that neighbourhood
carrying the whole support, plus a remainder missing it. Extending `s` by zero from each copy
gives a section of `j_! F` whose image agrees with `s` on the fibre over `x`; properness of the
support of the difference then shrinks the neighbourhood so that the two agree outright. Those
local preimages cover the test object, so `s` lies in the image by the sheaf axiom.

## Main results

* `AlgebraicGeometry.SmallEtale.abelianExtensionByZeroToPushforward_range_eq_fShriekSubsheaf` —
  **Stacks 0F4Y**, the sectionwise equality of the two subsheaves of the direct image.
* `AlgebraicGeometry.SmallEtale.mem_zeroOpen_add`,
  `AlgebraicGeometry.SmallEtale.mem_zeroOpen_sub` and
  `AlgebraicGeometry.SmallEtale.mem_zeroOpen_sum` — a point at which each of finitely many
  sections vanishes is a point at which their sum, or difference, vanishes.

## Implementation notes

The statement is sectionwise equality of two subsets of `(j_* F)(V)` rather than an equality of
subobjects: the canonical map of Tag 0F4L is a monomorphism and the proper-support subsheaf is
bundled with the characterisation of its image, so equality of the images at every `V` is
exactly equality of the two as subsheaves, and it is the form a consumer can use pointwise.

Only the étale and separated hypotheses on `j` are used, and both are already recorded: the
étaleness comes from `U` being an object of the small étale site of `X`, and separatedness is a
hypothesis of Tag 0F4L as well.

Two groups occurring here have each two spellings which are the same group but not the same
expression: the sections of the direct image over a test object and the sections of `F` over its
base change, and the sections of the extension by zero over the image of `W` and those of its
restriction over `W`. The private definitions `graphExtend` and `graphPush`, and the type
ascriptions on the two projections of each fibre product in the proof of the main result, pin
one spelling of each, which is what makes the restrictions of these sections well formed as
written and lets the rewriting go through unaided.

## References

* [Stacks Project, Tag 0F4Y](https://stacks.math.columbia.edu/tag/0F4Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped Function

universe u v w

namespace AlgebraicGeometry.SmallEtale

/-! ### Vanishing of finite sums of sections -/

section ZeroOpen

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v}) (U : SmallEtale B S hS)

/-- A point at which two sections both vanish is a point at which their sum vanishes. -/
public theorem mem_zeroOpen_add (s t : F.obj.obj (op U))
    {x : (SmallEtale.toScheme B S hS).obj U}
    (hs : x ∈ zeroOpen B S hS F U s) (ht : x ∈ zeroOpen B S hS F U t) :
    x ∈ zeroOpen B S hS F U (s + t) := by
  by_contra hx
  rcases supportSection_add_subset B S hS F U s t hx with h | h
  exacts [h hs, h ht]

/-- A point at which two sections both vanish is a point at which their difference vanishes. -/
public theorem mem_zeroOpen_sub (s t : F.obj.obj (op U))
    {x : (SmallEtale.toScheme B S hS).obj U}
    (hs : x ∈ zeroOpen B S hS F U s) (ht : x ∈ zeroOpen B S hS F U t) :
    x ∈ zeroOpen B S hS F U (s - t) := by
  rw [sub_eq_add_neg]
  exact mem_zeroOpen_add B S hS F U s (-t) hs (by rwa [zeroOpen_neg])

/-- A point at which each of a finite family of sections vanishes is a point at which their sum
vanishes. -/
public theorem mem_zeroOpen_sum {ι : Type w} (I : Finset ι) (s : ι → F.obj.obj (op U))
    {x : (SmallEtale.toScheme B S hS).obj U}
    (hs : ∀ i ∈ I, x ∈ zeroOpen B S hS F U (s i)) :
    x ∈ zeroOpen B S hS F U (∑ i ∈ I, s i) := by
  classical
  induction I using Finset.induction with
  | empty => simp [zeroOpen_zero]
  | insert i I hi ih =>
      rw [Finset.sum_insert hi]
      exact mem_zeroOpen_add B S hS F U _ _ (hs i (Finset.mem_insert_self i I))
        (ih fun j hj => hs j (Finset.mem_insert_of_mem hj))

end ZeroOpen

/-! ### Two lemmas on subsheaves of abelian sheaves -/

/-- A section of an abelian sheaf which is locally in the image of a monomorphism of sheaves is
in the image. -/
private theorem mem_range_of_imageSieve_mem
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget AddCommGrpCat.{v})]
    {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) [Mono f.hom]
    {V : C} (s : G.obj.obj (op V))
    (hs : Presheaf.imageSieve f.hom s ∈ J V) : s ∈ Set.range (f.hom.app (op V)) := by
  let φ := Functor.whiskerRight f.hom (forget AddCommGrpCat)
  have : Mono φ := by
    refine (NatTrans.mono_iff_mono_app φ).mpr fun W => ?_
    change Mono ((forget AddCommGrpCat).map (f.hom.app W))
    rw [mono_iff_injective]
    exact (AddCommGrpCat.mono_iff_injective (f.hom.app W)).mp inferInstance
  have hF : Presieve.IsSheaf J (F.obj ⋙ forget AddCommGrpCat) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp ((sheafCompose J (forget AddCommGrpCat)).obj F).property
  have hG : Presieve.IsSheaf J (G.obj ⋙ forget AddCommGrpCat) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp ((sheafCompose J (forget AddCommGrpCat)).obj G).property
  have hR := Presieve.isSheaf_iso J (asIso (Subfunctor.toRange φ)) hF
  change s ∈ (Subfunctor.range φ).obj (op V)
  rwa [(Subfunctor.range φ).eq_sheafify hG hR]

/-- A morphism of abelian sheaves whose image is sectionwise contained in the image of a
sectionwise injective morphism factors through it. -/
private theorem exists_sheaf_lift_of_range_subset
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {F G H : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ H) (g : G ⟶ H)
    (hg : ∀ V, Function.Injective (g.hom.app V))
    (h : ∀ V, Set.range (f.hom.app V) ⊆ Set.range (g.hom.app V)) :
    ∃ l : F ⟶ G, l ≫ g = f := by
  classical
  choose a ha using fun V s => h V ⟨s, rfl⟩
  let l : F ⟶ G := ⟨{
    app V := AddCommGrpCat.ofHom {
      toFun := a V
      map_zero' := hg V (by simp [ha])
      map_add' := fun x y => hg V (by simp [ha]) }
    naturality V W k := by
      ext x
      apply hg W
      symm
      change (g.hom.app W) (G.obj.map k (a V x)) =
        (g.hom.app W) (a W (F.obj.map k x))
      rw [← ConcreteCategory.comp_apply, g.hom.naturality]
      change H.obj.map k (g.hom.app V (a V x)) = _
      rw [ha, ha]
      exact (ConcreteCategory.congr_hom (f.hom.naturality k) x).symm }⟩
  refine ⟨l, ?_⟩
  ext V x
  exact ha V x

/-- If two arrows of the small étale site have disjoint images, no nonempty object maps into
both compatibly. -/
private theorem ne_of_disjoint_ranges {B : BigEtaleSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {A T P R : SmallEtale B S hS} (g : A ⟶ P) (c : T ⟶ P)
    (hd : Disjoint (Set.range ((SmallEtale.toScheme B S hS).map g))
      (Set.range ((SmallEtale.toScheme B S hS).map c)))
    (hR : Nonempty ((SmallEtale.toScheme B S hS).obj R)) (a : R ⟶ A) (b : R ⟶ T) :
    a ≫ g ≠ b ≫ c := by
  intro hab
  have hp := congrArg (fun k => ((SmallEtale.toScheme B S hS).map k) (Classical.choice hR)) hab
  simp only [Functor.map_comp, Scheme.Hom.comp_apply] at hp
  exact Set.disjoint_left.mp hd ⟨_, rfl⟩ ⟨_, hp.symm⟩

/-- The support of a section lies in a closed set `C` as soon as the section restricts to zero
along every arrow whose image is disjoint from `C`. -/
private theorem supportSection_subset_of_forall_disjoint_eq_zero (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    (P : SmallEtale B S hS) (s : F.obj.obj (op P))
    {C : Set ((SmallEtale.toScheme B S hS).obj P)} (hC : IsClosed C)
    (h : ∀ (T : SmallEtale B S hS) (c : T ⟶ P),
      Disjoint C (Set.range ((SmallEtale.toScheme B S hS).map c)) → F.obj.map c.op s = 0) :
    supportSection B S hS F P s ⊆ C := by
  let O : ((SmallEtale.toScheme B S hS).obj P).Opens := ⟨Cᶜ, hC.isOpen_compl⟩
  have hz := h _ (openObjectι B S hS P O) (by
    rw [show Set.range ((SmallEtale.toScheme B S hS).map (openObjectι B S hS P O)) = Cᶜ from
      openObjectι_range B S hS P O]
    exact disjoint_compl_right)
  have h := (map_eq_zero_iff_range_subset_zeroOpen B S hS F P s _ _).mp hz
  rw [openObjectι_range] at h
  exact fun z hz' => Classical.byContradiction fun hzg => hz' (h hzg)

/-! ### Sections carried by a graph -/

section Graph

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (U : SmallEtale B X hX)

/-- Base change of an arrow of the small étale site commutes with the first projections. -/
private theorem smallEtaleBaseChange_map_fst {Y Z : B.Scheme} (f : Y ⟶ Z)
    {V W : SmallEtale B Z.1 Z.property} (g : V ⟶ W) :
    (SmallEtale.toScheme B Y.1 Y.property).map ((smallEtaleBaseChange B f).map g) ≫
        B.inclusion.map (pullback.fst W.obj.hom f) =
      B.inclusion.map (pullback.fst V.obj.hom f) ≫
        (SmallEtale.toScheme B Z.1 Z.property).map g :=
  (isPullback_baseChange_projection B f g).w

variable (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1})

/-- A section of `F` over an étale object `W` of the small étale site of `U`, viewed as a section
of the extension by zero over the image of `W` in the small étale site of `X`.

This is the unit of the extension-by-zero adjunction, stated at the sections of the extension by
zero over `W` seen over `X` rather than at the sections of its restriction over `W`. The two are
the same group, and naming the first makes every later restriction of such a section
syntactically well formed. -/
private def graphExtend (W : SmallEtale B U.obj.left.1 U.obj.left.property)
    (s : F.obj.obj (op W)) :
    ((abelianExtensionByZero B X hX U).obj F).obj.obj
      (op ((smallEtalePostcompose B X hX U).obj W)) :=
  ((abelianExtensionByZeroAdjunction B X hX U).unit.app F).hom.app (op W) s

/-- The image of `graphExtend` in the direct image, read as a section of `F` over the base change
of the image of `W`.

The group of sections of the direct image over an object is the group of sections of `F` over its
base change; naming the second spelling keeps the restrictions of such a section syntactically
well formed. -/
private def graphPush (W : SmallEtale B U.obj.left.1 U.obj.left.property)
    (s : F.obj.obj (op W)) :
    F.obj.obj (op ((smallEtaleBaseChange B U.obj.hom).obj
      ((smallEtalePostcompose B X hX U).obj W))) :=
  ((abelianExtensionByZeroToPushforward B X hX U).app F).hom.app
    (op ((smallEtalePostcompose B X hX U).obj W)) (graphExtend B X hX U F W s)

/-- The section of the extension by zero carried by the graph of an étale object over `U`,
transported along an isomorphism of its image in the small étale site of `X`. -/
private def graphLift (W : SmallEtale B U.obj.left.1 U.obj.left.property)
    (V : SmallEtale B X hX) (e : (smallEtalePostcompose B X hX U).obj W ≅ V)
    (s : F.obj.obj (op W)) :
    ((abelianExtensionByZero B X hX U).obj F).obj.obj (op V) :=
  ((abelianExtensionByZero B X hX U).obj F).obj.map e.inv.op (graphExtend B X hX U F W s)

/-- The image of `graphLift` under the canonical map is the transport of the extension by zero
of the section. -/
private theorem graphLift_image (W : SmallEtale B U.obj.left.1 U.obj.left.property)
    (V : SmallEtale B X hX) (e : (smallEtalePostcompose B X hX U).obj W ≅ V)
    (s : F.obj.obj (op W)) :
    (((abelianExtensionByZeroToPushforward B X hX U).app F).hom.app (op V))
        (graphLift B X hX U F W V e s) =
      F.obj.map ((smallEtaleBaseChange B U.obj.hom).map e.inv).op (graphPush B X hX U F W s) :=
  ConcreteCategory.congr_hom
    (((abelianExtensionByZeroToPushforward B X hX U).app F).hom.naturality e.inv.op) _

/-- The image of a closed immersion admitting a left inverse `p` is proper over the target of
`p`. -/
public theorem isProperOver_range_of_comp_eq_id {Y Z : Scheme.{u}} (g : Z ⟶ Y) (p : Y ⟶ Z)
    [IsClosedImmersion g] [LocallyOfFiniteType p] (hgp : g ≫ p = 𝟙 Z) :
    IsProperOver p ⟨Set.range g.base, g.isClosedEmbedding.isClosed_range⟩ := by
  refine (isProperOver_iff_exists_isProper p _).2 ⟨g.ker, ?_, ?_⟩
  · apply SetLike.coe_injective
    change (g.ker.support : Set _) = Set.range g.base
    rw [Scheme.Hom.support_ker, IsClosed.closure_eq g.isClosedEmbedding.isClosed_range]
  · have hcomp : g.ker.subschemeι ≫ p = inv g.toImage := by
      rw [← cancel_epi g.toImage, ← Category.assoc, Scheme.Hom.toImage_imageι, hgp,
        IsIso.hom_inv_id]
    rw [hcomp]
    infer_instance

variable [IsSeparated (B.inclusion.map U.obj.hom)]

/-- The extension by zero of a section along the graph of an étale object over `U` has support
contained in that graph, hence proper over the test object. -/
private theorem graphSection_hasProperSupport
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) (σ : F.obj.obj (op W)) :
    properSupportSections B U.obj.hom F ((smallEtalePostcompose B X hX U).obj W)
      (((abelianExtensionByZeroToPushforward B X hX U).app F).hom.app
        (op ((smallEtalePostcompose B X hX U).obj W)) (graphExtend B X hX U F W σ)) := by
  classical
  let Wₓ := (smallEtalePostcompose B X hX U).obj W
  let P := (smallEtaleBaseChange B U.obj.hom).obj Wₓ
  let g := (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map
    (smallEtaleGraph B X hX U W)
  let p : (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).obj P ⟶
      (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).obj W :=
    B.inclusion.map (pullback.fst Wₓ.obj.hom U.obj.hom)
  have : IsClosedImmersion g := isClosedImmersion_map_smallEtaleGraph B X hX U W
  let Zg : Closeds ((SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).obj P) :=
    ⟨Set.range g.base, g.isClosedEmbedding.isClosed_range⟩
  let s := (((abelianExtensionByZeroToPushforward B X hX U).app F).hom.app (op Wₓ))
    (graphExtend B X hX U F W σ)
  have hsupport_le : (zeroOpen B U.obj.left.1 U.obj.left.property F P s).compl ≤ Zg :=
    supportSection_subset_of_forall_disjoint_eq_zero B U.obj.left.1 U.obj.left.property F P s
      g.isClosedEmbedding.isClosed_range fun T c hd =>
        abelianExtensionByZeroToPushforward_graph_compl B X hX U F W T c
          (fun _ hS a b => ne_of_disjoint_ranges _ _ hd hS a b) σ
  have : LocallyOfFiniteType p :=
    MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback (Over.hom Wₓ.obj) U.obj.hom).flip.map B.inclusion)
      inferInstance
  have hgp : g ≫ p = 𝟙 ((SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).obj W) := by
    change B.inclusion.map
      (pullback.lift (𝟙 (Over.left W.obj)) (Over.hom W.obj) _ ≫
        pullback.fst ((Over.hom W.obj) ≫ U.obj.hom) U.obj.hom) = _
    rw [pullback.lift_fst]
    simp
  exact isProperOver_of_le p hsupport_le (isProperOver_range_of_comp_eq_id g p hgp)

/-- The canonical map from extension by zero to the direct image factors through the
proper-support subsheaf. -/
private theorem exists_abelianExtensionByZero_factor :
    ∃ l : (abelianExtensionByZero B X hX U).obj F ⟶
      (fShriekSubsheaf B U.obj.hom F).val.obj.left,
      l ≫ (fShriekSubsheaf B U.obj.hom F).val.arrow =
        (abelianExtensionByZeroToPushforward B X hX U).app F := by
  let R := abelianRestriction B X hX U
  let adj := abelianExtensionByZeroAdjunction B X hX U
  let α := (abelianExtensionByZeroToPushforward B X hX U).app F
  let G := (fShriekSubsheaf B U.obj.hom F).val
  obtain ⟨a, ha⟩ := exists_sheaf_lift_of_range_subset
    ((adj.homEquiv _ _) α) (R.map G.arrow)
      (fun W => (AddCommGrpCat.mono_iff_injective _).mp inferInstance) (by
        rintro W s ⟨t, rfl⟩
        exact ((fShriekSubsheaf B U.obj.hom F).property
          ((smallEtalePostcompose B X hX U).obj W.unop) _).mpr
            (graphSection_hasProperSupport B X hX U F W.unop t))
  refine ⟨(adj.homEquiv _ _).symm a, ?_⟩
  apply (adj.homEquiv _ _).injective
  rwa [adj.homEquiv_naturality_right, Equiv.apply_symm_apply]

/-- A section with proper support which vanishes on a whole fibre of the first projection
vanishes over a Zariski open neighbourhood of the corresponding point of the test object. -/
private theorem exists_open_restrict_eq_zero_of_fiber_zero {Y Z : B.Scheme} (f : Y ⟶ Z)
    [LocallyOfFiniteType (B.inclusion.map f)]
    (G : Sheaf (SmallEtale.topology B Y.1 Y.property) AddCommGrpCat.{u + 1})
    (V : SmallEtale B Z.1 Z.property)
    (s : G.obj.obj (op ((smallEtaleBaseChange B f).obj V)))
    (hs : properSupportSections B f G V s)
    (v : (SmallEtale.toScheme B Z.1 Z.property).obj V)
    (hv : ∀ z : (SmallEtale.toScheme B Y.1 Y.property).obj ((smallEtaleBaseChange B f).obj V),
      B.inclusion.map (pullback.fst V.obj.hom f) z = v →
      z ∈ zeroOpen B Y.1 Y.property G ((smallEtaleBaseChange B f).obj V) s) :
    ∃ O : ((SmallEtale.toScheme B Z.1 Z.property).obj V).Opens,
      v ∈ O ∧ G.obj.map ((smallEtaleBaseChange B f).map
        (openObjectι B Z.1 Z.property V O)).op s = 0 := by
  let P := (smallEtaleBaseChange B f).obj V
  let q := B.inclusion.map (pullback.fst V.obj.hom f)
  let Zs : Closeds ((SmallEtale.toScheme B Y.1 Y.property).obj P) :=
    (zeroOpen B Y.1 Y.property G P s).compl
  have : LocallyOfFiniteType q :=
    MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback V.obj.hom f).flip.map B.inclusion) inferInstance
  obtain ⟨O, hvO, hO⟩ := exists_opens_mem_disjoint_image_of_isProperOver q Zs hs v
    (fun z hz heq => hz (hv z heq))
  refine ⟨O, hvO, ?_⟩
  let g := openObjectι B Z.1 Z.property V O
  let c := (smallEtaleBaseChange B f).map g
  apply (map_eq_zero_iff_range_subset_zeroOpen B Y.1 Y.property G P s _ c).mpr
  rintro _ ⟨z, rfl⟩
  by_contra hz
  apply hO _ hz
  have h := congrArg (fun k => k z) (smallEtaleBaseChange_map_fst B f g)
  change q ((SmallEtale.toScheme B Y.1 Y.property).map c z) =
    (SmallEtale.toScheme B Z.1 Z.property).map g
      (B.inclusion.map (pullback.fst (openObject B Z.1 Z.property V O).obj.hom f) z) at h
  rw [h, openObjectι_map]
  exact (B.inclusion.map
    (pullback.fst (openObject B Z.1 Z.property V O).obj.hom f) z).property

/-- Restricting the image of `graphLift` along the transported graph recovers the section. -/
private theorem graphLift_restrict (W : SmallEtale B U.obj.left.1 U.obj.left.property)
    (V : SmallEtale B X hX) (e : (smallEtalePostcompose B X hX U).obj W ≅ V)
    (s : F.obj.obj (op W)) :
    F.obj.map (smallEtaleGraph B X hX U W ≫
      (smallEtaleBaseChange B U.obj.hom).map e.hom).op
      ((((abelianExtensionByZeroToPushforward B X hX U).app F).hom.app (op V))
        (graphLift B X hX U F W V e s)) = s := by
  rw [graphLift_image, ← ConcreteCategory.comp_apply, ← F.obj.map_comp, ← op_comp]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id]
  rw [(smallEtaleBaseChange B U.obj.hom).map_id, Category.comp_id]
  exact abelianExtensionByZeroToPushforward_graph B X hX U F W s

/-- The image of `graphLift` restricts to zero along any arrow avoiding the transported
graph. -/
private theorem graphLift_restrict_eq_zero
    (W T : SmallEtale B U.obj.left.1 U.obj.left.property) (V : SmallEtale B X hX)
    (e : (smallEtalePostcompose B X hX U).obj W ≅ V) (s : F.obj.obj (op W))
    (g : T ⟶ (smallEtaleBaseChange B U.obj.hom).obj V)
    (hg : disjointFromSmallEtaleGraph B X hX U W T
      (g ≫ (smallEtaleBaseChange B U.obj.hom).map e.inv)) :
    F.obj.map g.op
      ((((abelianExtensionByZeroToPushforward B X hX U).app F).hom.app (op V))
        (graphLift B X hX U F W V e s)) = 0 := by
  rw [graphLift_image, ← ConcreteCategory.comp_apply, ← F.obj.map_comp, ← op_comp]
  exact abelianExtensionByZeroToPushforward_graph_compl B X hX U F W T _ hg s

end Graph

/-! ### Sections through open copies of a base change -/

/-- A section of `P' ⟶ V'` lying over an open `D` of `S ×_T Y` which maps isomorphically onto
`Y` factors through `D` after composing with the map `P' ⟶ S ×_T Y`. -/
private theorem comp_eq_of_section_openCopy {S T Y V' P' : Scheme.{u}} {q : S ⟶ T}
    {b : Y ⟶ T} {D : (pullback q b).Opens} [IsIso (D.ι ≫ pullback.snd q b)] {ι : V' ⟶ Y}
    {q' : P' ⟶ V'} {c : P' ⟶ S} {δ : P' ⟶ pullback q b} (hδfst : δ ≫ pullback.fst q b = c)
    (hδsnd : δ ≫ pullback.snd q b = q' ≫ ι) {σ : V' ⟶ P'} (hσq : σ ≫ q' = 𝟙 V')
    (hσc : σ ≫ c = ι ≫ inv (D.ι ≫ pullback.snd q b) ≫ D.ι ≫ pullback.fst q b) :
    σ ≫ δ = ι ≫ inv (D.ι ≫ pullback.snd q b) ≫ D.ι := by
  apply pullback.hom_ext
  · simp only [Category.assoc, hδfst, hσc]
  · rw [Category.assoc, hδsnd, ← Category.assoc, hσq, Category.id_comp]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- Let `D i` be finitely many pairwise disjoint opens of `S ×_T Y`, each mapping isomorphically
onto `Y`, and covering the points over `pt` lying over `Z`. For an open immersion `V' ⟶ Y` and the
base change `P' ⟶ V'`, sections lying over the `D i` have pairwise disjoint images, and those
images contain every point over a preimage of `pt` whose image in `S` lies in `Z`. -/
private theorem sections_openCopies_disjoint_and_cover {S T Y V' P' : Scheme.{u}} {q : S ⟶ T}
    {b : Y ⟶ T} {n : ℕ} {D : Fin n → (pullback q b).Opens}
    [∀ i, IsIso ((D i).ι ≫ pullback.snd q b)] (hpair : Pairwise (Disjoint on D))
    {Z : Closeds S} {pt : Y}
    (hsupport : ∀ p : (pullback q b : Scheme), pullback.snd q b p = pt →
      pullback.fst q b p ∈ Z → ∃ i, p ∈ D i)
    {ι : V' ⟶ Y} [IsOpenImmersion ι] {q' : P' ⟶ V'} {c : P' ⟶ S}
    (hcart : IsPullback c q' q (ι ≫ b)) {σ : Fin n → (V' ⟶ P')} (hσq : ∀ i, σ i ≫ q' = 𝟙 V')
    (hσc : ∀ i, σ i ≫ c = ι ≫ inv ((D i).ι ≫ pullback.snd q b) ≫ (D i).ι ≫ pullback.fst q b)
    {x' : V'} (hx' : ι x' = pt) :
    (Pairwise fun i j => Disjoint (Set.range (σ i)) (Set.range (σ j))) ∧
      ∀ z, q' z = x' → c z ∈ Z → ∃ i, z ∈ Set.range (σ i) := by
  let δ : P' ⟶ pullback q b :=
    pullback.lift c (q' ≫ ι) (by simpa only [Category.assoc] using hcart.w)
  have hδfst : δ ≫ pullback.fst q b = c := pullback.lift_fst _ _ _
  have hδsnd : δ ≫ pullback.snd q b = q' ≫ ι := pullback.lift_snd _ _ _
  have hδcart : IsPullback δ q' (pullback.snd q b) ι :=
    IsPullback.of_right (by rwa [hδfst]) hδsnd (IsPullback.of_hasPullback q b)
  have : IsOpenImmersion δ := MorphismProperty.of_isPullback hδcart.flip inferInstance
  have hσδ (i) := comp_eq_of_section_openCopy hδfst hδsnd (hσq i) (hσc i)
  have hmem (i) (z : V') : δ (σ i z) ∈ D i := by
    have h : δ (σ i z) = (D i).ι (inv ((D i).ι ≫ pullback.snd q b) (ι z)) :=
      congrArg (fun f => f z) (hσδ i)
    rw [h]
    exact (inv ((D i).ι ≫ pullback.snd q b) (ι z)).property
  refine ⟨fun i j hij => Set.disjoint_left.mpr ?_, fun z hz hzc => ?_⟩
  · rintro z ⟨zi, rfl⟩ ⟨zj, hzj⟩
    exact Set.disjoint_left.mp (TopologicalSpace.Opens.coe_disjoint.mpr (hpair hij))
      (hmem i zi) (hzj ▸ hmem j zj)
  have hzδ : pullback.snd q b (δ z) = pt := by
    have h := congrArg (fun f => f z) hδsnd
    change pullback.snd q b (δ z) = ι (q' z) at h
    rw [h, hz, hx']
  have hzδZ : pullback.fst q b (δ z) ∈ Z := (congrArg (fun f => f z) hδfst) ▸ hzc
  obtain ⟨i, hi⟩ := hsupport (δ z) hzδ hzδZ
  refine ⟨i, q' z, δ.isOpenEmbedding.injective ?_⟩
  have hid : inv ((D i).ι ≫ pullback.snd q b) (pullback.snd q b (δ z)) =
      (⟨δ z, hi⟩ : (↑(D i) : Scheme)) :=
    congrArg (fun f => f (⟨δ z, hi⟩ : (↑(D i) : Scheme)))
      (IsIso.hom_inv_id ((D i).ι ≫ pullback.snd q b))
  have hpoint := congrArg (fun f => f (q' z)) (hσδ i)
  change δ (σ i (q' z)) = _ at hpoint
  rw [hpoint]
  have hbase : ι (q' z) = pullback.snd q b (δ z) := (congrArg (fun f => f z) hδsnd).symm
  change (D i).ι (inv ((D i).ι ≫ pullback.snd q b) (ι (q' z))) = δ z
  rw [hbase, hid]
  rfl

section Disjoint

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (U : SmallEtale B X hX)

/-- An arrow whose image misses the transported graph of `W` avoids that graph in the
étale-test-object sense. -/
private theorem graph_disjoint_of_disjoint_ranges
    (W T : SmallEtale B U.obj.left.1 U.obj.left.property) (V : SmallEtale B X hX)
    (e : (smallEtalePostcompose B X hX U).obj W ≅ V)
    (c : T ⟶ (smallEtaleBaseChange B U.obj.hom).obj V)
    (hd : Disjoint
      (Set.range ((SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map
        (smallEtaleGraph B X hX U W ≫ (smallEtaleBaseChange B U.obj.hom).map e.hom)))
      (Set.range ((SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map c))) :
    disjointFromSmallEtaleGraph B X hX U W T
      (c ≫ (smallEtaleBaseChange B U.obj.hom).map e.inv) := by
  intro S hS a b hab
  have h := congrArg (fun k => k ≫ (smallEtaleBaseChange B U.obj.hom).map e.hom) hab
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id] at h
  rw [(smallEtaleBaseChange B U.obj.hom).map_id, Category.comp_id] at h
  exact ne_of_disjoint_ranges _ _ hd hS a b h

/-- Every point of a scheme étale over an object of the small étale site lies in the image of an
open immersion from an object of that site, through which the structure morphism factors. -/
private theorem exists_smallEtale_openImmersion_point (V : SmallEtale B X hX) {Y : Scheme.{u}}
    (f : Y ⟶ (SmallEtale.toScheme B X hX).obj V) [Etale f] (y : Y) :
    ∃ (V' : SmallEtale B X hX) (g : V' ⟶ V) (ι : (SmallEtale.toScheme B X hX).obj V' ⟶ Y)
      (y' : (SmallEtale.toScheme B X hX).obj V'),
      IsOpenImmersion ι ∧ (SmallEtale.toScheme B X hX).map g = ι ≫ f ∧ ι y' = y := by
  obtain ⟨A, hA, hyA, _⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) (by simp)
  have : _root_.AlgebraicGeometry.IsAffine A.toScheme := hA
  have hsize : B.Contains A.toScheme :=
    (Scheme.size_le_of_locallyOfFiniteType (A.ι ≫ f)).trans_lt V.obj.left.property
  let k : B.obj A.toScheme hsize ⟶ V.obj.left := B.inclusion.preimage (A.ι ≫ f)
  let V' : SmallEtale B X hX := ⟨Over.mk (k ≫ V.obj.hom), by
    change Etale (B.inclusion.map (k ≫ V.obj.hom))
    rw [Functor.map_comp, B.inclusion.map_preimage]
    infer_instance⟩
  exact ⟨V', ObjectProperty.homMk (Over.homMk k), A.ι, ⟨y, hyA⟩,
    (inferInstance : IsOpenImmersion A.ι), B.inclusion.map_preimage _, rfl⟩

/-- The object of the small étale site of `U` given by a morphism `γ` from `V'` to the base
change of `U` to `V` which is étale over `U`. -/
private def sectionObj (V V' : SmallEtale B X hX)
    (γ : (SmallEtale.toScheme B X hX).obj V' ⟶
      (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).obj
        ((smallEtaleBaseChange B U.obj.hom).obj V))
    (hγ : Etale (γ ≫ B.inclusion.map (pullback.snd V.obj.hom U.obj.hom))) :
    SmallEtale B U.obj.left.1 U.obj.left.property :=
  ⟨Over.mk (B.inclusion.preimage (γ ≫ B.inclusion.map (pullback.snd V.obj.hom U.obj.hom)) :
    V'.obj.left ⟶ U.obj.left), by
      change Etale (B.inclusion.map (B.inclusion.preimage _))
      rw [B.inclusion.map_preimage]
      exact hγ⟩

/-- When `γ` lies over a morphism `g : V' ⟶ V`, the image of `sectionObj` in the small étale site
of `X` is `V'`. -/
private def sectionIso (V V' : SmallEtale B X hX) (g : V' ⟶ V)
    (γ : (SmallEtale.toScheme B X hX).obj V' ⟶
      (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).obj
        ((smallEtaleBaseChange B U.obj.hom).obj V))
    (hγq : γ ≫ B.inclusion.map (pullback.fst V.obj.hom U.obj.hom) =
      (SmallEtale.toScheme B X hX).map g)
    (hγ : Etale (γ ≫ B.inclusion.map (pullback.snd V.obj.hom U.obj.hom))) :
    (smallEtalePostcompose B X hX U).obj (sectionObj B X hX U V V' γ hγ) ≅ V' :=
  ObjectProperty.isoMk _ (Over.isoMk (Iso.refl V'.obj.left) (by
    change 𝟙 V'.obj.left ≫ V'.obj.hom =
      (B.inclusion.preimage (γ ≫ B.inclusion.map (pullback.snd V.obj.hom U.obj.hom)) :
        V'.obj.left ⟶ U.obj.left) ≫ U.obj.hom
    have hcond := ((IsPullback.of_hasPullback V.obj.hom U.obj.hom).map B.inclusion).w
    rw [Category.id_comp]
    apply B.inclusion.map_injective
    rw [Functor.map_comp, B.inclusion.map_preimage]
    exact ((B.inclusion.map_comp g.hom.left V.obj.hom).symm.trans
      (congrArg B.inclusion.map (Over.w g.hom))).symm.trans
      ((congrArg (· ≫ B.inclusion.map V.obj.hom) hγq).symm.trans
        (((Category.assoc _ _ _).trans (congrArg (γ ≫ ·) hcond)).trans
          (Category.assoc _ _ _).symm))))

/-- The transported graph of `sectionObj` is a section of the first projection of the base
change to `V'`, and composing it with the base change of `g` recovers `γ`. -/
private theorem sectionObj_graph (V V' : SmallEtale B X hX) (g : V' ⟶ V)
    (γ : (SmallEtale.toScheme B X hX).obj V' ⟶
      (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).obj
        ((smallEtaleBaseChange B U.obj.hom).obj V))
    (hγq : γ ≫ B.inclusion.map (pullback.fst V.obj.hom U.obj.hom) =
      (SmallEtale.toScheme B X hX).map g)
    (hγ : Etale (γ ≫ B.inclusion.map (pullback.snd V.obj.hom U.obj.hom))) :
    (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map
        (smallEtaleGraph B X hX U (sectionObj B X hX U V V' γ hγ) ≫
          (smallEtaleBaseChange B U.obj.hom).map (sectionIso B X hX U V V' g γ hγq hγ).hom) ≫
      B.inclusion.map (pullback.fst V'.obj.hom U.obj.hom) =
        𝟙 ((SmallEtale.toScheme B X hX).obj V') ∧
    (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map
        (smallEtaleGraph B X hX U (sectionObj B X hX U V V' γ hγ) ≫
          (smallEtaleBaseChange B U.obj.hom).map (sectionIso B X hX U V V' g γ hγq hγ).hom) ≫
      (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map
        ((smallEtaleBaseChange B U.obj.hom).map g) = γ := by
  let P := (smallEtaleBaseChange B U.obj.hom).obj V
  let q : (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).obj P ⟶
      (SmallEtale.toScheme B X hX).obj V :=
    B.inclusion.map (pullback.fst V.obj.hom U.obj.hom)
  let r : (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).obj P ⟶ U.obj.left.1 :=
    B.inclusion.map (pullback.snd V.obj.hom U.obj.hom)
  have hγq' : γ ≫ q = (SmallEtale.toScheme B X hX).map g := hγq
  let a : V'.obj.left ⟶ U.obj.left := B.inclusion.preimage (γ ≫ r)
  have hai : B.inclusion.map a = γ ≫ r := B.inclusion.map_preimage _
  let W := sectionObj B X hX U V V' γ hγ
  let e := sectionIso B X hX U V V' g γ hγq hγ
  let q' : (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).obj
      ((smallEtaleBaseChange B U.obj.hom).obj V') ⟶ (SmallEtale.toScheme B X hX).obj V' :=
    B.inclusion.map (pullback.fst V'.obj.hom U.obj.hom)
  let r' : (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).obj
      ((smallEtaleBaseChange B U.obj.hom).obj V') ⟶ U.obj.left.1 :=
    B.inclusion.map (pullback.snd V'.obj.hom U.obj.hom)
  let c := (smallEtaleBaseChange B U.obj.hom).map g
  let cₛ := (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map c
  have hcq : cₛ ≫ q = q' ≫ (SmallEtale.toScheme B X hX).map g :=
    smallEtaleBaseChange_map_fst B U.obj.hom g
  have hcleft : c.hom.left ≫ pullback.snd V.obj.hom U.obj.hom =
      pullback.snd V'.obj.hom U.obj.hom := pullback.lift_snd _ _ _
  have hcsnd : cₛ ≫ r = r' :=
    (B.inclusion.map_comp c.hom.left (pullback.snd V.obj.hom U.obj.hom)).symm.trans
      (congrArg B.inclusion.map hcleft)
  let b := smallEtaleGraph B X hX U W ≫ (smallEtaleBaseChange B U.obj.hom).map e.hom
  let bₛ := (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map b
  have hb : b.hom.left ≫ pullback.fst V'.obj.hom U.obj.hom = 𝟙 V'.obj.left := by
    change (pullback.lift (𝟙 V'.obj.left) a _ ≫
      pullback.lift (pullback.fst _ _ ≫ 𝟙 V'.obj.left) (pullback.snd _ _) _) ≫
        pullback.fst _ _ = _
    simp only [Category.assoc, pullback.lift_fst, Category.comp_id]
    exact pullback.lift_fst _ _ _
  have hbq : bₛ ≫ q' = 𝟙 ((SmallEtale.toScheme B X hX).obj V') :=
    (B.inclusion.map_comp _ _).symm.trans
      ((congrArg B.inclusion.map hb).trans (B.inclusion.map_id _))
  have hbsnd : bₛ ≫ r' = γ ≫ r :=
    (B.inclusion.map_comp _ _).symm.trans ((congrArg B.inclusion.map (Over.w b.hom)).trans hai)
  refine ⟨hbq, ?_⟩
  change bₛ ≫ cₛ = γ
  apply ((IsPullback.of_hasPullback V.obj.hom U.obj.hom).map B.inclusion).hom_ext
  · change (bₛ ≫ cₛ) ≫ q = γ ≫ q
    rw [Category.assoc, hcq, ← Category.assoc, hbq]
    exact (Category.id_comp _).trans hγq'.symm
  · change (bₛ ≫ cₛ) ≫ r = γ ≫ r
    rw [Category.assoc, hcsnd, hbsnd]

variable [IsSeparated (B.inclusion.map U.obj.hom)]
  (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1})

/-- The support of the image of `graphLift` is contained in the transported graph. -/
private theorem graphLift_support_subset
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) (V : SmallEtale B X hX)
    (e : (smallEtalePostcompose B X hX U).obj W ≅ V) (s : F.obj.obj (op W)) :
    supportSection B U.obj.left.1 U.obj.left.property F
      ((smallEtaleBaseChange B U.obj.hom).obj V)
      ((((abelianExtensionByZeroToPushforward B X hX U).app F).hom.app (op V))
        (graphLift B X hX U F W V e s)) ⊆
      Set.range ((SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map
        (smallEtaleGraph B X hX U W ≫ (smallEtaleBaseChange B U.obj.hom).map e.hom)) := by
  let P := (smallEtaleBaseChange B U.obj.hom).obj V
  let g := smallEtaleGraph B X hX U W ≫ (smallEtaleBaseChange B U.obj.hom).map e.hom
  let gs := (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map g
  have : IsClosedImmersion gs := by
    change IsClosedImmersion ((SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map
      (smallEtaleGraph B X hX U W) ≫
      (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map
        ((smallEtaleBaseChange B U.obj.hom).map e.hom))
    have := isClosedImmersion_map_smallEtaleGraph B X hX U W
    infer_instance
  exact supportSection_subset_of_forall_disjoint_eq_zero B U.obj.left.1 U.obj.left.property F P _
    gs.isClosedEmbedding.isClosed_range fun T c hd =>
      graphLift_restrict_eq_zero B X hX U F W T V e s c
        (graph_disjoint_of_disjoint_ranges B X hX U W T V e c hd)

/-- Over a set of points of the base change covered by finitely many pairwise disjoint
transported graphs, a section agrees with the image of a section of the extension by zero. -/
private theorem exists_graph_sum_zeroOn (V : SmallEtale B X hX) (n : ℕ)
    (W : Fin n → SmallEtale B U.obj.left.1 U.obj.left.property)
    (e : ∀ i, (smallEtalePostcompose B X hX U).obj (W i) ≅ V)
    (s : F.obj.obj (op ((smallEtaleBaseChange B U.obj.hom).obj V)))
    (Z : Set ((SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).obj
      ((smallEtaleBaseChange B U.obj.hom).obj V)))
    (hd : Pairwise fun i j => Disjoint
      (Set.range ((SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map
        (smallEtaleGraph B X hX U (W i) ≫
          (smallEtaleBaseChange B U.obj.hom).map (e i).hom)))
      (Set.range ((SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map
        (smallEtaleGraph B X hX U (W j) ≫
          (smallEtaleBaseChange B U.obj.hom).map (e j).hom))))
    (hZ : ∀ z ∈ Z, z ∈ supportSection
      B U.obj.left.1 U.obj.left.property F ((smallEtaleBaseChange B U.obj.hom).obj V) s →
      ∃ i, z ∈ Set.range ((SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map
        (smallEtaleGraph B X hX U (W i) ≫
          (smallEtaleBaseChange B U.obj.hom).map (e i).hom))) :
    ∃ t, ∀ z ∈ Z, z ∈ zeroOpen
      B U.obj.left.1 U.obj.left.property F ((smallEtaleBaseChange B U.obj.hom).obj V)
      (s - (show F.obj.obj (op ((smallEtaleBaseChange B U.obj.hom).obj V)) from
        (((abelianExtensionByZeroToPushforward B X hX U).app F).hom.app (op V)) t)) := by
  classical
  let P := (smallEtaleBaseChange B U.obj.hom).obj V
  let g (i) := smallEtaleGraph B X hX U (W i) ≫
    (smallEtaleBaseChange B U.obj.hom).map (e i).hom
  let α : ((abelianExtensionByZero B X hX U).obj F).obj.obj (op V) ⟶ F.obj.obj (op P) :=
    ((abelianExtensionByZeroToPushforward B X hX U).app F).hom.app (op V)
  let σ (i) := F.obj.map (g i).op s
  let t (i) := graphLift B X hX U F (W i) V (e i) (σ i)
  refine ⟨∑ i, t i, ?_⟩
  have hi (i) : F.obj.map (g i).op (s - α (∑ j, t j)) = 0 := by
    have hsum : F.obj.map (g i).op (α (∑ j, t j)) = σ i := by
      simp only [map_sum]
      rw [Finset.sum_eq_single i]
      · exact graphLift_restrict B X hX U F (W i) V (e i) (σ i)
      · intro j _ hji
        exact graphLift_restrict_eq_zero B X hX U F (W j) (W i) V (e j) (σ j) (g i)
          (graph_disjoint_of_disjoint_ranges B X hX U (W j) (W i) V (e j) (g i) (hd hji))
      · simp
    rw [map_sub, hsum, sub_self]
  intro z hz
  by_cases hzg : ∃ i, z ∈ Set.range
      ((SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map (g i))
  · obtain ⟨i, hzi⟩ := hzg
    exact (map_eq_zero_iff_range_subset_zeroOpen B U.obj.left.1
      U.obj.left.property F P _ (W i) (g i)).mp (hi i) hzi
  · apply mem_zeroOpen_sub
    · by_contra hzs
      exact hzg (hZ z hz hzs)
    · have ht (i) : z ∈ zeroOpen B U.obj.left.1 U.obj.left.property F P (α (t i)) := by
        by_contra hzt
        exact hzg ⟨i, graphLift_support_subset B X hX U F (W i) V (e i) (σ i) hzt⟩
      change z ∈ zeroOpen B U.obj.left.1 U.obj.left.property F P (α (∑ i, t i))
      rw [map_sum]
      exact mem_zeroOpen_sum B U.obj.left.1 U.obj.left.property F P Finset.univ
        (fun i => α (t i)) (fun i _ => ht i)

/-- The image in the direct image of a section of the extension by zero has proper support. -/
private theorem properSupportSections_abelianExtensionByZeroToPushforward (V : SmallEtale B X hX)
    (t : ((abelianExtensionByZero B X hX U).obj F).obj.obj (op V)) :
    properSupportSections B U.obj.hom F V
      (((abelianExtensionByZeroToPushforward B X hX U).app F).hom.app (op V) t) := by
  obtain ⟨l, hl⟩ := exists_abelianExtensionByZero_factor B X hX U F
  exact ((fShriekSubsheaf B U.obj.hom F).property V _).mp ⟨l.hom.app (op V) t,
    ConcreteCategory.congr_hom (congrArg (fun k => k.hom.app (op V)) hl) t⟩

/-- A section with proper support which agrees on one fibre with the image of a section of the
extension by zero agrees with it over a whole étale neighbourhood of that fibre. -/
private theorem exists_local_preimage_of_fiber_agreement (V : SmallEtale B X hX)
    (s : F.obj.obj (op ((smallEtaleBaseChange B U.obj.hom).obj V)))
    (hs : properSupportSections B U.obj.hom F V s)
    (v : (SmallEtale.toScheme B X hX).obj V)
    (t : ((abelianExtensionByZero B X hX U).obj F).obj.obj (op V))
    (ht : ∀ z : (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).obj
      ((smallEtaleBaseChange B U.obj.hom).obj V),
      B.inclusion.map (pullback.fst V.obj.hom U.obj.hom) z = v →
      z ∈ zeroOpen B U.obj.left.1 U.obj.left.property F
        ((smallEtaleBaseChange B U.obj.hom).obj V)
        (s - (show F.obj.obj (op ((smallEtaleBaseChange B U.obj.hom).obj V)) from
          (((abelianExtensionByZeroToPushforward B X hX U).app F).hom.app (op V)) t))) :
    ∃ (W : SmallEtale B X hX) (g : W ⟶ V),
      Etale ((SmallEtale.toScheme B X hX).map g) ∧
      v ∈ Set.range ((SmallEtale.toScheme B X hX).map g) ∧
      F.obj.map ((smallEtaleBaseChange B U.obj.hom).map g).op s ∈
        Set.range (((abelianExtensionByZeroToPushforward B X hX U).app F).hom.app (op W)) := by
  let α := (abelianExtensionByZeroToPushforward B X hX U).app F
  let a : F.obj.obj (op ((smallEtaleBaseChange B U.obj.hom).obj V)) := α.hom.app (op V) t
  have ha : properSupportSections B U.obj.hom F V a :=
    properSupportSections_abelianExtensionByZeroToPushforward B X hX U F V t
  have hdiff : properSupportSections B U.obj.hom F V (s - a) :=
    (properSupportSubgroup B U.obj.hom F V).sub_mem hs ha
  obtain ⟨O, hvO, hO⟩ :=
    exists_open_restrict_eq_zero_of_fiber_zero B U.obj.hom F V (s - a) hdiff v ht
  let W := openObject B X hX V O
  let g := openObjectι B X hX V O
  have hg := openObjectι_map B X hX V O
  refine ⟨W, g, ?_, ?_, ?_⟩
  · exact hg ▸ (inferInstance : Etale O.ι)
  · rwa [openObjectι_range B X hX V O]
  · refine ⟨((abelianExtensionByZero B X hX U).obj F).obj.map g.op t, ?_⟩
    have hm := ConcreteCategory.congr_hom (α.hom.naturality g.op) t
    have hz : F.obj.map ((smallEtaleBaseChange B U.obj.hom).map g).op s =
        F.obj.map ((smallEtaleBaseChange B U.obj.hom).map g).op a :=
      sub_eq_zero.mp (by simpa only [map_sub] using hO)
    exact hm.trans hz.symm

omit [IsSeparated (B.inclusion.map U.obj.hom)] in
/-- If a restriction of a section along an étale morphism `g` lies in the image of the extension
by zero over an étale neighbourhood of a point, so does the section near the image of the point. -/
private theorem exists_etale_nbhd_mem_range_comp (V V' : SmallEtale B X hX) (g : V' ⟶ V)
    [Etale ((SmallEtale.toScheme B X hX).map g)]
    (s : F.obj.obj (op ((smallEtaleBaseChange B U.obj.hom).obj V)))
    (x' : (SmallEtale.toScheme B X hX).obj V')
    (h : ∃ (W : SmallEtale B X hX) (g' : W ⟶ V'),
      Etale ((SmallEtale.toScheme B X hX).map g') ∧
      x' ∈ Set.range ((SmallEtale.toScheme B X hX).map g') ∧
      F.obj.map ((smallEtaleBaseChange B U.obj.hom).map g').op
          (F.obj.map ((smallEtaleBaseChange B U.obj.hom).map g).op s) ∈
        Set.range (((abelianExtensionByZeroToPushforward B X hX U).app F).hom.app (op W))) :
    ∃ (W : SmallEtale B X hX) (g'' : W ⟶ V),
      Etale ((SmallEtale.toScheme B X hX).map g'') ∧
      (SmallEtale.toScheme B X hX).map g x' ∈
        Set.range ((SmallEtale.toScheme B X hX).map g'') ∧
      F.obj.map ((smallEtaleBaseChange B U.obj.hom).map g'').op s ∈
        Set.range (((abelianExtensionByZeroToPushforward B X hX U).app F).hom.app (op W)) := by
  obtain ⟨V'', g', hg', ⟨z, hz⟩, ht'⟩ := h
  refine ⟨V'', g' ≫ g, ?_, ⟨z, ?_⟩, ?_⟩
  · rw [Functor.map_comp]
    infer_instance
  · rw [Functor.map_comp, Scheme.Hom.comp_apply, hz]
  · rwa [Functor.map_comp, op_comp, F.obj.map_comp, ConcreteCategory.comp_apply]

/-- If `V' ⟶ V` factors through an étale `Y ⟶ V` over which the base change of `U` has disjoint
copies of `Y` covering the support of `s` over the point below `x'`, then `s` lies in the image
of the extension by zero over an étale neighbourhood of the image of `x'`. -/
private theorem exists_etale_nbhd_mem_range_of_openCopies (V V' : SmallEtale B X hX)
    (g : V' ⟶ V) (s : F.obj.obj (op ((smallEtaleBaseChange B U.obj.hom).obj V)))
    (hs : properSupportSections B U.obj.hom F V s) {Y : Scheme.{u}}
    (b : Y ⟶ (SmallEtale.toScheme B X hX).obj V) [Etale b]
    (ι : (SmallEtale.toScheme B X hX).obj V' ⟶ Y) [IsOpenImmersion ι]
    (hg : (SmallEtale.toScheme B X hX).map g = ι ≫ b)
    (q : (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).obj
      ((smallEtaleBaseChange B U.obj.hom).obj V) ⟶ (SmallEtale.toScheme B X hX).obj V)
    (hq : q = B.inclusion.map (pullback.fst V.obj.hom U.obj.hom)) {n : ℕ}
    (D : Fin n → (pullback q b).Opens) [∀ i, IsIso ((D i).ι ≫ pullback.snd q b)]
    (hpair : Pairwise (Disjoint on D)) {pt : Y}
    (hsupport : ∀ p : (pullback q b : Scheme), pullback.snd q b p = pt →
      pullback.fst q b p ∈ (zeroOpen B U.obj.left.1 U.obj.left.property F
        ((smallEtaleBaseChange B U.obj.hom).obj V) s).compl → ∃ i, p ∈ D i)
    (x' : (SmallEtale.toScheme B X hX).obj V') (hx' : ι x' = pt) :
    ∃ (W : SmallEtale B X hX) (g' : W ⟶ V),
      Etale ((SmallEtale.toScheme B X hX).map g') ∧
      (SmallEtale.toScheme B X hX).map g x' ∈
        Set.range ((SmallEtale.toScheme B X hX).map g') ∧
      F.obj.map ((smallEtaleBaseChange B U.obj.hom).map g').op s ∈
        Set.range (((abelianExtensionByZeroToPushforward B X hX U).app F).hom.app (op W)) := by
  let P := (smallEtaleBaseChange B U.obj.hom).obj V
  let r : (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).obj P ⟶ U.obj.left.1 :=
    B.inclusion.map (pullback.snd V.obj.hom U.obj.hom)
  have : Etale r := P.property
  have : Etale ((SmallEtale.toScheme B X hX).map g) := by
    rw [hg]
    infer_instance
  let γ (i) : (SmallEtale.toScheme B X hX).obj V' ⟶
      (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).obj P :=
    ι ≫ inv ((D i).ι ≫ pullback.snd q b) ≫ (D i).ι ≫ pullback.fst q b
  have hγq (i) : γ i ≫ q = ι ≫ b := by
    simp only [γ, Category.assoc, pullback.condition]
    rw [← Category.assoc (D i).ι, IsIso.inv_hom_id_assoc]
  have hγ (i) : Etale (γ i ≫ r) := by
    dsimp only [γ]
    infer_instance
  have hγq' (i) : γ i ≫ B.inclusion.map (pullback.fst V.obj.hom U.obj.hom) =
      (SmallEtale.toScheme B X hX).map g :=
    (congrArg (γ i ≫ ·) hq).symm.trans ((hγq i).trans hg.symm)
  let W (i) := sectionObj B X hX U V V' (γ i) (hγ i)
  let e (i) := sectionIso B X hX U V V' g (γ i) (hγq' i) (hγ i)
  let P' := (smallEtaleBaseChange B U.obj.hom).obj V'
  let q' : (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).obj P' ⟶
      (SmallEtale.toScheme B X hX).obj V' :=
    B.inclusion.map (pullback.fst V'.obj.hom U.obj.hom)
  let c := (smallEtaleBaseChange B U.obj.hom).map g
  let cₛ := (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map c
  have hcart : IsPullback cₛ q' q (ι ≫ b) := by
    rw [← hg, hq]
    exact isPullback_baseChange_projection B U.obj.hom g
  let bₛ (i) := (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map
    (smallEtaleGraph B X hX U (W i) ≫ (smallEtaleBaseChange B U.obj.hom).map (e i).hom)
  have hbq (i) : bₛ i ≫ q' = 𝟙 ((SmallEtale.toScheme B X hX).obj V') :=
    (sectionObj_graph B X hX U V V' g (γ i) (hγq' i) (hγ i)).1
  have hbc (i) : bₛ i ≫ cₛ = γ i :=
    (sectionObj_graph B X hX U V V' g (γ i) (hγq' i) (hγ i)).2
  obtain ⟨hd, hsec⟩ := sections_openCopies_disjoint_and_cover hpair hsupport hcart hbq hbc hx'
  let s' := F.obj.map c.op s
  have hZ (z) (hz : q' z = x')
      (hzs : z ∈ supportSection B U.obj.left.1 U.obj.left.property F P' s') :
      ∃ i, z ∈ Set.range (bₛ i) :=
    hsec z hz fun hzero =>
      hzs ((coe_zeroOpen_map B U.obj.left.1 U.obj.left.property F P P' c s).ge hzero)
  obtain ⟨t, ht⟩ := exists_graph_sum_zeroOn B X hX U F V' n W e s' {z | q' z = x'} hd hZ
  exact exists_etale_nbhd_mem_range_comp B X hX U F V V' g s x'
    (exists_local_preimage_of_fiber_agreement B X hX U F V' s'
      (properSupportSections_restrict B U.obj.hom F V V' g s hs) x' t ht)

/-- A section of the direct image with proper support lies, after restriction to an étale
neighbourhood of any given point of the test object, in the image of the extension by zero. -/
private theorem exists_etale_nbhd_mem_range_of_properSupportSections (V : SmallEtale B X hX)
    (s : F.obj.obj (op ((smallEtaleBaseChange B U.obj.hom).obj V)))
    (hs : properSupportSections B U.obj.hom F V s) (x : (SmallEtale.toScheme B X hX).obj V) :
    ∃ (W : SmallEtale B X hX) (g : W ⟶ V),
      Etale ((SmallEtale.toScheme B X hX).map g) ∧
      x ∈ Set.range ((SmallEtale.toScheme B X hX).map g) ∧
      F.obj.map ((smallEtaleBaseChange B U.obj.hom).map g).op s ∈
        Set.range (((abelianExtensionByZeroToPushforward B X hX U).app F).hom.app (op W)) := by
  let P := (smallEtaleBaseChange B U.obj.hom).obj V
  let q : (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).obj P ⟶
      (SmallEtale.toScheme B X hX).obj V :=
    B.inclusion.map (pullback.fst V.obj.hom U.obj.hom)
  have hq := (IsPullback.of_hasPullback V.obj.hom U.obj.hom).flip.map B.inclusion
  have : Etale q := MorphismProperty.of_isPullback hq inferInstance
  have : IsSeparated q := MorphismProperty.of_isPullback hq inferInstance
  obtain ⟨N, R, n, D, hcover, hpair, hdis, hiso, hsupport⟩ :=
    exists_etaleNeighborhood_openCopies_decomposition_of_isProperOver q
      (zeroOpen B U.obj.left.1 U.obj.left.property F P s).compl hs x
  obtain ⟨V', g, ι, x', hι, hg, hxι⟩ :=
    exists_smallEtale_openImmersion_point B X hX V N.toBase N.point
  have : IsOpenImmersion ι := hι
  have : ∀ i, IsIso ((D i).ι ≫ pullback.snd q N.toBase) := hiso
  have hxg : (SmallEtale.toScheme B X hX).map g x' = x := by
    rw [hg, Scheme.Hom.comp_apply, hxι]
    exact N.map_point
  rw [← hxg]
  exact exists_etale_nbhd_mem_range_of_openCopies B X hX U F V V' g s hs N.toBase ι hg q rfl D
    hpair hsupport x' hxι

end Disjoint

/-- A section of an abelian étale sheaf which lies in the image of a morphism of sheaves after
restriction to an étale neighbourhood of each of its points lies locally in that image. -/
private theorem imageSieve_mem_of_pointwise_local_range (B : BigEtaleSite.{u}) (X : Scheme.{u})
    (hX : B.Contains X) {F G : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}}
    (f : F ⟶ G) (V : SmallEtale B X hX) (s : G.obj.obj (op V))
    (hs : ∀ x : (SmallEtale.toScheme B X hX).obj V,
      ∃ (W : SmallEtale B X hX) (g : W ⟶ V),
        Etale ((SmallEtale.toScheme B X hX).map g) ∧
        x ∈ Set.range ((SmallEtale.toScheme B X hX).map g) ∧
        G.obj.map g.op s ∈ Set.range (f.hom.app (op W))) :
    Presheaf.imageSieve f.hom s ∈ SmallEtale.topology B X hX V := by
  classical
  choose W g hg hx hsg using hs
  let E : PreZeroHypercover.{u + 1} ((SmallEtale.toScheme B X hX).obj V) := {
    I₀ := ULift.{u + 1} ((SmallEtale.toScheme B X hX).obj V)
    X i := (SmallEtale.toScheme B X hX).obj (W i.down)
    f i := (SmallEtale.toScheme B X hX).map (g i.down) }
  have hE : E.presieve₀ ∈ Scheme.etalePrecoverage _ :=
    (Scheme.presieve₀_mem_precoverage_iff E).mpr
      ⟨fun x => ⟨⟨x⟩, hx x⟩, fun i => hg i.down⟩
  obtain ⟨R, hR, ⟨θ⟩⟩ := BigEtaleSite.exists_covering_refining_etale_cover B E hE
  have hRet (i) : Etale (B.inclusion.map (R.f i)) :=
    ((Scheme.presieve₀_mem_precoverage_iff (R.map B.inclusion)).mp hR.1).2 i
  let A (i) : SmallEtale B X hX := ⟨Over.mk (R.f i ≫ V.obj.hom), by
    change Etale (B.inclusion.map (R.f i ≫ V.obj.hom))
    rw [Functor.map_comp]
    have := hRet i
    infer_instance⟩
  let a (i) : A i ⟶ V := ObjectProperty.homMk (Over.homMk (R.f i))
  let Rsite : PreZeroHypercover.{u + 1} V := { I₀ := R.I₀, X := A, f := a }
  have hRsite : Sieve.generate Rsite.presieve₀ ∈ SmallEtale.topology B X hX V :=
    Precoverage.generate_mem_toGrothendieck ⟨Rsite, rfl, hR⟩
  apply (SmallEtale.topology B X hX).superset_covering _ hRsite
  rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro i
  let i' : (R.map B.inclusion).I₀ := i
  let k : (SmallEtale.toScheme B X hX).obj V := (θ.s₀ i').down
  let bbase : R.X i ⟶ (W k).obj.left := B.inclusion.preimage (θ.h₀ i')
  have hbbase : B.inclusion.map bbase = θ.h₀ i' := B.inclusion.map_preimage _
  have hfac : bbase ≫ (g k).hom.left = R.f i := by
    apply B.inclusion.map_injective
    rw [Functor.map_comp, hbbase]
    exact θ.w₀ i'
  let b : A i ⟶ W k := ObjectProperty.homMk (Over.homMk bbase (by
    change bbase ≫ (W k).obj.hom = R.f i ≫ V.obj.hom
    rw [← Over.w (g k).hom, ← Category.assoc, hfac]))
  have hba : b ≫ g k = a i := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact hfac
  change (Presheaf.imageSieve f.hom s) (a i)
  rw [← hba]
  exact (Presheaf.imageSieve f.hom s).downward_closed (hsg k) b

/-- **Stacks 0F4Y.** For a separated étale morphism, the image of extension by zero in the
direct image is precisely the proper-support subsheaf. -/
@[stacks 0F4Y]
public theorem abelianExtensionByZeroToPushforward_range_eq_fShriekSubsheaf
    (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (U : SmallEtale B X hX)
    [IsSeparated (B.inclusion.map U.obj.hom)]
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1})
    (V : SmallEtale B X hX) :
    Set.range (((abelianExtensionByZeroToPushforward B X hX U).app F).hom.app (op V)) =
      Set.range (((fShriekSubsheaf B U.obj.hom F).val.arrow).hom.app (op V)) := by
  ext s
  rw [(fShriekSubsheaf B U.obj.hom F).property V s]
  constructor
  · rintro ⟨t, rfl⟩
    exact properSupportSections_abelianExtensionByZeroToPushforward B X hX U F V t
  · intro hs
    have := abelianExtensionByZeroToPushforward_mono B X hX U F
    apply mem_range_of_imageSieve_mem
    apply imageSieve_mem_of_pointwise_local_range B X hX
    exact exists_etale_nbhd_mem_range_of_properSupportSections B X hX U F V s hs

end AlgebraicGeometry.SmallEtale

end
