module

public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.Topology.Constructible
public import Mathlib.Topology.Sheaves.Limits
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.Skyscraper
public import Mathlib.Topology.Spectral.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.EpiMono.Stalk
public import StacksFrontier.Topology.Sheaves.Functors.Pullback.SheafStalk
public import StacksFrontier.Topology.Sheaves.Functors.Pushforward.IsSheaf
public import StacksFrontier.Topology.Sheaves.Spectral.FiniteSoberPullback
public import StacksFrontier.Topology.Sheaves.Stalk.Constant

/-!
# Constructible sheaves of sets embed into products of constant sheaves on closed subspaces

Let `X` be a spectral topological space and let `F` be a sheaf of sets on `X` which is the
coequalizer of two maps between finite coproducts of finite constant sheaves extended from
quasi-compact opens — the presentation `Stacks.HasFiniteBasisCoequalizerPresentation` which
characterises the constructible sheaves of sets. Then there are finitely many closed
constructible subsets `Z₁, …, Zₙ` of `X` and finite sets `S₁, …, Sₙ` such that `F` is
isomorphic to a subsheaf of `∏ (Zᵢ → X)_* S̲ᵢ`.

The argument descends `F` along a spectral map `g : X → Y` to a finite sober space, where it
becomes a sheaf `G` with finite stalks. On the finite space `Y` the canonical maps to the
skyscrapers at the points are jointly monomorphic, so `G` embeds into the finite product of the
skyscrapers at the points of `Y` with values the stalks of `G`. Pulling that embedding back to
`X` and comparing each pulled-back skyscraper with the pushforward of the constant sheaf from
the closed constructible subset `g⁻¹(closure {y})` gives the embedding.

## Main definitions

* `Stacks.constantSheafPushforward`: the pushforward to `X` of the constant sheaf with value
  `S` on a subspace `Z`.

## Main results

* `Stacks.exists_mono_to_pi_constantSheafPushforward`: the embedding of a constructible sheaf
  of sets into a finite product of such pushforwards.

## Implementation notes

Being isomorphic to a subsheaf is expressed as the existence of a monomorphism into the
ambient sheaf, and finite sets are types carrying a `Finite` instance, with the finite product
indexed by `Fin n`.

The comparison between the pullback of a skyscraper and the pushforward of a constant sheaf is
built by adjunction: a map out of the skyscraper at `y` into the pushforward along
`Z → X → Y` of the constant sheaf is what the universal property of the skyscraper asks for,
because every point of `Z` specialises to `y`; its transpose is the required map on `X`. The
transpose is a monomorphism because on stalks it is a surjection between finite sets at points
of `Z`, and both stalks are subsingletons elsewhere.

Skyscrapers are Mathlib's `skyscraperSheaf`, which takes the decidability of `y ∈ U` as an
instance; the auxiliary declarations therefore carry that instance as a hypothesis, and it is
discharged classically once, in the proof of the main theorem.

## References

* [Stacks Project, Tag 0CAL](https://stacks.math.columbia.edu/tag/0CAL)
* [Stacks Project, Tag 0CAK](https://stacks.math.columbia.edu/tag/0CAK)
* [Stacks Project, Tag 009B](https://stacks.math.columbia.edu/tag/009B)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace Stacks

variable {X : Type u} [TopologicalSpace X]

/-- The pushforward to `X` of the constant sheaf with value `S` on the subspace `Z`. -/
noncomputable abbrev constantSheafPushforward (Z : Set X) (S : Type u) :
    TopCat.Sheaf (Type u) (TopCat.of X) :=
  (TopCat.Sheaf.pushforward (Type u)
    (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of Z ⟶ TopCat.of X)).obj
      (constantSheafOnSpace (TopCat.of Z) (Type u) S)

/-- The preimage of a closed subset of a finite space under a spectral map from a spectral
space is constructible. -/
private theorem isConstructible_preimage_closed_of_finite
    [SpectralSpace X] {Y : Type u} [TopologicalSpace Y] [Finite Y]
    (f : TopCat.of X ⟶ TopCat.of Y) (hf : IsSpectralMap f)
    {Z : Set Y} (hZ : IsClosed Z) :
    Topology.IsConstructible (f ⁻¹' Z) := by
  have h := ((Set.toFinite Zᶜ).isCompact.preimage_of_isOpen hf hZ.isOpen_compl).isConstructible
    (hZ.isOpen_compl.preimage hf.continuous)
  simpa only [Set.preimage_compl, compl_compl] using h.compl

/-! ### Embedding a sheaf on a finite space into a product of skyscrapers -/

section Skyscrapers

variable {Y : Type u} [TopologicalSpace Y]

/-- The unit of the stalk–skyscraper adjunction at a point: the canonical map from a sheaf to
the skyscraper at `y` with value its stalk at `y`. -/
private noncomputable def pointMap (G : TopCat.Sheaf (Type u) (TopCat.of Y)) (y : Y)
    [∀ U : Opens Y, Decidable (y ∈ U)] :
    G ⟶ skyscraperSheaf (X := TopCat.of Y) y (G.presheaf.stalk y) :=
  (stalkSkyscraperSheafAdjunction (X := TopCat.of Y) y).unit.app G

/-- Two maps into a sheaf that agree after composing with every `Stacks.pointMap` induce the
same maps on all stalks. -/
private theorem pointMap_reflects_stalks (G H : TopCat.Sheaf (Type u) (TopCat.of Y))
    [∀ (y : Y) (U : Opens Y), Decidable (y ∈ U)] (a b : H ⟶ G)
    (h : ∀ y, a ≫ pointMap G y = b ≫ pointMap G y) :
    ∀ y, (TopCat.Presheaf.stalkFunctor (Type u) y).map a.hom =
      (TopCat.Presheaf.stalkFunctor (Type u) y).map b.hom := by
  intro y
  let adj := stalkSkyscraperSheafAdjunction (C := Type u) (X := TopCat.of Y) y
  have ha := adj.homEquiv_naturality_left_symm a (adj.unit.app G)
  have hb := adj.homEquiv_naturality_left_symm b (adj.unit.app G)
  simp only [adj.homEquiv_symm_unit, Category.comp_id] at ha hb
  exact ha.symm.trans
    ((congrArg (fun q => (adj.homEquiv H (G.presheaf.stalk y)).symm q) (h y)).trans hb)

/-- A morphism of sheaves of sets is determined by the maps it induces on all stalks. -/
private theorem eq_of_stalkMaps_eq (G H : TopCat.Sheaf (Type u) (TopCat.of Y)) (a b : H ⟶ G)
    (h : ∀ y, (TopCat.Presheaf.stalkFunctor (Type u) y).map a.hom =
      (TopCat.Presheaf.stalkFunctor (Type u) y).map b.hom) : a = b := by
  apply Sheaf.hom_ext
  ext ⟨U⟩ s
  apply TopCat.Presheaf.section_ext G U
  intro y hy
  have h' := congrArg (fun q => q ((H.presheaf.germ U y hy) s)) (h y)
  rwa [TopCat.Presheaf.stalkFunctor_map_germ_apply U y hy a.hom s,
    TopCat.Presheaf.stalkFunctor_map_germ_apply U y hy b.hom s] at h'

/-- The map to the product of the skyscrapers at a family of points. -/
private noncomputable def indexedPointMap {I : Type v} [Fintype I]
    (G : TopCat.Sheaf (Type u) (TopCat.of Y)) (points : I → Y)
    [∀ (y : Y) (U : Opens Y), Decidable (y ∈ U)] :
    G ⟶ ∏ᶜ fun i => skyscraperSheaf (X := TopCat.of Y) (points i)
      (G.presheaf.stalk (points i)) :=
  Pi.lift (fun i => pointMap G (points i))

/-- If the family of points is surjective, the map to the product of the skyscrapers is a
monomorphism, because a morphism of sheaves is determined by its maps on stalks. -/
private theorem indexedPointMap_mono {I : Type v} [Fintype I]
    (G : TopCat.Sheaf (Type u) (TopCat.of Y)) (points : I → Y)
    [∀ (y : Y) (U : Opens Y), Decidable (y ∈ U)]
    (hpoints : Function.Surjective points) : Mono (indexedPointMap G points) := by
  refine ⟨fun {H} a b hab =>
    eq_of_stalkMaps_eq G H a b (pointMap_reflects_stalks G H a b fun y => ?_)⟩
  obtain ⟨i, rfl⟩ := hpoints y
  simpa only [indexedPointMap, Category.assoc, Pi.lift_comp_π] using congrArg (fun q => q ≫ Pi.π
    (fun i : I => skyscraperSheaf (X := TopCat.of Y) (points i) (G.presheaf.stalk (points i))) i)
    hab

end Skyscrapers

/-! ### Pullback of sheaves of sets along a continuous map -/

/-- Pullback of sheaves of sets preserves finite limits. -/
theorem pullbackPreservesFiniteLimits {A B : TopCat.{u}} (f : A ⟶ B) :
    PreservesFiniteLimits (TopCat.Sheaf.pullback (Type u) f) := by
  let _ : PreservesFiniteLimits
      ((Opens.map f).op.lan : ((Opens B)ᵒᵖ ⥤ Type u) ⥤ (Opens A)ᵒᵖ ⥤ Type u) := inferInstance
  show PreservesFiniteLimits ((Opens.map f).sheafPullback (Type u)
    (Opens.grothendieckTopology B) (Opens.grothendieckTopology A))
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _

/-- Pullback of sheaves of sets commutes with finite products. -/
private noncomputable def pullbackProductIso {A B : TopCat.{u}} (f : A ⟶ B)
    (n : ℕ) (K : Fin n → TopCat.Sheaf (Type u) B) :
    (TopCat.Sheaf.pullback (Type u) f).obj (∏ᶜ K) ≅
      ∏ᶜ fun i => (TopCat.Sheaf.pullback (Type u) f).obj (K i) := by
  let := pullbackPreservesFiniteLimits f
  have : PreservesLimitsOfShape (Discrete (Fin n))
      (TopCat.Sheaf.pullback (Type u) f) := PreservesFiniteProducts.preserves n
  exact PreservesProduct.iso (TopCat.Sheaf.pullback (Type u) f) K

/-! ### Comparing a skyscraper with the pushforward of a constant sheaf -/

/-- The stalks of a constant sheaf are its value. -/
private noncomputable def constantSheaf_stalkIso {A : TopCat.{u}} (S : Type u) (x : A) :
    TopCat.Presheaf.stalk (constantSheafOnSpace A (Type u) S).obj x ≅ S := by
  let P := constantPresheafOnSpace A (Type u) S
  have hUnit : IsIso ((TopCat.Presheaf.stalkFunctor (C := Type u) (X := A) x).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology A) P)) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x (Type u) P
  exact (asIso ((TopCat.Presheaf.stalkFunctor (C := Type u) (X := A) x).map
    (CategoryTheory.toSheafify (Opens.grothendieckTopology A) P))).symm ≪≫
      (Equiv.ofBijective (alphaX A S x) (alphaX_bijective A S x)).symm.toIso

/-- The canonical section with value `s` of the pushforward of a constant sheaf, over any open
of the target. -/
private noncomputable def constantSection {A B : TopCat.{u}} (g : A ⟶ B) (S : Type u)
    (U : (Opens B)ᵒᵖ) : S ⟶
      ((TopCat.Sheaf.pushforward (Type u) g).obj
        (constantSheafOnSpace A (Type u) S)).presheaf.obj U := by
  let q := (CategoryTheory.toSheafify (Opens.grothendieckTopology A)
    (constantPresheafOnSpace A (Type u) S)).app (op ((Opens.map g).obj (unop U)))
  simpa [constantPresheafOnSpace, constantSheafOnSpace,
    TopCat.Sheaf.pushforward, Functor.sheafPushforwardContinuous,
    TopCat.Presheaf.pushforward] using q

/-- The canonical sections of the pushforward of a constant sheaf are compatible with
restriction. -/
private theorem constantSection_naturality {A B : TopCat.{u}} (g : A ⟶ B) (S : Type u)
    {U V : (Opens B)ᵒᵖ} (i : U ⟶ V) :
    constantSection g S U ≫
      ((TopCat.Sheaf.pushforward (Type u) g).obj
        (constantSheafOnSpace A (Type u) S)).presheaf.map i = constantSection g S V := by
  unfold constantSection
  simp only [constantPresheafOnSpace, constantSheafOnSpace,
    TopCat.Sheaf.pushforward, Functor.sheafPushforwardContinuous]
  let j := ((Opens.map g).map i.unop).op
  simpa [j] using ((CategoryTheory.toSheafify (Opens.grothendieckTopology A)
    ((Functor.const (Opens A)ᵒᵖ).obj S)).naturality j).symm

/-- If every point of the source specialises to `y`, the pushforward of a constant sheaf has a
terminal value on every open missing `y`. -/
private noncomputable def pushforwardConstant_isTerminal_of_not_mem
    {A B : TopCat.{u}} (g : A ⟶ B) (y : B) (S : Type u)
    (hg : ∀ z : A, g z ∈ closure ({y} : Set B))
    (U : Opens B) (hy : y ∉ U) :
    IsTerminal (((TopCat.Sheaf.pushforward (Type u) g).obj
      (constantSheafOnSpace A (Type u) S)).presheaf.obj (op U)) := by
  have heq : (Opens.map g).obj U = ⊥ := by
    apply Opens.ext
    ext z
    exact ⟨fun hz => (hy ((specializes_iff_mem_closure.mpr (hg z)).mem_open U.2 hz)).elim,
      by simp⟩
  have ht : IsTerminal ((constantSheafOnSpace A (Type u) S).obj.obj (op (⊥ : Opens A))) :=
    Sheaf.isTerminalOfBotCover (constantSheafOnSpace A (Type u) S)
      (⊥ : Opens A) (by intro z hz; simp at hz)
  simpa [TopCat.Sheaf.pushforward, Functor.sheafPushforwardContinuous,
    TopCat.Presheaf.pushforward, heq] using ht

section SkyscraperToConstant

variable {A B : TopCat.{u}} (g : A ⟶ B) (y : B) [∀ U : Opens B, Decidable (y ∈ U)]

/-- The underlying map of presheaves of `Stacks.skyscraperToConstantPushforward`. -/
private noncomputable def skyscraperToConstantPushforwardPresheaf (S : Type u)
    (hg : ∀ z : A, g z ∈ closure ({y} : Set B)) :
    skyscraperPresheaf (C := Type u) y S ⟶
      (TopCat.Sheaf.pushforward (Type u) g |>.obj
        (constantSheafOnSpace A (Type u) S)).presheaf := by
  refine { app := fun U => ?_, naturality := ?_ }
  · exact if hy : y ∈ unop U then
      eqToHom (ite_eq_left hy) ≫ constantSection g S U
    else by
      have ht' : IsTerminal
          (((TopCat.Sheaf.pushforward (Type u) g).obj
            (constantSheafOnSpace A (Type u) S)).presheaf.obj U) :=
        pushforwardConstant_isTerminal_of_not_mem g y S hg (unop U) hy
      exact ht'.from _
  · intro U V i
    by_cases hyV : y ∈ unop V
    · have hyU : y ∈ unop U := i.unop.le hyV
      have hcast :
          (skyscraperPresheaf (C := Type u) y S).map i ≫
            (eqToHom (ite_eq_left hyV) :
              (if y ∈ unop V then S else terminal (Type u)) ⟶ S) =
            (eqToHom (ite_eq_left hyU) :
              (if y ∈ unop U then S else terminal (Type u)) ⟶ S) := by
        simp only [skyscraperPresheaf_map, hyV]
        refine eqToHom_trans ?_ ?_
        all_goals simp [hyU, hyV]
      simp only [dite_eq_left hyU, dite_eq_left hyV, Category.assoc]
      calc
        _ = (eqToHom (ite_eq_left hyU) :
              (if y ∈ unop U then S else terminal (Type u)) ⟶ S) ≫ constantSection g S V := by
              rw [← Category.assoc]
              exact congrArg (fun q => q ≫ constantSection g S V) hcast
        _ = _ := by
          rw [← Category.assoc]
          exact congrArg (fun q => (eqToHom (ite_eq_left hyU) :
            (if y ∈ unop U then S else terminal (Type u)) ⟶ S) ≫ q)
            (constantSection_naturality g S i).symm
    · exact (pushforwardConstant_isTerminal_of_not_mem g y S hg (unop V) hyV).hom_ext _ _

/-- The canonical map from the skyscraper at `y` with value `S` to the pushforward of the
constant sheaf `S`, along a map all of whose values specialise to `y`. -/
private noncomputable def skyscraperToConstantPushforward (S : Type u)
    (hg : ∀ z : A, g z ∈ closure ({y} : Set B)) :
    skyscraperSheaf (C := Type u) y S ⟶
      (TopCat.Sheaf.pushforward (Type u) g).obj (constantSheafOnSpace A (Type u) S) :=
  ObjectProperty.homMk (skyscraperToConstantPushforwardPresheaf g y S hg)

/-- On global sections, `Stacks.skyscraperToConstantPushforward` is the canonical constant
section. -/
private theorem skyscraperToConstantPushforward_top (S : Type u)
    (hg : ∀ z : A, g z ∈ closure ({y} : Set B)) :
    (skyscraperToConstantPushforward g y S hg).hom.app (op ⊤) =
      eqToHom (by simp) ≫ constantSection g S (op ⊤) := by
  show (skyscraperToConstantPushforwardPresheaf g y S hg).app (op ⊤) = _
  simp only [skyscraperToConstantPushforwardPresheaf, unop_op,
    dite_eq_left (show y ∈ (⊤ : Opens B) from trivial)]
  rfl

end SkyscraperToConstant

section PullbackSkyscraper

variable {A B : TopCat.{u}} (f : A ⟶ B) (Z : Set A) (y : B)
  [∀ U : Opens B, Decidable (y ∈ U)]

/-- The transpose along the pullback–pushforward adjunction of
`Stacks.skyscraperToConstantPushforward`: the comparison between the pullback of the
skyscraper at `y` and the pushforward of the constant sheaf from a subspace `Z` all of whose
points map into the closure of `y`. -/
private noncomputable def pullbackSkyscraperToConstantPushforward (S : Type u)
    (hZ : ∀ z : Z, f z ∈ closure ({y} : Set B)) :
    (TopCat.Sheaf.pullback (Type u) f).obj (skyscraperSheaf (C := Type u) y S) ⟶
      (TopCat.Sheaf.pushforward (Type u)
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of Z ⟶ A)).obj
        (constantSheafOnSpace (TopCat.of Z) (Type u) S) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).homEquiv _ _).symm
    (skyscraperToConstantPushforward
      ((TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of Z ⟶ A) ≫ f) y S hZ)

/-- The transpose of `Stacks.skyscraperToConstantPushforward` recovers it after composing with
the unit of the adjunction. -/
private theorem skyscraperToConstantPushforward_unit_comp (S : Type u)
    (hZ : ∀ z : Z, f z ∈ closure ({y} : Set B)) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app
      (skyscraperSheaf (C := Type u) y S) ≫
      (TopCat.Sheaf.pushforward (Type u) f).map
        (pullbackSkyscraperToConstantPushforward f Z y S hZ) =
    skyscraperToConstantPushforward
      ((TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of Z ⟶ A) ≫ f)
      y S hZ := by
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f
  let j : TopCat.of Z ⟶ A :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let K := (TopCat.Sheaf.pushforward (Type u) j).obj
    (constantSheafOnSpace (TopCat.of Z) (Type u) S)
  let q : skyscraperSheaf (C := Type u) y S ⟶
      (TopCat.Sheaf.pushforward (Type u) f).obj K :=
    skyscraperToConstantPushforward (j ≫ f) y S hZ
  exact (adj.homEquiv_unit (skyscraperSheaf (C := Type u) y S) K
    (pullbackSkyscraperToConstantPushforward f Z y S hZ)).symm.trans
      ((adj.homEquiv (skyscraperSheaf (C := Type u) y S) K).apply_symm_apply q)

end PullbackSkyscraper

/-- At a point of `Z`, the stalk of the pushforward of a constant sheaf from `Z` is its
value. -/
private noncomputable def constantSheafPushforward_stalkIso_mem
    (A : TopCat.{u}) (Z : Set A) (S : Type u) (x : Z) :
    (constantSheafPushforward (X := A) Z S).presheaf.stalk (x : A) ≅ S := by
  let i : TopCat.of Z ⟶ A :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let C := constantSheafOnSpace (TopCat.of Z) (Type u) S
  let m : (constantSheafPushforward (X := A) Z S).presheaf.stalk (x : A) ⟶
      TopCat.Presheaf.stalk C.obj x :=
    TopCat.Presheaf.stalkPushforward (Type u) i C.obj x
  have : IsIso m :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      (C := Type u) (f := i) Topology.IsInducing.subtypeVal C.obj x
  exact asIso m ≪≫ constantSheaf_stalkIso (A := TopCat.of Z) S x

/-- Every germ at a point of `Z` of the pushforward of the constant sheaf `S` from `Z` comes
from a global constant section. -/
private theorem constantSheafPushforward_germ_top_surjective (A : TopCat.{u})
    (Z : Set A) (S : Type u) (x : Z) :
    Function.Surjective (fun s : S =>
      (constantSheafPushforward (X := A) Z S).presheaf.germ ⊤ (x : A) trivial
        ((CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of Z))
          (constantPresheafOnSpace (TopCat.of Z) (Type u) S)).app (op ⊤) s)) := by
  intro t
  let j : TopCat.of Z ⟶ A := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let P := constantPresheafOnSpace (TopCat.of Z) (Type u) S
  let u := CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of Z)) P
  let e := constantSheafPushforward_stalkIso_mem A Z S x
  refine ⟨e.hom t, e.toEquiv.injective ?_⟩
  have h1 := TopCat.Presheaf.stalkPushforward_germ_apply (Type u) j
    (constantSheafOnSpace (TopCat.of Z) (Type u) S).obj ⊤ x trivial (u.app (op ⊤) (e.hom t))
  have h2 := TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ x trivial u (e.hom t)
  refine (congrArg (constantSheaf_stalkIso (A := TopCat.of Z) S x).hom (h1.trans h2.symm)).trans ?_
  exact (constantSheaf_stalkIso (A := TopCat.of Z) S x).inv_hom_id_apply _

section PullbackSkyscraperStalk

variable {A B : TopCat.{u}} (f : A ⟶ B) (Z : Set A) (y : B)
  [∀ U : Opens B, Decidable (y ∈ U)]

/-- The transpose sends the global section of the pullback of the skyscraper coming from `s` to
the constant global section `s`. -/
private theorem pullbackSkyscraperToConstantPushforward_global_section (S : Type u)
    (hZ : ∀ z : Z, f z ∈ closure ({y} : Set B)) (s : S) :
    (pullbackSkyscraperToConstantPushforward f Z y S hZ).hom.app (op ⊤)
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app
        (skyscraperSheaf (C := Type u) y S)).hom.app (op ⊤)
          ((eqToHom (by simp) :
            S ⟶ (skyscraperSheaf (C := Type u) y S).presheaf.obj (op ⊤)) s)) =
      (CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of Z))
        (constantPresheafOnSpace (TopCat.of Z) (Type u) S)).app (op ⊤) s := by
  let g : TopCat.of Z ⟶ B :=
    (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of Z ⟶ A) ≫ f
  let d : (skyscraperSheaf (C := Type u) y S).presheaf.obj (op ⊤) ⟶ S := eqToHom (by simp)
  let e : S ⟶ (skyscraperSheaf (C := Type u) y S).presheaf.obj (op ⊤) := eqToHom (by simp)
  have hedge : e ≫ d = 𝟙 S := by
    dsimp [e, d]
    rw [eqToHom_trans]
    exact eqToHom_refl S _
  have h := congrArg (fun q => q.hom.app (op ⊤))
    (skyscraperToConstantPushforward_unit_comp f Z y S hZ)
  have h' : ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app
      (skyscraperSheaf (C := Type u) y S)).hom.app (op ⊤) ≫
      (pullbackSkyscraperToConstantPushforward f Z y S hZ).hom.app (op ⊤) =
      (skyscraperToConstantPushforward g y S hZ).hom.app (op ⊤) := by
    convert h using 1
    rfl
  have h := congrArg (fun q => q (e s)) h'
  have hTop : (skyscraperToConstantPushforward g y S hZ).hom.app (op ⊤) =
      d ≫ constantSection g S (op ⊤) := by
    simpa [d] using skyscraperToConstantPushforward_top g y S hZ
  have hleft : (d ≫ constantSection g S (op ⊤)) (e s) =
      (constantSection g S (op ⊤)) s := by
    show (e ≫ d ≫ constantSection g S (op ⊤)) s = _
    rw [← Category.assoc, hedge, Category.id_comp]
  have hconst : (constantSection g S (op ⊤)) s =
      (CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of Z))
        (constantPresheafOnSpace (TopCat.of Z) (Type u) S)).app (op ⊤) s := by
    simp only [constantSection, g]
    rfl
  exact ((h.trans (congrArg (fun q => q (e s)) hTop)).trans hleft).trans hconst

/-- At a point of `Z`, the transpose is surjective on stalks. -/
private theorem pullbackSkyscraperToConstantPushforward_stalk_surjective_mem (S : Type u)
    (hZ : ∀ z : Z, f z ∈ closure ({y} : Set B)) (x : Z) :
    Function.Surjective ((TopCat.Presheaf.stalkFunctor (Type u) (x : A)).map
      (pullbackSkyscraperToConstantPushforward f Z y S hZ).hom) := by
  intro t
  obtain ⟨s, hs⟩ := constantSheafPushforward_germ_top_surjective A Z S x t
  let e : S ⟶ (skyscraperSheaf (C := Type u) y S).presheaf.obj (op ⊤) := eqToHom (by simp)
  let v := ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app
    (skyscraperSheaf (C := Type u) y S)).hom.app (op ⊤) (e s)
  refine ⟨((TopCat.Sheaf.pullback (Type u) f).obj
    (skyscraperSheaf (C := Type u) y S)).presheaf.germ ⊤ (x : A) trivial v, ?_⟩
  have hmap := TopCat.Presheaf.stalkFunctor_map_germ_apply
    ⊤ (x : A) trivial (pullbackSkyscraperToConstantPushforward f Z y S hZ).hom v
  exact hmap.trans ((congrArg (fun q => (constantSheafPushforward (X := A) Z S).presheaf.germ
    ⊤ (x : A) trivial q)
      (pullbackSkyscraperToConstantPushforward_global_section f Z y S hZ s)).trans hs)

/-- For `S` finite and `Z` the whole preimage of the closure of `y`, the transpose is a
monomorphism: on stalks it is a surjection between finite sets at points of `Z`, and both
stalks are subsingletons elsewhere. -/
private theorem pullbackSkyscraperToConstantPushforward_mono (S : Type u)
    [Finite S] (hZ : ∀ z : Z, f z ∈ closure ({y} : Set B))
    (hEq : Z = f ⁻¹' closure ({y} : Set B)) :
    Mono (pullbackSkyscraperToConstantPushforward f Z y S hZ) := by
  rw [Stacks.Topology.SheafStalk.mono_iff_stalk_injective]
  intro x
  by_cases hx : x ∈ Z
  · let z : Z := ⟨x, hx⟩
    let eSrc : ((TopCat.Sheaf.pullback (Type u) f).obj
      (skyscraperSheaf (C := Type u) y S)).presheaf.stalk x ≅ S :=
      stalkPullbackSheafIso f (skyscraperSheaf (C := Type u) y S) x ≪≫
        skyscraperPresheafStalkOfSpecializes (C := Type u) y S
          (specializes_iff_mem_closure.mpr (hZ z))
    let eTgt : (constantSheafPushforward (X := A) Z S).presheaf.stalk x ≅ S :=
      constantSheafPushforward_stalkIso_mem A Z S z
    let : Finite (((TopCat.Sheaf.pullback (Type u) f).obj
      (skyscraperSheaf (C := Type u) y S)).presheaf.stalk x) :=
      Finite.of_equiv S eSrc.symm.toEquiv
    exact (Finite.injective_iff_surjective_of_equiv
      (eSrc.toEquiv.trans eTgt.symm.toEquiv)).mpr
        (pullbackSkyscraperToConstantPushforward_stalk_surjective_mem f Z y S hZ z)
  · let e := stalkPullbackSheafIso f (skyscraperSheaf (C := Type u) y S) x ≪≫
      skyscraperPresheafStalkOfNotSpecializes (C := Type u) y S
        (fun hs => (by simpa [hEq] using hx : f x ∉ closure ({y} : Set B))
          (specializes_iff_mem_closure.mp hs)) ≪≫
      CategoryTheory.Limits.Types.terminalIso
    intro a b _
    exact e.toEquiv.injective (Subsingleton.elim (e.hom a) (e.hom b))

end PullbackSkyscraperStalk

/-! ### The embedding -/

/-- **Stacks Project, Tag 0CAL.** A constructible sheaf of sets on a spectral space — one with
a finite presentation by finite constant sheaves extended from quasi-compact opens — is
isomorphic to a subsheaf of a finite product of pushforwards of finite constant sheaves from
closed constructible subspaces. -/
@[stacks 0CAL]
theorem exists_mono_to_pi_constantSheafPushforward [SpectralSpace X]
    (F : TopCat.Sheaf (Type u) (TopCat.of X))
    (hF : HasFiniteBasisCoequalizerPresentation
      { U : Opens X | IsCompact (U : Set X) } F) :
    ∃ (n : ℕ) (Z : Fin n → Set X),
      (∀ i, IsClosed (Z i)) ∧ (∀ i, Topology.IsConstructible (Z i)) ∧
        ∃ (S : Fin n → Type u) (_ : ∀ i, Finite (S i))
          (f : F ⟶ ∏ᶜ fun i ↦ constantSheafPushforward (Z i) (S i)), Mono f := by
  classical
  obtain ⟨Y, tY, finiteY, soberY, t0Y, g, G, hg, hG, ⟨e⟩⟩ :=
    exists_pullback_from_finite_sober_of_hasFiniteBasisCoequalizerPresentation F hF
  let : TopologicalSpace Y := tY
  let : Finite Y := finiteY
  let : QuasiSober Y := soberY
  let : T0Space Y := t0Y
  let : Fintype Y := Fintype.ofFinite Y
  let : ∀ (z : Y) (U : Opens Y), Decidable (z ∈ U) := fun _ _ => Classical.dec _
  let n : ℕ := Fintype.card Y
  let points : Fin n ≃ Y := (Fintype.equivFin Y).symm
  let Z : Fin n → Set X := fun i => g ⁻¹' closure ({points i} : Set Y)
  refine ⟨n, Z, (fun i => isClosed_closure.preimage hg.continuous),
    (fun i => isConstructible_preimage_closed_of_finite g hg isClosed_closure),
    (fun i => G.presheaf.stalk (points i)), (fun i => hG (points i)), ?_⟩
  let S : Fin n → Type u := fun i => G.presheaf.stalk (points i)
  let : ∀ i, Finite (S i) := fun i => hG (points i)
  let K : Fin n → TopCat.Sheaf (Type u) (TopCat.of Y) :=
    fun i => skyscraperSheaf (X := TopCat.of Y) (points i) (S i)
  let p : G ⟶ ∏ᶜ K := indexedPointMap G points
  have : Mono p := indexedPointMap_mono G points points.surjective
  let a := (TopCat.Sheaf.pullback (Type u) g).map p
  let := pullbackPreservesFiniteLimits g
  have : Mono a := Functor.map_mono _ p
  let r := pullbackProductIso g n K
  let c : ∀ i, (TopCat.Sheaf.pullback (Type u) g).obj (K i) ⟶
      constantSheafPushforward (Z i) (S i) := fun i =>
    pullbackSkyscraperToConstantPushforward g (Z i) (points i) (S i)
      (fun z => z.property)
  have : ∀ i, Mono (c i) := fun i =>
    pullbackSkyscraperToConstantPushforward_mono g (Z i) (points i) (S i)
      (fun z => z.property) rfl
  exact ⟨e.inv ≫ a ≫ r.hom ≫ CategoryTheory.Limits.Pi.map c, inferInstance⟩

end Stacks
