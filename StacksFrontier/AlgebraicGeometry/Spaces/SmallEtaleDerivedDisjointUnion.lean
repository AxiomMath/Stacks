module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Pi.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.ComplexesWithSupport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact
public import StacksFrontier.CategoryTheory.Sites.DisjointCoverSections
public import StacksFrontier.Algebra.Homology.DerivedCategory.PiEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherentCohomologyUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceFinitePart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDenseAffineFamily
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FromLocalAtSource

/-!
# Modules and derived categories on a disjoint union of algebraic spaces

Let `V` be an algebraic space over a scheme `W₀` of the site which is the disjoint union of
schemes `W_k` of the site, and let `V_k = V ×_{W₀} W_k` be the pieces, with the inclusions
`j_k : V_k ⟶ V`. The `V_k` are open and closed in `V`, pairwise disjoint and cover `V`, so the
small étale site of `V` splits: restriction identifies `𝒪_V`-modules with families of
`𝒪_{V_k}`-modules, and the derived category `D(𝒪_V)` with `∏_k D(𝒪_{V_k})`. In particular
`Hom_{D(𝒪_V)}(K, E) = ∏_k Hom_{D(𝒪_{V_k})}(K|_{V_k}, E|_{V_k})` for all `K`, `E`. The source
(the proof of Stacks 0DLC) uses this without comment, to read a family of morphisms on the members
of an fppf covering as one morphism on their disjoint union.

The proof runs through a general recognition principle for product decompositions. For an étale
representable monomorphism `j : V' ⟶ V`, restriction of modules `j^*` is left adjoint to the
direct image `j_*`, which is restriction of sections along base change of charts
(`AlgebraicGeometry.Space.etaleModulePullbackSmallBaseChangeAdjunction`). Then:

* every `𝒪_V`-module `M` is the product of the `j_{k*}j_k^*M` through the units, because the
  base changes `U ×_V V_k ⟶ U` of a chart `U` form a disjoint covering family of monomorphisms, and
  the sections of a sheaf over such a family form a product
  (`CategoryTheory.Presheaf.IsSheaf.isLimitFanSectionsOfDisjointArrows`);
* `j_i^*j_{k*}` is zero for `i ≠ k`, its sections living over empty charts;
* the counits `j_k^*j_{k*} ⟶ 𝟭` are isomorphisms, `j_k` being a monomorphism;
* the `j_k^*` preserve products.

These four conditions make `Functor.pi' j^* : Mod(𝒪_V) ⥤ ∏_k Mod(𝒪_{V_k})` an equivalence
(`CategoryTheory.Functor.isEquivalence_pi'_of_isLimit_unit`), and an equivalence onto a product
by exact functors passes to derived categories
(`CategoryTheory.Functor.isEquivalence_pi'_mapDerivedCategory`).

## Main results

* `CategoryTheory.Functor.isEquivalence_pi'_of_isLimit_unit`: the recognition principle for a
  product decomposition through a family of adjunctions.
* `SheafOfModules.isLimitFanUnitPushforwardPushforwardAdj`: a sheaf of modules is the product of
  its restrictions to the pieces of a disjoint decomposition of the site.
* `AlgebraicGeometry.Space.isEquivalence_pi'_etaleModulePullback`: modules on `V` are families of
  modules on the `V' k`, for a disjoint covering family of étale representable monomorphisms.
* `AlgebraicGeometry.Space.isEquivalence_pi'_etaleModulePullback_of_isPullback_cofan`: the same
  for the pieces of an algebraic space over a disjoint union of schemes.
* `Space.bijective_mapDerivedCategory_etaleModulePullback_map_of_isPullback_cofan` says
  `Hom_{D(𝒪_V)}(K, E) = ∏_k Hom_{D(𝒪_{V_k})}(K|_{V_k}, E|_{V_k})`, in any model of the derived
  categories.

## Implementation notes

The hypotheses of the general statements are phrased through the adjunction of postcomposition
and base change of étale charts, `AlgebraicGeometry.Space.smallEtalePostcompBaseChangeAdjunction`,
so that the units and counits of the adjoint module functors are, on sections, restriction maps by
definition (`SheafOfModules.pushforwardPushforwardAdj_unit_app_val_app`); the product and
vanishing statements are therefore proved for an arbitrary pair of adjoint functors of sites and
only instantiated here. The derived statements quantify over arbitrary models of the derived
categories; the identification of the derived pullback with the exact restriction, which is
stated for the standard model, is made at the use site.

## References

* [Stacks Project, Tag 0DLC](https://stacks.math.columbia.edu/tag/0DLC)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v v₁ v₂ u u₁ u₂

namespace CategoryTheory.Functor

section PiOfUnitFan

variable {A : Type u₁} [Category.{v₁} A] {ι : Type w} {C : ι → Type u₂}
  [∀ i, Category.{v₂} (C i)] {L : ∀ i, A ⥤ C i} {R : ∀ i, C i ⥤ A} (adj : ∀ i, L i ⊣ R i)

/-- **A family of left adjoints whose units exhibit every object as a product is jointly fully
faithful.** If `L i ⊣ R i` and every `M` is the product of the `R i (L i M)` through the units,
then `Functor.pi' L : A ⥤ ∀ i, C i` is fully faithful. -/
def fullyFaithfulPi'OfIsLimitUnit
    (h : ∀ M : A, IsLimit (Fan.mk M fun i => (adj i).unit.app M)) :
    (Functor.pi' L).FullyFaithful where
  preimage {X Y} f := (h Y).lift (Fan.mk X fun i => (adj i).homEquiv _ _ (f i))
  map_preimage {X Y} f := by
    funext i
    apply ((adj i).homEquiv _ _).injective
    change (adj i).homEquiv X ((L i).obj Y)
      ((L i).map ((h Y).lift (Fan.mk X fun i => (adj i).homEquiv _ _ (f i)))) = _
    rw [Adjunction.homEquiv_unit, Adjunction.unit_naturality]
    exact (h Y).fac (Fan.mk X fun i => (adj i).homEquiv _ _ (f i)) ⟨i⟩
  preimage_map {X Y} g := by
    refine ((h Y).uniq (Fan.mk X fun i => (adj i).homEquiv _ _ ((L i).map g)) g ?_).symm
    rintro ⟨i⟩
    change g ≫ (adj i).unit.app Y = (adj i).homEquiv _ _ ((L i).map g)
    rw [Adjunction.homEquiv_unit, Adjunction.unit_naturality]

end PiOfUnitFan

end CategoryTheory.Functor

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C] {ι : Type w} {f : ι → C}

/-- **The projection of a product all of whose other factors are zero is an isomorphism.** -/
theorem isIso_proj_of_isZero {c : Fan f} (hc : IsLimit c) (i : ι)
    (hz : ∀ j, j ≠ i → IsZero (f j)) : IsIso (c.proj i) := by
  classical
  let s : Fan f := Fan.mk (f i) fun j =>
    if h : j = i then eqToHom (congrArg f h.symm) else 0
  have hs : hc.lift s ≫ c.proj i = 𝟙 _ := (hc.fac s ⟨i⟩).trans (by simp [s])
  refine ⟨hc.lift s, Fan.IsLimit.hom_ext hc _ _ fun j => ?_, hs⟩
  by_cases hji : j = i
  · subst hji
    rw [Category.assoc, hs]
    exact (Category.comp_id (c.proj j)).trans (Category.id_comp (c.proj j)).symm
  · exact (hz j hji).eq_of_tgt _ _

end CategoryTheory.Limits

namespace CategoryTheory.Functor

section PiOfUnitFan

variable {A : Type u₁} [Category.{v₁} A] {ι : Type w} {C : ι → Type u₂}
  [∀ i, Category.{v₂} (C i)] {L : ∀ i, A ⥤ C i} {R : ∀ i, C i ⥤ A} (adj : ∀ i, L i ⊣ R i)

/-- **A product decomposition from a family of adjunctions.** Let `L i ⊣ R i` be adjunctions
such that

* every `M` is the product of the `R i (L i M)` through the units,
* `L i (R j N)` is zero for `i ≠ j`,
* the counits are isomorphisms, and
* the `L i` preserve products indexed by `ι`.

Then `Functor.pi' L : A ⥤ ∀ i, C i` is an equivalence: its inverse sends a family `N` to the
product of the `R i (N i)`. -/
theorem isEquivalence_pi'_of_isLimit_unit [HasLimitsOfShape (Discrete ι) A]
    [∀ i, HasZeroMorphisms (C i)] [∀ i, PreservesLimitsOfShape (Discrete ι) (L i)]
    (h : ∀ M : A, IsLimit (Fan.mk M fun i => (adj i).unit.app M))
    (hz : ∀ i j, i ≠ j → ∀ N : C j, IsZero ((L i).obj ((R j).obj N)))
    [∀ i, IsIso (adj i).counit] :
    (Functor.pi' L).IsEquivalence := by
  have hff := fullyFaithfulPi'OfIsLimitUnit adj h
  have : (Functor.pi' L).Full := hff.full
  have : (Functor.pi' L).Faithful := hff.faithful
  refine { essSurj := ⟨fun N => ⟨∏ᶜ fun j => (R j).obj (N j), ⟨Pi.isoMk fun i => ?_⟩⟩⟩ }
  have hπ : IsIso ((L i).map (Pi.π (fun j => (R j).obj (N j)) i)) :=
    isIso_proj_of_isZero (isLimitOfHasProductOfPreservesLimit (L i) _) i
      (fun j hj => hz i j (Ne.symm hj) (N j))
  exact @asIso _ _ _ _ ((L i).map (Pi.π (fun j => (R j).obj (N j)) i)) hπ ≪≫
    asIso ((adj i).counit.app (N i))

end PiOfUnitFan

/-- If two families of functors `P k`, `Q k : A ⥤ B k` are isomorphic, then `φ ↦ (P k).map φ`
is jointly bijective as soon as `φ ↦ (Q k).map φ` is. -/
theorem bijective_pi_map_of_iso {A : Type u₁} [Category.{v₁} A] {ι : Type w} {C : ι → Type u₂}
    [∀ i, Category.{v₂} (C i)] {P Q : ∀ i, A ⥤ C i} (e : ∀ i, P i ≅ Q i) {X Y : A}
    (h : Function.Bijective fun φ : X ⟶ Y => fun i => (Q i).map φ) :
    Function.Bijective fun φ : X ⟶ Y => fun i => (P i).map φ := by
  have : (fun φ : X ⟶ Y => fun i => (P i).map φ) =
      (fun ψ : ∀ i, (Q i).obj X ⟶ (Q i).obj Y => fun i =>
        (e i).hom.app X ≫ ψ i ≫ (e i).inv.app Y) ∘ fun φ : X ⟶ Y => fun i => (Q i).map φ := by
    funext φ i
    simp
  rw [this]
  refine Function.Bijective.comp ⟨fun ψ ψ' hψ => funext fun i => ?_, fun χ =>
    ⟨fun i => (e i).inv.app X ≫ χ i ≫ (e i).hom.app Y, funext fun i => by simp⟩⟩ h
  simpa using congrFun hψ i

/-- **Derived categories of a product decomposition, on morphisms.** If exact functors `F i`
identify an abelian category `A` with `∏ i, B i`, then `Hom_{D(A)}(K, E)` is the product of the
`Hom_{D(B i)}(F i K, F i E)`. -/
theorem bijective_pi_mapDerivedCategory_map {A : Type u₁} [Category.{v₁} A] {ι : Type w}
    {C : ι → Type u₂} [∀ i, Category.{v₂} (C i)] (F : ∀ i, A ⥤ C i) [Abelian A]
    [∀ i, Abelian (C i)] [∀ i, (F i).Additive] [∀ i, PreservesFiniteLimits (F i)]
    [∀ i, PreservesFiniteColimits (F i)] [(Functor.pi' F).IsEquivalence] [HasDerivedCategory A]
    [∀ i, HasDerivedCategory (C i)] (K E : DerivedCategory A) :
    Function.Bijective fun φ : K ⟶ E => fun i => (F i).mapDerivedCategory.map φ :=
  (Functor.FullyFaithful.ofFullyFaithful
    (Functor.pi' fun i => (F i).mapDerivedCategory)).map_bijective K E

end CategoryTheory.Functor

namespace SheafOfModules

open Opposite

section Zero

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u₂}}

/-- A sheaf of modules all of whose groups of sections are zero is zero. -/
theorem isZero_of_isZero_presheaf_obj (M : SheafOfModules.{v₂} R)
    (h : ∀ U, IsZero (M.val.presheaf.obj U)) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  apply (SheafOfModules.toSheaf.{v₂} R ⋙ sheafToPresheaf J AddCommGrpCat.{v₂}).map_injective
  ext U : 2
  exact (h U).eq_of_src _ _

/-- The sections of a sheaf of modules over an object covered by the empty sieve are zero. -/
theorem isZero_presheaf_obj_of_bot_mem (M : SheafOfModules.{v₂} R) {U : C}
    (hU : (⊥ : Sieve U) ∈ J U) : IsZero (M.val.presheaf.obj (op U)) := by
  obtain ⟨_t, -, hu⟩ := M.isSheaf (M.val.presheaf.obj (op U)) ⊥ hU (fun _ _ hf ↦ hf.elim)
    (fun _ _ _ _ _ _ _ h₁ ↦ h₁.elim)
  exact (IsZero.iff_id_eq_zero _).2
    ((hu _ fun _ _ hf ↦ hf.elim).trans (hu _ fun _ _ hf ↦ hf.elim).symm)

/-- A pushforward of a pushforward of a sheaf of modules is zero when the composite functor of
sites lands in objects covered by the empty sieve. -/
theorem isZero_pushforward_pushforward_obj {C' : Type*} [Category* C']
    {J' : GrothendieckTopology C'}
    {D : Type*} [Category* D] {K : GrothendieckTopology D} {F : C' ⥤ D} {G : D ⥤ C}
    [Functor.IsContinuous F J' K] [Functor.IsContinuous G K J]
    {R' : Sheaf J' RingCat.{u₂}} {R'' : Sheaf K RingCat.{u₂}}
    (φ : R' ⟶ (F.sheafPushforwardContinuous RingCat.{u₂} J' K).obj R'')
    (ψ : R'' ⟶ (G.sheafPushforwardContinuous RingCat.{u₂} K J).obj R)
    (N : SheafOfModules.{v₂} R) (h : ∀ W, (⊥ : Sieve (G.obj (F.obj W))) ∈ J (G.obj (F.obj W))) :
    IsZero ((pushforward.{v₂} φ).obj ((pushforward.{v₂} ψ).obj N)) :=
  isZero_of_isZero_presheaf_obj _ fun W => isZero_presheaf_obj_of_bot_mem N (h W.unop)

end Zero

section Adjunction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D} {G : D ⥤ C}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K] [Functor.IsContinuous G K J] (adj : F ⊣ G)
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj S)
  (H₁ : Functor.whiskerRight (NatTrans.op adj.counit) R.obj = ψ.hom ≫ G.op.whiskerLeft φ.hom)
  (H₂ : φ.hom ≫ F.op.whiskerLeft ψ.hom ≫
    Functor.whiskerRight (NatTrans.op adj.unit) S.obj = 𝟙 S.obj)

/-- **The counit of the adjoint pushforwards is an isomorphism when the unit of the adjunction of
sites is.** -/
theorem isIso_pushforwardPushforwardAdj_counit [IsIso adj.unit] :
    IsIso (pushforwardPushforwardAdj.{v} adj φ ψ H₁ H₂).counit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf.{v} S),
    ← isIso_iff_of_reflects_iso _ (sheafToPresheaf J AddCommGrpCat.{v}),
    NatTrans.isIso_iff_isIso_app]
  intro U
  exact (inferInstance : IsIso (M.val.presheaf.map (adj.unit.app U.unop).op))

end Adjunction

section DisjointUnit

variable {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D} {R : Sheaf K RingCat.{u}}
  {ι : Type v} {C : ι → Type u₁} [∀ k, Category.{v₁} (C k)] {J : ∀ k, GrothendieckTopology (C k)}
  {S : ∀ k, Sheaf (J k) RingCat.{u}} {F : ∀ k, C k ⥤ D} {G : ∀ k, D ⥤ C k}
  [∀ k, Functor.IsContinuous (F k) (J k) K] [∀ k, Functor.IsContinuous (G k) K (J k)]
  (adj : ∀ k, F k ⊣ G k)
  (φ : ∀ k, S k ⟶ ((F k).sheafPushforwardContinuous RingCat.{u} (J k) K).obj R)
  (ψ : ∀ k, R ⟶ ((G k).sheafPushforwardContinuous RingCat.{u} K (J k)).obj (S k))
  (H₁ : ∀ k, Functor.whiskerRight (NatTrans.op (adj k).counit) R.obj =
    (ψ k).hom ≫ (G k).op.whiskerLeft (φ k).hom)
  (H₂ : ∀ k, (φ k).hom ≫ (F k).op.whiskerLeft (ψ k).hom ≫
    Functor.whiskerRight (NatTrans.op (adj k).unit) (S k).obj = 𝟙 (S k).obj)

/-- **A sheaf of modules is the product of its restrictions to the pieces of a disjoint
decomposition.** Let `F k ⊣ G k` be adjunctions of sites such that, for every `U`, the counits
`F k (G k U) ⟶ U` form a covering family of monomorphisms which is pairwise disjoint (an object
mapping to two distinct members over `U` is covered by the empty sieve). Then every sheaf of
modules `M` is the product of the `G_* F_* M` through the units of the adjoint pushforwards. -/
def isLimitFanUnitPushforwardPushforwardAdj (M : SheafOfModules.{v} R)
    (hcov : ∀ U, Sieve.ofArrows (fun k => (F k).obj ((G k).obj U)) (fun k => (adj k).counit.app U)
      ∈ K U)
    (hmono : ∀ U k, Mono ((adj k).counit.app U))
    (hdisj : ∀ U i k, i ≠ k → ∀ {Z : D} (gi : Z ⟶ (F i).obj ((G i).obj U))
      (gk : Z ⟶ (F k).obj ((G k).obj U)),
      gi ≫ (adj i).counit.app U = gk ≫ (adj k).counit.app U → (⊥ : Sieve Z) ∈ K Z) :
    IsLimit (Fan.mk M fun k =>
      (pushforwardPushforwardAdj.{v} (adj k) (φ k) (ψ k) (H₁ k) (H₂ k)).unit.app M) := by
  have : ReflectsLimitsOfShape (Discrete ι) (SheafOfModules.toSheaf.{v} R) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  have : HasProducts.{v} (Dᵒᵖ ⥤ AddCommGrpCat.{v}) := fun _ => functorCategoryHasLimitsOfShape
  have : HasLimitsOfShape (Discrete ι) (Sheaf K AddCommGrpCat.{v}) :=
    hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (sheafToPresheaf K AddCommGrpCat.{v})
  have : ReflectsLimitsOfShape (Discrete ι) (sheafToPresheaf K AddCommGrpCat.{v}) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  refine isLimitOfReflects (SheafOfModules.toSheaf.{v} R ⋙ sheafToPresheaf K AddCommGrpCat.{v}) ?_
  refine evaluationJointlyReflectsLimits _ fun U => ?_
  refine (isLimitMapConeFanMkEquiv ((SheafOfModules.toSheaf.{v} R ⋙
    sheafToPresheaf K AddCommGrpCat.{v}) ⋙
      (CategoryTheory.evaluation Dᵒᵖ AddCommGrpCat.{v}).obj U) _ _).symm ?_
  exact M.isSheaf.isLimitFanSectionsOfDisjointArrows (fun k => (adj k).counit.app U.unop)
    (hcov U.unop) (hmono U.unop) (hdisj U.unop)

end DisjointUnit

end SheafOfModules

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange
  etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Modules

variable {V : AlgebraicSpaces B S hS} {ι : Type u} {V' : ι → AlgebraicSpaces B S hS}
  (j : ∀ k, V' k ⟶ V) (hj : ∀ k, IsEtale B S hS (j k).hom)
  (hrep : ∀ k, yoneda.relativelyRepresentable (j k).hom)

/-- The unit `W ⟶ (j W) ×_V V'` of postcomposition and base change of étale charts along a
monomorphism `j : V' ⟶ V` is an isomorphism. -/
theorem isIso_smallEtalePostcompBaseChangeAdjunction_unit_app {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) (hrep : yoneda.relativelyRepresentable f.hom)
    [Mono f.hom] (c : SmallEtale B S hS X.1) :
    IsIso ((smallEtalePostcompBaseChangeAdjunction B S hS f hf hrep).unit.app c) := by
  have hs : Mono (hrep.snd ((smallEtalePostcomp B S hS f hf).obj c).1.hom) :=
    yoneda.mono_of_mono_map (hrep.isPullback _).mono_snd_of_mono
  have hu := smallEtalePostcompBaseChangeAdjunction_unit_left_comp_snd B S hS f hf hrep c
  have : IsSplitEpi (hrep.snd ((smallEtalePostcomp B S hS f hf).obj c).1.hom) := ⟨⟨⟨_, hu⟩⟩⟩
  have hsi : IsIso (hrep.snd ((smallEtalePostcomp B S hS f hf).obj c).1.hom) :=
    isIso_of_mono_of_isSplitEpi _
  have : IsIso ((smallEtalePostcompBaseChangeAdjunction B S hS f hf hrep).unit.app c).hom.left := by
    have hc : IsIso
        (((smallEtalePostcompBaseChangeAdjunction B S hS f hf hrep).unit.app c).hom.left ≫
          hrep.snd ((smallEtalePostcomp B S hS f hf).obj c).1.hom) := by
      rw [hu]
      exact IsIso.id _
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hsi hc
  have : IsIso ((SmallEtale.toOver B S hS X.1).map
      ((smallEtalePostcompBaseChangeAdjunction B S hS f hf hrep).unit.app c)) := this
  exact isIso_of_reflects_iso _ (SmallEtale.toOver B S hS X.1)

/-- The counit `(U ×_V V') ⟶ U` of postcomposition and base change of étale charts along a
monomorphism `j : V' ⟶ V` is a monomorphism. -/
theorem mono_smallEtalePostcompBaseChangeAdjunction_counit_app {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) (hrep : yoneda.relativelyRepresentable f.hom)
    [Mono f.hom] (U : SmallEtale B S hS Y.1) :
    Mono ((smallEtalePostcompBaseChangeAdjunction B S hS f hf hrep).counit.app U) := by
  have hs : Mono (hrep.snd U.1.hom) :=
    yoneda.mono_of_mono_map (hrep.isPullback U.1.hom).mono_snd_of_mono
  have : Mono ((SmallEtale.toOver B S hS Y.1).map
      ((smallEtalePostcompBaseChangeAdjunction B S hS f hf hrep).counit.app U)) := hs
  exact (SmallEtale.toOver B S hS Y.1).mono_of_mono_map this

/-- **Modules on a disjoint union of algebraic spaces.** Let `j k : V' k ⟶ V` be étale,
representable monomorphisms of algebraic spaces such that the base changes `U ×_V V' k ⟶ U`
cover every étale chart `U` of `V`, and such that no nonempty scheme maps to two distinct
`V' k` compatibly over `V`. Then restriction identifies `𝒪_V`-modules with families of
`𝒪_{V' k}`-modules. -/
theorem isEquivalence_pi'_etaleModulePullback [∀ k, Mono (j k).hom]
    (hcov : ∀ U : SmallEtale B S hS V.1,
      Sieve.ofArrows (fun k => (smallEtalePostcomp B S hS (j k) (hj k)).obj
          ((smallBaseChange B S hS (j k) (hrep k)).obj U))
        (fun k =>
          (smallEtalePostcompBaseChangeAdjunction B S hS (j k) (hj k) (hrep k)).counit.app U)
        ∈ SmallEtale.topology B S hS V.1 U)
    (hdisj : ∀ i k, i ≠ k → ∀ (Z : BigFppfOver B S hS) (a : yoneda.obj Z ⟶ (V' i).1)
      (b : yoneda.obj Z ⟶ (V' k).1), a ≫ (j i).hom = b ≫ (j k).hom →
        IsEmpty ((BigFppfOver.toScheme B S hS).obj Z)) :
    (Functor.pi' fun k => etaleModulePullback.{u, u} B S hS (j k) (hj k)).IsEquivalence := by
  have : ∀ k, PreservesLimitsOfShape (Discrete ι)
      (etaleModulePullback.{u, u} B S hS (j k) (hj k)) :=
    fun k => by
      rw [← etaleModulePullback_eq_pushforward]
      exact (SheafOfModules.preservesLimitsOfSize_pushforward
        (etaleRestrictionSharp B S hS (j k) (hj k))).preservesLimitsOfShape
  have : ∀ k,
      IsIso (etaleModulePullbackSmallBaseChangeAdjunction B S hS (j k) (hj k) (hrep k)).counit :=
    fun k => by
      have := fun c => isIso_smallEtalePostcompBaseChangeAdjunction_unit_app B S hS
        (j k) (hj k) (hrep k) c
      have : IsIso (smallEtalePostcompBaseChangeAdjunction B S hS (j k) (hj k) (hrep k)).unit :=
        NatIso.isIso_of_isIso_app _
      exact SheafOfModules.isIso_pushforwardPushforwardAdj_counit _ _ _ _ _
  refine Functor.isEquivalence_pi'_of_isLimit_unit
    (fun k => etaleModulePullbackSmallBaseChangeAdjunction B S hS (j k) (hj k) (hrep k))
    (fun M => SheafOfModules.isLimitFanUnitPushforwardPushforwardAdj
      (fun k => smallEtalePostcompBaseChangeAdjunction B S hS (j k) (hj k) (hrep k))
      (fun k => etaleRestrictionSharp B S hS (j k) (hj k))
      (fun k => smallBaseChangeSharp B S hS (j k) (hrep k))
      (fun k => smallBaseChangeSharp_counit B S hS (j k) (hj k) (hrep k))
      (fun k => smallBaseChangeSharp_unit B S hS (j k) (hj k) (hrep k)) M hcov
      (fun U k => mono_smallEtalePostcompBaseChangeAdjunction_counit_app B S hS _ _ _ U)
      (fun U i k hik Z gi gk _ => SmallEtale.bot_mem_topology B S hS V.1 Z
        (hdisj i k hik Z.1.left (yoneda.map gi.hom.left ≫
            ((smallBaseChange B S hS (j i) (hrep i)).obj U).1.hom)
          (yoneda.map gk.hom.left ≫ ((smallBaseChange B S hS (j k) (hrep k)).obj U).1.hom)
          ((Category.assoc _ _ _).trans ((CostructuredArrow.w gi.hom).trans
            ((CostructuredArrow.w gk.hom).symm.trans (Category.assoc _ _ _).symm))))))
    (fun i k hik N => by
      rw [← etaleModulePullback_eq_pushforward]
      exact SheafOfModules.isZero_pushforward_pushforward_obj
        (etaleRestrictionSharp B S hS (j i) (hj i)) (smallBaseChangeSharp B S hS (j k) (hrep k)) N
        fun W => SmallEtale.bot_mem_topology B S hS (V' k).1 _
          (hdisj k i (Ne.symm hik)
            ((smallBaseChange B S hS (j k) (hrep k)).obj
              ((smallEtalePostcomp B S hS (j i) (hj i)).obj W)).1.left
            ((smallBaseChange B S hS (j k) (hrep k)).obj
              ((smallEtalePostcomp B S hS (j i) (hj i)).obj W)).1.hom
            (yoneda.map ((hrep k).snd ((smallEtalePostcomp B S hS (j i) (hj i)).obj W).1.hom) ≫
              W.1.hom)
            (((hrep k).w _).trans (Category.assoc _ _ _).symm)))

/-- **Morphisms in the derived category of a disjoint union of algebraic spaces**, in any model
of the derived categories. Under the hypotheses of
`AlgebraicGeometry.Space.isEquivalence_pi'_etaleModulePullback`, for `K`, `E` in `D(𝒪_V)` the
map `Hom(K, E) ⟶ ∏_k Hom(j_k^*K, j_k^*E)` induced by the exact restrictions is bijective. -/
theorem bijective_mapDerivedCategory_etaleModulePullback_map [∀ k, Mono (j k).hom]
    (hcov : ∀ U : SmallEtale B S hS V.1,
      Sieve.ofArrows (fun k => (smallEtalePostcomp B S hS (j k) (hj k)).obj
          ((smallBaseChange B S hS (j k) (hrep k)).obj U))
        (fun k =>
          (smallEtalePostcompBaseChangeAdjunction B S hS (j k) (hj k) (hrep k)).counit.app U)
        ∈ SmallEtale.topology B S hS V.1 U)
    (hdisj : ∀ i k, i ≠ k → ∀ (Z : BigFppfOver B S hS) (a : yoneda.obj Z ⟶ (V' i).1)
      (b : yoneda.obj Z ⟶ (V' k).1), a ≫ (j i).hom = b ≫ (j k).hom →
        IsEmpty ((BigFppfOver.toScheme B S hS).obj Z))
    [HasDerivedCategory (Modules.{u, u} B S hS V.1 V.2)]
    [∀ k, HasDerivedCategory (Modules.{u, u} B S hS (V' k).1 (V' k).2)]
    (K E : DerivedCategory (Modules.{u, u} B S hS V.1 V.2)) :
    Function.Bijective fun φ : K ⟶ E => fun k =>
      (etaleModulePullback.{u, u} B S hS (j k) (hj k)).mapDerivedCategory.map φ := by
  have := isEquivalence_pi'_etaleModulePullback B S hS j hj hrep hcov hdisj
  exact Functor.bijective_pi_mapDerivedCategory_map _ K E

end Modules

/-! ### The pieces of an algebraic space over a disjoint union of schemes -/

section SchemeCoproduct

variable {B S hS} {ι : Type u} {W : ι → BigFppfOver B S hS} {W₀ : BigFppfOver B S hS}
  {w : ∀ k, W k ⟶ W₀}
  (hW : IsColimit (Cofan.mk ((BigFppfOver.toScheme B S hS).obj W₀)
    fun k => (BigFppfOver.toScheme B S hS).map (w k)))
  {V : AlgebraicSpaces B S hS} {p : V ⟶ (schemeSpaceFunctor B S hS).obj W₀}
  {V' : ι → AlgebraicSpaces B S hS} {j : ∀ k, V' k ⟶ V}
  {p' : ∀ k, V' k ⟶ (schemeSpaceFunctor B S hS).obj (W k)}
  (hsq : ∀ k, IsPullback (j k) (p' k) p ((schemeSpaceFunctor B S hS).map (w k)))

include hW hsq

/-- A piece `V_k = V ×_{W₀} W_k` of an algebraic space over a disjoint union of schemes is étale
over `V`. -/
theorem isEtale_hom_of_isPullback_cofan (k : ι) : IsEtale B S hS (j k).hom := by
  have := isOpenImmersion_of_isColimit_cofanMk hW k
  exact isEtale_of_isPullback_of_isAlgebraicSpace B S hS
    (AlgebraicSpaces.isPullback_hom B S hS (hsq k)) (V' k).2 V.2
    ((schemeSpaceFunctor B S hS).obj (W k)).2 ((schemeSpaceFunctor B S hS).obj W₀).2
    ((isEtale_iff_presheaf_of_yoneda B S hS _).2
      ((presheaf_yoneda_map_etale_iff B S hS (w k)).2 inferInstance))

omit hW in
/-- The inclusion of a piece `V_k = V ×_{W₀} W_k` of an algebraic space over a disjoint union of
schemes is representable. -/
theorem relativelyRepresentable_hom_of_isPullback_cofan (k : ι) :
    yoneda.relativelyRepresentable (j k).hom :=
  MorphismProperty.of_isPullback (AlgebraicSpaces.isPullback_hom B S hS (hsq k)).flip
    (Functor.relativelyRepresentable.map yoneda (w k))

/-- The inclusion of a piece `V_k = V ×_{W₀} W_k` of an algebraic space over a disjoint union of
schemes is a monomorphism. -/
theorem mono_hom_of_isPullback_cofan (k : ι) : Mono (j k).hom := by
  have := mono_of_isColimit_toScheme B S hS W W₀ w hW k
  exact (AlgebraicSpaces.isPullback_hom B S hS (hsq k)).mono_fst_of_mono
    (inferInstanceAs (Mono (yoneda.map (w k))))

/-- Two distinct pieces of an algebraic space over a disjoint union of schemes are disjoint: a
scheme mapping to both compatibly over `V` is empty. -/
theorem isEmpty_of_isPullback_cofan {i k : ι} (hik : i ≠ k) (Z : BigFppfOver B S hS)
    (a : yoneda.obj Z ⟶ (V' i).1) (b : yoneda.obj Z ⟶ (V' k).1)
    (hab : a ≫ (j i).hom = b ≫ (j k).hom) : IsEmpty ((BigFppfOver.toScheme B S hS).obj Z) := by
  have key : ∀ (k) (c : yoneda.obj Z ⟶ (V' k).1),
      yoneda.map (yoneda.preimage (c ≫ (p' k).hom) ≫ w k) = c ≫ (j k).hom ≫ p.hom := fun k c => by
    have hk : (j k).hom ≫ p.hom = (p' k).hom ≫ yoneda.map (w k) :=
      congrArg (fun f => f.hom) (hsq k).w
    rw [Functor.map_comp, Functor.map_preimage, hk]
    rfl
  have h := (key i a).trans ((congrArg (· ≫ p.hom) hab).trans (key k b).symm)
  exact isEmpty_of_commSq_of_isColimit_cofanMk hW hik
    (by rw [← Functor.map_comp, ← Functor.map_comp, yoneda.map_injective h])

/-- The base changes `U ×_V V_k ⟶ U` of an étale chart `U` of an algebraic space `V` over a
disjoint union of schemes to the pieces `V_k = V ×_{W₀} W_k` form a covering family of `U`. -/
theorem ofArrows_counit_mem_topology_of_isPullback_cofan (hj : ∀ k, IsEtale B S hS (j k).hom)
    (hrep : ∀ k, yoneda.relativelyRepresentable (j k).hom) (U : SmallEtale B S hS V.1) :
    Sieve.ofArrows (fun k => (smallEtalePostcomp B S hS (j k) (hj k)).obj
        ((smallBaseChange B S hS (j k) (hrep k)).obj U))
      (fun k => (smallEtalePostcompBaseChangeAdjunction B S hS (j k) (hj k) (hrep k)).counit.app U)
      ∈ SmallEtale.topology B S hS V.1 U := by
  let g : U.obj.left ⟶ W₀ := yoneda.preimage (U.obj.hom ≫ p.hom)
  have hP := Space.isColimit_yoneda_of_isColimit_toScheme B S hS W W₀ w hW
  obtain ⟨W', q, hq, hz, -, hcover, -⟩ := Sheaf.exists_clopen_decomposition_of_isColimit_cofan
    (fun k => (BigFppfOver.topology B S hS).yoneda.map (w k)) hP U.obj.left g
  choose z hz using hz
  have hqe : ∀ k, Etale ((BigFppfOver.toScheme B S hS).map (q k)) := fun k => by
    have := hq k
    infer_instance
  let c : ι → SmallEtale B S hS V.1 := fun k => SmallEtale.ofEtaleMap U (q k) (hqe k)
  let a : ∀ k, c k ⟶ U := fun k => SmallEtale.ofEtaleMapHom U (q k) (hqe k)
  refine (SmallEtale.topology B S hS V.1).superset_covering ?_
    (SmallEtale.ofArrows_mem_topology B S hS V.1 c a
      (ofArrows_mem_etalePrecoverage_iff.2 ⟨hcover, hqe⟩))
  rintro Y h ⟨Z, e, f, ⟨k⟩, rfl⟩
  have hα : (yoneda.map (q k) ≫ U.obj.hom) ≫ p.hom =
      yoneda.map (z k) ≫ ((schemeSpaceFunctor B S hS).map (w k)).hom := by
    have h1 : yoneda.map (z k ≫ w k) = yoneda.map (q k ≫ g) := congrArg yoneda.map (hz k)
    rw [Functor.map_comp, Functor.map_comp, Functor.map_preimage] at h1
    exact (Category.assoc _ _ _).trans h1.symm
  let α : yoneda.obj (W' k) ⟶ (V' k).1 :=
    (AlgebraicSpaces.isPullback_hom B S hS (hsq k)).lift _ _ hα
  have hα' : α ≫ (j k).hom = yoneda.map (q k) ≫ U.obj.hom :=
    (AlgebraicSpaces.isPullback_hom B S hS (hsq k)).lift_fst _ _ hα
  let ml : W' k ⟶ (hrep k).pullback U.obj.hom := (hrep k).lift α (q k) hα'
  let m : c k ⟶ (smallEtalePostcomp B S hS (j k) (hj k)).obj
      ((smallBaseChange B S hS (j k) (hrep k)).obj U) :=
    ObjectProperty.homMk (CostructuredArrow.homMk ml
      ((congrArg (· ≫ (j k).hom) ((hrep k).lift_fst α (q k) hα')).trans hα'))
  refine ⟨_, e ≫ m, _, ⟨k⟩, ?_⟩
  rw [Category.assoc]
  congr 1
  refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ ?_)
  exact ((congrArg (ml ≫ ·)
    (smallEtalePostcompBaseChangeAdjunction_counit_left B S hS (j k) (hj k) (hrep k) U)).trans
      ((hrep k).lift_snd α (q k) hα'))

/-- **Modules on an algebraic space over a disjoint union of schemes.** For `V` over
`W₀ = ∐ W_k` with pieces `V_k = V ×_{W₀} W_k`, restriction identifies `𝒪_V`-modules with families
of `𝒪_{V_k}`-modules. -/
theorem isEquivalence_pi'_etaleModulePullback_of_isPullback_cofan
    (hj : ∀ k, IsEtale B S hS (j k).hom) :
    (Functor.pi' fun k => etaleModulePullback.{u, u} B S hS (j k) (hj k)).IsEquivalence :=
  have := fun k => mono_hom_of_isPullback_cofan hW hsq k
  isEquivalence_pi'_etaleModulePullback B S hS j hj
    (relativelyRepresentable_hom_of_isPullback_cofan hsq)
    (ofArrows_counit_mem_topology_of_isPullback_cofan hW hsq hj _)
    (fun _ _ hik Z a b hab => isEmpty_of_isPullback_cofan hW hsq hik Z a b hab)

/-- **Morphisms in the derived category of an algebraic space over a disjoint union of
schemes**, in any model of the derived categories. For `V` over `W₀ = ∐ W_k` with pieces
`V_k = V ×_{W₀} W_k` and `K`, `E` in `D(𝒪_V)`, the map
`Hom(K, E) ⟶ ∏_k Hom(K|_{V_k}, E|_{V_k})` is bijective. -/
theorem bijective_mapDerivedCategory_etaleModulePullback_map_of_isPullback_cofan
    (hj : ∀ k, IsEtale B S hS (j k).hom)
    [HasDerivedCategory (Modules.{u, u} B S hS V.1 V.2)]
    [∀ k, HasDerivedCategory (Modules.{u, u} B S hS (V' k).1 (V' k).2)]
    (K E : DerivedCategory (Modules.{u, u} B S hS V.1 V.2)) :
    Function.Bijective fun φ : K ⟶ E => fun k =>
      (etaleModulePullback.{u, u} B S hS (j k) (hj k)).mapDerivedCategory.map φ :=
  have := isEquivalence_pi'_etaleModulePullback_of_isPullback_cofan hW hsq hj
  Functor.bijective_pi_mapDerivedCategory_map _ K E

end SchemeCoproduct

end AlgebraicGeometry.Space

end
