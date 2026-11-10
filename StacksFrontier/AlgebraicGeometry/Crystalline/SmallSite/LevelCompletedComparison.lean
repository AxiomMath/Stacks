module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedComparisonOfLevels
public import StacksFrontier.AlgebraicGeometry.Crystalline.CoordinateOperatorsInfinite
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelComparisonInterchange
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelSectionsPAdicComplete

/-!
# The functor of [Stacks, Tag 07JG] out of the crystals, with no finiteness of the coordinates

`Crystalline.GlobalCrystallineSituation.SmallSite.LevelComparison07JG` of
`StacksFrontier/AlgebraicGeometry/Crystalline/LevelFirstOrderCrystal.lean` is the datum the functor
of
[Stacks, Lemma 60.17.3, Tag 07JG] was built from, and it carries the comparison datum of a crystal
on the limit module `M = lim_e Γ(T_e, ℱ)` over the *uncompleted* base change.  Every producer of
such a datum from the levels therefore passed through the interchange
`(D ⊕ Ω) ⊗_D M ≅ lim_e ((D ⊕ Ω) ⊗_D M_e)` and so carried `[Fintype ι]`, which the source's own
situation — `P = A[x_i]` with an arbitrary family of variables — does not satisfy.

**This module is the same datum over the completed base change**, and it is the point at which the
finiteness disappears from the chapter: the bundle
`...SmallSite.LevelCompletedComparison07JG` below asks for the comparison datum of
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedFirstOrderComparison.lean`, its producer from
the levels is `Crystalline.CompletedFirstOrderComparison.ofLevels` — which runs on the crystal
level-quotient relation and on nothing about `Ω` — and the clause `hasCoordinateOperators` is
`Crystalline.hasCoordinateOperators_of_basis`, which needs a basis of `Ω` but no finiteness of its
index.

## Main definitions

Everything is in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `LevelScalars07JG.levelComponent` — the reduction `M = lim_e Γ(T_e, ℱ) ⟶ Γ(T_e, ℱ)` of a
  compatible family to its component at the level `e`, as a `D`-linear map.  The hypotheses of
  this module are stated about it, because that is the form in which the tree supplies them:
  `...SmallSite.mem_pow_smul_top_iff_wholeSpaceSectionsVal_eq_zero` is its kernel.
* `LevelScalars07JG.completedComparisonOfLevels` — the completed comparison datum on
  `M = lim_e Γ(T_e, ℱ)`, from the comparison data of the levels.
* `LevelCompletedComparison07JG` — **the datum the functor of [Stacks, Tag 07JG] is built from**,
  over the completed base change.
* `LevelCompletedComparison07JG.obj` and `...functor` — **the functor
  `{crystals in quasi-coherent 𝒪_{X/S}-modules on Cris(X/S)} ⟶ {pairs (M, ∇)}` of
  [Stacks, Tag 07JG]**, given such a datum.  Its source is the tag's own source category and it
  lands in `Crystalline.Pair` directly, without passing through
  `Crystalline.FirstOrderCrystal`.
* `levelCompletedComparison07JGOfLevelwise` — the datum assembled from level-by-level comparison
  data, the crystal level-quotient relation, a basis of `Ω` on the chosen differentials, and items
  (07JD) and (07JE).

## Main results

* `LevelScalars07JG.completedComparisonOfLevels_naturality` — the assembled datum is natural in
  the crystal, which is the functoriality clause of the tag.
* `isPAdicallyComplete_sections_of_ker` — item (07JB) from the level-quotient relation alone: the
  relation forces the annihilation `p^{N+e} M_e = 0`, so no separate annihilation input is needed.

## What is and is not proved

**No `@[stacks]` attribute is placed in this module.**  [Stacks, Tag 07JG] is
`...SmallSite.crystalPairFunctor` of `SmallSite/CrystalPairFunctor07JG.lean`, built directly from
the whole-space system and not through the datum of this module.  What changes here is the *price*
of the passage from the levels to the limit, and nothing else.  The inputs of
`levelCompletedComparison07JGOfLevelwise` are, in full:

1. the comparison datum of the crystal at each single level, with its compatibility and its
   naturality — the same input as before, and still the affine content of [Stacks, Tag 07J6];
2. the crystal level-quotient relation: the component maps `M ⟶ Γ(T_e, ℱ)` are surjective with
   kernel `p^{N+e} M`.  This is what *replaces* the finite basis.  It is the hypothesis of
   [Stacks, Proposition 60.21.3, Tag 07LG] that [Stacks, Lemma 60.19.3, Tag 07LF] does not have,
   and for a quasi-coherent crystal over the system of [Stacks, Proposition 60.21.1, Tag 07JN] it
   is a theorem, `...SmallSite.mem_pow_smul_top_iff_wholeSpaceSectionsVal_eq_zero` together with
   `...SmallSite.surjective_wholeSpaceSectionsVal`;
3. a basis of `Ω` on the chosen differentials, with **no** `[Fintype ι]`;
4. items (07JD) and (07JE) of the tag.  The functor `...SmallSite.crystalPairFunctor` derives
   them for its own pairs, from the Taylor expansion of the crystal over `D(1)`; they are not
   derived for the datum of this module.

Item (07JB) is not an input: it follows from (2).

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07JB](https://stacks.math.columbia.edu/tag/07JB)
* [Stacks Project, Tag 07JC](https://stacks.math.columbia.edu/tag/07JC)
* [Stacks Project, Tag 07JD](https://stacks.math.columbia.edu/tag/07JD)
* [Stacks Project, Tag 07JE](https://stacks.math.columbia.edu/tag/07JE)
* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Proposition 60.21.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct

universe u uI

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

variable {S : GlobalCrystallineSituation.{u}} {A : Type u} [CommRing A]
  {D : DividedPowerRing.{u}} {g : A →+* D} {Omega : Type u} [AddCommGroup Omega]
  [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
  {d : DividedPowerDerivation A D g Omega} {p : ℕ} {ι : Type uI} {dx : ι → Omega}

namespace LevelScalars07JG

variable (L : LevelScalars07JG S D)

/-- **The reduction of `M = lim_e Γ(T_e, ℱ)` to its component at the level `e`**, as a `D`-linear
map.  Every hypothesis below is about this map, and not about the restrictions
`Γ(T_{e+1}, ℱ) ⟶ Γ(T_e, ℱ)`, because that is the form in which the tree supplies them. -/
def levelComponent (F : QuasiCoherentCrystal S) (e : ℕ) :
    L.sections F →ₗ[(D : Type u)] L.levelSections F e :=
  limitLevelProj (L.levelSections F) (L.levelRestrict F) (L.sectionsInvLimitEquiv F) e

/-- The component of `m` at the level `e` is the `e`-th entry of the compatible family
corresponding to `m`. -/
@[simp] theorem levelComponent_apply (F : QuasiCoherentCrystal S) (e : ℕ) (m : L.sections F) :
    L.levelComponent F e m = (L.sectionsEquiv F m).val e :=
  rfl

/-- The components are compatible with the restrictions of the system. -/
theorem levelRestrict_comp_levelComponent (F : QuasiCoherentCrystal S) (e : ℕ) :
    L.levelRestrict F e ∘ₗ L.levelComponent F (e + 1) = L.levelComponent F e :=
  trans_comp_limitLevelProj (L.levelSections F) (L.levelRestrict F) (L.sectionsInvLimitEquiv F) e

/-- **A morphism of crystals commutes with the components**: the map of the limit modules it
induces is the limit of the maps of the levels. -/
theorem levelComponent_comp_sectionsMap {F G : QuasiCoherentCrystal S} (psi : F ⟶ G) (e : ℕ) :
    L.levelComponent G e ∘ₗ L.sectionsMap psi =
      L.levelSectionsMap psi e ∘ₗ L.levelComponent F e :=
  rfl

/-! ### Item (07JB) from the level-quotient relation -/

/-- **Item (07JB) from the crystal level-quotient relation alone.**  The relation
`ker (M ⟶ M_e) = p^{N+e} M` with surjective components forces the annihilation `p^{N+e} M_e = 0`,
so the `p`-adic completeness of `M = lim_e M_e` needs no separate input. -/
theorem isPAdicallyComplete_sections_of_ker (F : QuasiCoherentCrystal S) (N : ℕ)
    (hsurj : ∀ e, Function.Surjective (L.levelComponent F e))
    (hker : ∀ e, LinearMap.ker (L.levelComponent F e) =
      DividedPowers.pAdicIdeal (A := (D : Type u)) p ^ (N + e) •
        (⊤ : Submodule (D : Type u) (L.sections F))) :
    IsPAdicallyComplete p (D : Type u) (L.sections F) :=
  L.isPAdicallyComplete_sections p F N fun e x ↦ by
    have hbot := _root_.Crystalline.pow_smul_top_eq_bot_of_ker_proj (L.levelSections F) N
      (L.levelComponent F) hsurj hker e
    exact (_root_.Crystalline.pAdicIdeal_pow_smul_top_eq_bot_iff p (D : Type u)
      (L.levelSections F) N (n := e)).1 hbot x

/-! ### The completed comparison datum on the limit module -/

/-- **The completed comparison datum on `M = lim_e Γ(T_e, ℱ)`, from the comparison data of the
levels.**

This is `Crystalline.CompletedFirstOrderComparison.ofLevels` at the tower of level sections.  What
it consumes beyond the level data is the crystal level-quotient relation; **no basis of `Ω` and no
finiteness of its index appear**, which is what separates it from
`...SmallSite.LevelScalars07JG.comparisonOfLevels`. -/
def completedComparisonOfLevels (F : QuasiCoherentCrystal S) (N : ℕ)
    (hsurj : ∀ e, Function.Surjective (L.levelComponent F e))
    (hker : ∀ e, LinearMap.ker (L.levelComponent F e) =
      DividedPowers.pAdicIdeal (A := (D : Type u)) p ^ (N + e) •
        (⊤ : Submodule (D : Type u) (L.sections F)))
    (c : ∀ e : ℕ, FirstOrderComparison A D g Omega d (L.levelSections F e))
    (hc : ∀ (e : ℕ) (x : L.levelSections F (e + 1)),
      LinearMap.lTensor (firstOrderExtension D Omega) (L.levelRestrict F e) (c (e + 1) x) =
        c e (L.levelRestrict F e x)) :
    CompletedFirstOrderComparison A D g Omega d p (L.sections F) :=
  CompletedFirstOrderComparison.ofLevels (L.sections F) (L.levelSections F) (L.levelRestrict F)
    N (L.levelComponent F) hsurj hker (L.levelRestrict_comp_levelComponent F) c hc

/-- **The assembled datum is natural in the crystal**, which is the functoriality clause of
[Stacks, Lemma 60.17.3, Tag 07JG].  This is
`Crystalline.completedLevelComparisonFun_naturality`, whose hypothesis `hphi` is
`...SmallSite.LevelScalars07JG.levelComponent_comp_sectionsMap`. -/
theorem completedComparisonOfLevels_naturality {F G : QuasiCoherentCrystal S} (psi : F ⟶ G)
    (N : ℕ)
    (hsurjF : ∀ e, Function.Surjective (L.levelComponent F e))
    (hkerF : ∀ e, LinearMap.ker (L.levelComponent F e) =
      DividedPowers.pAdicIdeal (A := (D : Type u)) p ^ (N + e) •
        (⊤ : Submodule (D : Type u) (L.sections F)))
    (hsurjG : ∀ e, Function.Surjective (L.levelComponent G e))
    (hkerG : ∀ e, LinearMap.ker (L.levelComponent G e) =
      DividedPowers.pAdicIdeal (A := (D : Type u)) p ^ (N + e) •
        (⊤ : Submodule (D : Type u) (L.sections G)))
    (c : ∀ e : ℕ, FirstOrderComparison A D g Omega d (L.levelSections F e))
    (hc : ∀ (e : ℕ) (x : L.levelSections F (e + 1)),
      LinearMap.lTensor (firstOrderExtension D Omega) (L.levelRestrict F e) (c (e + 1) x) =
        c e (L.levelRestrict F e x))
    (c' : ∀ e : ℕ, FirstOrderComparison A D g Omega d (L.levelSections G e))
    (hc' : ∀ (e : ℕ) (x : L.levelSections G (e + 1)),
      LinearMap.lTensor (firstOrderExtension D Omega) (L.levelRestrict G e) (c' (e + 1) x) =
        c' e (L.levelRestrict G e x))
    (hnat : ∀ (e : ℕ) (x : L.levelSections F e),
      c' e (L.levelSectionsMap psi e x) =
        LinearMap.lTensor (firstOrderExtension D Omega) (L.levelSectionsMap psi e) (c e x))
    (m : L.sections F) :
    L.completedComparisonOfLevels G N hsurjG hkerG c' hc' (L.sectionsMap psi m) =
      AdicCompletion.map (DividedPowers.pAdicIdeal (A := (D : Type u)) p)
        (LinearMap.lTensor (firstOrderExtension D Omega) (L.sectionsMap psi))
        (L.completedComparisonOfLevels F N hsurjF hkerF c hc m) :=
  completedLevelComparisonFun_naturality (L.sections F) (L.sections G) (L.levelSections F)
    (L.levelRestrict F) (L.levelSections G) (L.levelRestrict G) N (L.levelComponent F)
    (L.levelComponent G) hsurjF hkerF (L.levelRestrict_comp_levelComponent F) hsurjG hkerG
    (L.levelRestrict_comp_levelComponent G) (L.sectionsMap psi) (L.levelSectionsMap psi)
    (fun e ↦ L.levelComponent_comp_sectionsMap psi e) c hc c' hc' hnat m

end LevelScalars07JG

/-! ### The datum the functor of the tag is built from -/

/-- **The datum the functor of [Stacks, Lemma 60.17.3, Tag 07JG] is built from, over the completed
base change.**

This is `...SmallSite.LevelComparison07JG` with its comparison datum completed.  Every field is a
named missing input and none is a stand-in for the tag: `comparison` and `comparison_naturality`
are the comparison datum of the crystal read on `M = lim_e Γ(T_e, ℱ)` and its naturality, and the
remaining four are items (07JB), (07JD), (07JE) of the tag's target with the non-vacuity of the
last two.  What the datum does **not** supply is the module, its `D`-action, the identification of
it with the limit and the functoriality: those are
`...SmallSite.LevelScalars07JG.sections`, `...sectionsInvLimitEquiv` and `...sectionsMap`, all
constructed. -/
structure LevelCompletedComparison07JG (S : GlobalCrystallineSituation.{u}) (A : Type u)
    [CommRing A] (D : DividedPowerRing.{u}) (g : A →+* D) (Omega : Type u) [AddCommGroup Omega]
    [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
    (d : DividedPowerDerivation A D g Omega) (p : ℕ) {ι : Type uI} (dx : ι → Omega)
    (L : LevelScalars07JG S D) where
  /-- The completed comparison datum of the crystal, read on `M = lim_e Γ(T_e, ℱ)`. -/
  comparison : ∀ F : QuasiCoherentCrystal S,
    CompletedFirstOrderComparison A D g Omega d p (L.sections F)
  /-- It is natural in the crystal, which is the functoriality clause of the tag. -/
  comparison_naturality : ∀ {F G : QuasiCoherentCrystal S} (psi : F ⟶ G) (m : L.sections F),
    comparison G (L.sectionsMap psi m) =
      AdicCompletion.map (DividedPowers.pAdicIdeal (A := (D : Type u)) p)
        (LinearMap.lTensor (firstOrderExtension D Omega) (L.sectionsMap psi)) (comparison F m)
  /-- **Item (07JB).**  The module is `p`-adically complete. -/
  isPAdicallyComplete : ∀ F : QuasiCoherentCrystal S,
    IsPAdicallyComplete p (D : Type u) (L.sections F)
  /-- The connection admits coordinate operators for the chosen differentials. -/
  hasCoordinateOperators : ∀ F : QuasiCoherentCrystal S,
    ∃ theta : ι → (L.sections F → L.sections F),
      IsCoordinateExpansion p (D : Type u) Omega dx (comparison F).completedConnection theta
  /-- **Item (07JD).**  The connection is integrable. -/
  isIntegrable : ∀ F : QuasiCoherentCrystal S,
    IsIntegrable p (D : Type u) Omega dx (comparison F).completedConnection
  /-- **Item (07JE).**  The connection is topologically quasi-nilpotent. -/
  isTopologicallyQuasiNilpotent : ∀ F : QuasiCoherentCrystal S,
    IsTopologicallyQuasiNilpotent p (D : Type u) Omega dx (comparison F).completedConnection

namespace LevelCompletedComparison07JG

variable {L : LevelScalars07JG S D} (C : LevelCompletedComparison07JG S A D g Omega d p dx L)

/-- **The pair `(M, ∇)` of [Stacks, Lemma 60.17.3, Tag 07JG] attached to a crystal in
quasi-coherent `𝒪_{X/S}`-modules**: the module is `M = lim_e Γ(T_e, ℱ)` over `D`, and the
connection is the one the completed comparison datum determines, which is item (07JC). -/
def obj (F : QuasiCoherentCrystal S) :
    Pair.{u, u, uI, u} p (D : Type u) Omega dx (derivationFun A D g Omega d) where
  carrier := L.sections F
  isPAdicallyComplete := C.isPAdicallyComplete F
  nabla := (C.comparison F).completedConnection
  hasCoordinateOperators := C.hasCoordinateOperators F
  isIntegrable := C.isIntegrable F
  isTopologicallyQuasiNilpotent := C.isTopologicallyQuasiNilpotent F

/-- **A morphism of crystals is horizontal for the connections of the two pairs.**  The
differential component of the base change is natural in the module,
`Crystalline.firstOrderDifferentialComm_comp_lTensor`, and the comparison data are natural in the
crystal, so the connections are too. -/
theorem horizontal {F G : QuasiCoherentCrystal S} (psi : F ⟶ G) (m : L.sections F) :
    (C.obj G).nabla (L.sectionsMap psi m) =
      AdicCompletion.map (DividedPowers.pAdicIdeal (A := (D : Type u)) p)
        (TensorProduct.map (L.sectionsMap psi)
          (LinearMap.id (R := (D : Type u)) (M := Omega))) ((C.obj F).nabla m) := by
  change AdicCompletion.map (DividedPowers.pAdicIdeal (A := (D : Type u)) p)
      (firstOrderDifferentialComm D Omega (L.sections G))
      (C.comparison G (L.sectionsMap psi m)) = _
  rw [C.comparison_naturality psi m, AdicCompletion.map_comp_apply,
    firstOrderDifferentialComm_comp_lTensor D Omega (L.sections F) (L.sectionsMap psi),
    ← AdicCompletion.map_comp_apply]
  rfl

/-- **The functor of [Stacks, Lemma 60.17.3, Tag 07JG], with the source the tag gives it**: from
the crystals in quasi-coherent `𝒪_{X/S}`-modules on `Cris(X/S)` to the pairs `(M, ∇)` satisfying
items (07JB), (07JC), (07JD) and (07JE).

Unlike `...SmallSite.functor07JG` this one does not factor through
`Crystalline.FirstOrderCrystal`: the pair is built from the completed comparison datum directly,
which is what removes the finiteness of the coordinates from the construction. -/
def functor :
    QuasiCoherentCrystal S ⥤ Pair.{u, u, uI, u} p (D : Type u) Omega dx
      (derivationFun A D g Omega d) where
  obj F := C.obj F
  map psi := { toLinearMap := L.sectionsMap psi, horizontal := C.horizontal psi }
  map_id F := by apply PairHom.ext; exact L.sectionsMap_id F
  map_comp psi chi := by apply PairHom.ext; exact L.sectionsMap_comp psi chi

/-- The functor sends a crystal `F` to the pair `C.obj F`. -/
@[simp] theorem functor_obj (C : LevelCompletedComparison07JG S A D g Omega d p dx L)
    (F : QuasiCoherentCrystal S) : C.functor.obj F = C.obj F :=
  rfl

/-- The linear map underlying the image of a morphism `psi` is `L.sectionsMap psi`. -/
@[simp] theorem functor_map_toLinearMap (C : LevelCompletedComparison07JG S A D g Omega d p dx L)
    {F G : QuasiCoherentCrystal S} (psi : F ⟶ G) :
    (C.functor.map psi).toLinearMap = L.sectionsMap psi :=
  rfl

end LevelCompletedComparison07JG

/-! ### The datum from level-by-level comparison data -/

/-- **The datum of [Stacks, Lemma 60.17.3, Tag 07JG] over a system of levels, from data at the
single objects `T_e` and the crystal level-quotient relation.**

The four inputs are listed in the module documentation.  The one that is *not* here, and whose
absence is the point of this module, is `[Fintype ι]`: the basis `b` of `Ω` is used only by
`Crystalline.hasCoordinateOperators_of_basis`, which does not need its index finite, and the
passage from the levels to the limit is
`Crystalline.CompletedFirstOrderComparison.ofLevels`, which does not need a basis at all.

**No `@[stacks]` attribute follows from this**: it is a term of a record of hypotheses, items
(07JD) and (07JE) among them. -/
def levelCompletedComparison07JGOfLevelwise (L : LevelScalars07JG S D) (N : ℕ)
    (hsurj : ∀ (F : QuasiCoherentCrystal S) (e : ℕ),
      Function.Surjective (L.levelComponent F e))
    (hker : ∀ (F : QuasiCoherentCrystal S) (e : ℕ),
      LinearMap.ker (L.levelComponent F e) =
        DividedPowers.pAdicIdeal (A := (D : Type u)) p ^ (N + e) •
          (⊤ : Submodule (D : Type u) (L.sections F)))
    (c : ∀ (F : QuasiCoherentCrystal S) (e : ℕ),
      FirstOrderComparison A D g Omega d (L.levelSections F e))
    (hc : ∀ (F : QuasiCoherentCrystal S) (e : ℕ) (x : L.levelSections F (e + 1)),
      LinearMap.lTensor (firstOrderExtension D Omega) (L.levelRestrict F e) (c F (e + 1) x) =
        c F e (L.levelRestrict F e x))
    (hnat : ∀ {F G : QuasiCoherentCrystal S} (psi : F ⟶ G) (e : ℕ) (x : L.levelSections F e),
      c G e (L.levelSectionsMap psi e x) =
        LinearMap.lTensor (firstOrderExtension D Omega) (L.levelSectionsMap psi e) (c F e x))
    (b : Module.Basis ι (D : Type u) Omega) (hdx : ∀ i, dx i = b i)
    (hint : ∀ F : QuasiCoherentCrystal S,
      IsIntegrable p (D : Type u) Omega dx
        (L.completedComparisonOfLevels F N (hsurj F) (hker F) (c F)
          (hc F)).completedConnection)
    (hqn : ∀ F : QuasiCoherentCrystal S,
      IsTopologicallyQuasiNilpotent p (D : Type u) Omega dx
        (L.completedComparisonOfLevels F N (hsurj F) (hker F) (c F)
          (hc F)).completedConnection) :
    LevelCompletedComparison07JG S A D g Omega d p dx L where
  comparison F := L.completedComparisonOfLevels F N (hsurj F) (hker F) (c F) (hc F)
  comparison_naturality psi m :=
    L.completedComparisonOfLevels_naturality psi N _ _ _ _ _ _ _ _ (fun e x ↦ hnat psi e x) m
  isPAdicallyComplete F := L.isPAdicallyComplete_sections_of_ker F N (hsurj F) (hker F)
  hasCoordinateOperators F :=
    _root_.Crystalline.hasCoordinateOperators_of_basis p (D : Type u) Omega
      (dx := dx) (fun G : QuasiCoherentCrystal S ↦ L.sections G)
      (fun G ↦ (L.completedComparisonOfLevels G N (hsurj G) (hker G) (c G)
        (hc G)).completedConnection) b hdx
      (fun G ↦ L.isPAdicallyComplete_sections_of_ker G N (hsurj G) (hker G)) F
  isIntegrable := hint
  isTopologicallyQuasiNilpotent := hqn

end Crystalline.GlobalCrystallineSituation.SmallSite

end
