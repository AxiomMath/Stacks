module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Blowup.FiniteOverLocalDimensionOne
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCap42.ClosedSubschemeZeroCycle
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward.ComponentDegree
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward.Proper
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDominantPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassOfSection
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DegreeHomomorphism
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegreeClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FibreDifferencePushforward
public import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClassTensor
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullbackCycles.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.IteratedCap
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.TowerChow
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.CurveDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ModuleComposition
public import StacksFrontier.AlgebraicGeometry.Chow.Setup.JacobsonDimension
public import StacksFrontier.AlgebraicGeometry.ChowNoetherian.Refinements
public import StacksFrontier.AlgebraicGeometry.ClosedSupportFiniteness.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafGeneral
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic
public import StacksFrontier.AlgebraicGeometry.HProjective.QuasiProjectiveOfHQuasiProjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.PseudoMorphism
public import StacksFrontier.AlgebraicGeometry.Segre.ChartSurjective
public import StacksFrontier.AlgebraicGeometry.TensorSheafSpellingIso.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RiemannRochZeroScheme
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersection
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.Additivity
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.ComponentsVanishing
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.DivisorIntersectionProper
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.FiniteDominant
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.Positivity
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.PositivityZeroDim

/-!
# Numerical intersection numbers are degrees of iterated first Chern classes

Let `k` be a field, let `X` be a proper scheme over `k`, let `Z ⊆ X` be a closed subscheme of
dimension `d` and let `𝓛_1, …, 𝓛_d` be invertible `𝒪_X`-modules. [Stacks, Tag 0BFI] identifies
the numerical intersection number of [Stacks, Tag 0BEP] with a degree on the Chow groups:

`(𝓛_1 ⋯ 𝓛_d · Z) = deg(c₁(𝓛_1) ∩ ⋯ ∩ c₁(𝓛_d) ∩ [Z]_d)`,

and in particular `deg_𝓛(Z) = deg(c₁(𝓛)^d ∩ [Z]_d)` for `𝓛` ample.

## Main definitions

* `AlgebraicGeometry.iteratedFirstChernCap`: the iterated cap
  `c₁(𝓛_1) ∩ ⋯ ∩ c₁(𝓛_d) ∩ - : A_d(X) ⟶ A_0(X)`.
* `AlgebraicGeometry.capDegree`: its composite with the degree `A_0(X) ⟶ ℤ` of
  [Stacks, Tag 0AZ1].

## Main results

* `AlgebraicGeometry.intersectionNumber_eq_chowDegree_iteratedFirstChernCap_and_ample`:
  the formula together with its ample case.
* `AlgebraicGeometry.intersectionNumber_eq_chowDegree_iteratedFirstChernCap`: the formula.
* `AlgebraicGeometry.degreeWithRespectTo_eq_chowDegree_iteratedFirstChernCap`: its ample case.
* `AlgebraicGeometry.intersectionNumber_comp_perm`: the intersection number is symmetric in the
  invertible modules.
* `AlgebraicGeometry.cycleAssociatedToClosedSubscheme_eq_finsum_dimComponents`:
  `[Z]_d = ∑ m_i [Z_i]` over the `d`-dimensional components.

## Implementation notes

The proof is the induction on `d` of [Stacks, Tag 0BFI], for closed subschemes of dimension *at
most* `d` (an effective Cartier divisor may be empty). In dimension zero both sides are
`dim_k Γ(Z, 𝒪_Z)`. In positive dimension both sides decompose along the `d`-dimensional components
([Stacks, Tag 0BES]), so `Z` may be taken integral. Chow's lemma ([Stacks, Tags 0200 and 0201])
dominates `Z` birationally by an integral scheme `Y` immersed in a projective space; the
intersection number is unchanged by [Stacks, Tag 0BET] and the degree of the cap product by the
projection formula of Stacks 02SU. On `Y`, which carries an ample invertible module, the last module
is `𝒪(D) ⊗ 𝒪(D')^{⊗ -1}` with `D`, `D'` effective Cartier ([Stacks, Tag 0AYM]); both sides are
additive in it ([Stacks, Tag 0BER] and Stacks 02SP), and for an effective Cartier divisor they
reduce to `D` and the first `d - 1` modules, by [Stacks, Tag 0BEU] and by Stacks 02SQ respectively.

The cap with `c₁(𝓛_d)` is the innermost one, as in the notation of [Stacks, Tag 0BFI]; since
[Stacks, Tag 0BEU] removes the *first* module, the numerical side is first permuted, which is
`AlgebraicGeometry.intersectionNumber_comp_perm`.

The Chow groups are those of `Stacks.Chow.fieldChowSituation k`, the spectrum of `k` with its
zero dimension function, and the degree is taken at the closed point of `Spec k`.

## References

* [Stacks Project, Tag 0BFI](https://stacks.math.columbia.edu/tag/0BFI)
* [Stacks Project, Tag 0BEP](https://stacks.math.columbia.edu/tag/0BEP)
* [Stacks Project, Tag 0BEW](https://stacks.math.columbia.edu/tag/0BEW)
* [Stacks Project, Tag 0AZ1](https://stacks.math.columbia.edu/tag/0AZ1)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

open Stacks.Chow

/-- The invertibility of a module on a scheme, at the presheaf spelling, re-read at the sheaf
spelling the cap products are stated with; the two spellings are definitionally equal. -/
theorem isInvertible_sheaf_of_presheaf {X : Scheme.{u}} (L : X.Modules)
    [h : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L := h

attribute [local instance] isInvertible_sheaf_of_presheaf

/-! ### Iterated caps along an arbitrary list -/

section IteratedCap

variable (C : ChowSituation.{u}) {P : Scheme.{u}} (sP : P ⟶ C.S) [LocallyOfFiniteType sP]

/-- **Peeling off the innermost cap of an arbitrary list.** The operator at the end of the list
is applied first. -/
theorem iteratedChernCapOnChow_append_singleton (Os : List (ChernCapOperator C sP))
    (O : ChernCapOperator C sP) (d : ℤ) (x : chowGroup C sP (d + ((Os ++ [O]).length : ℤ)))
    (y : chowGroup C sP (d + (Os.length : ℤ) + 1)) (hxy : x ≍ y)
    (z : chowGroup C sP (d + (Os.length : ℤ)))
    (hz : z ≍ O.capOnChow C sP (d + (Os.length : ℤ)) y) :
    iteratedChernCapOnChow C sP (Os ++ [O]) d x = iteratedChernCapOnChow C sP Os d z := by
  induction Os generalizing d with
  | nil =>
    change iteratedChernCapOnChow C sP [O] d x = _
    rw [iteratedChernCapOnChow_cons_eq C sP O [] d x
      (chowGroupCast C sP (by simp) x) (chowGroupCast_heq C sP _ x).symm]
    refine chowGroup_eq_of_heq C sP ?_
    refine HEq.trans ?_ (iteratedChernCapOnChow_nil_heq C sP d z).symm
    refine HEq.trans ?_ hz.symm
    refine capOnChow_heq C sP O (by simp) ?_
    exact (iteratedChernCapOnChow_nil_heq C sP _ _).trans
      ((chowGroupCast_heq C sP _ x).trans hxy)
  | cons Q Os ih =>
    change iteratedChernCapOnChow C sP (Q :: (Os ++ [O])) d x = _
    rw [iteratedChernCapOnChow_cons_eq C sP Q (Os ++ [O]) d x
      (chowGroupCast C sP
        (by simp only [List.length_cons, List.length_append, List.length_nil, Nat.cast_add,
          Nat.cast_one]; ring) x) (chowGroupCast_heq C sP _ x).symm,
      iteratedChernCapOnChow_cons_eq C sP Q Os d z
      (chowGroupCast C sP (by simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring) z)
      (chowGroupCast_heq C sP _ z).symm]
    congr 1
    refine ih (d + 1) _
      (chowGroupCast C sP (by simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring) y)
      ((chowGroupCast_heq C sP _ x).trans (hxy.trans (chowGroupCast_heq C sP _ y).symm)) _ ?_
    refine (chowGroupCast_heq C sP _ z).trans (hz.trans ?_)
    exact capOnChow_heq C sP O (by simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring)
      (chowGroupCast_heq C sP _ y).symm

end IteratedCap

/-! ### The degree of an iterated first Chern class cap -/

section CapDegree

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- **The iterated first Chern class cap** `α ↦ c₁(𝓛_1) ∩ ⋯ ∩ c₁(𝓛_d) ∩ α`, from `A_d(X)` to
`A_0(X)`, for a family of `d` invertible modules on a scheme proper over a field: the cap with
`c₁(𝓛_d)` is taken first and the cap with `c₁(𝓛_1)` last, each being the operation of
[Stacks, Tag 02TI]. -/
def iteratedFirstChernCap {d : ℕ} (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] :
    chowGroup (fieldChowSituation k) f d →+ chowGroup (fieldChowSituation k) f 0 :=
  (iteratedChernCapOnChow (fieldChowSituation k) f
      (List.ofFn fun j => invCap (fieldChowSituation k) f (L j)) 0).comp
    (chowGroupCast (fieldChowSituation k) f (by simp)).toAddMonoidHom

/-- The degree `deg(c₁(𝓛_1) ∩ ⋯ ∩ c₁(𝓛_d) ∩ α)` of the iterated first Chern class cap of a class
`α ∈ A_d(X)`, the degree being that of [Stacks, Tag 0AZ1]. -/
def capDegree {d : ℕ} (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] :
    chowGroup (fieldChowSituation k) f d →+ ℤ :=
  (chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k) f
      (IsLocalRing.closedPoint k)).comp (iteratedFirstChernCap k f L)

/-- With no module the degree of the iterated cap is the degree of the class. -/
theorem capDegree_zero (L : Fin 0 → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    (a : chowGroup (fieldChowSituation k) f 0) :
    capDegree k f L a =
      chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k) f
        (IsLocalRing.closedPoint k) a := by
  simp only [capDegree, iteratedFirstChernCap, AddMonoidHom.comp_apply,
    AddEquiv.coe_toAddMonoidHom]
  congr 1

/-- **Peeling off the innermost cap.** The last module of the family is capped first. -/
theorem capDegree_succ {d : ℕ} (L : Fin (d + 1) → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    (a : chowGroup (fieldChowSituation k) f ((d + 1 : ℕ) : ℤ)) :
    capDegree k f L a =
      capDegree k f (fun j : Fin d => L j.castSucc)
        ((invCap (fieldChowSituation k) f (L (Fin.last d))).capOnChow (fieldChowSituation k) f
          (d : ℤ)
          (chowGroupCast (fieldChowSituation k) f (by push_cast; ring) a)) := by
  simp only [capDegree, iteratedFirstChernCap, AddMonoidHom.comp_apply,
    AddEquiv.coe_toAddMonoidHom]
  refine congrArg (chowDegree (fieldChowSituation k)
    (fieldChowSituation_dimensionFunction_eq_zero k) f (IsLocalRing.closedPoint k)) ?_
  have hlist : (List.ofFn fun j => invCap (fieldChowSituation k) f (L j)) =
      (List.ofFn fun j : Fin d => invCap (fieldChowSituation k) f (L j.castSucc)) ++
        [invCap (fieldChowSituation k) f (L (Fin.last d))] := by
    rw [List.ofFn_succ', List.concat_eq_append]
  set C := fieldChowSituation k
  set Os := List.ofFn fun j : Fin d => invCap C f (L j.castSucc)
  set O := invCap C f (L (Fin.last d))
  have hOs : (Os.length : ℤ) = d := by simp [Os]
  have e₁ : ((d + 1 : ℕ) : ℤ) = 0 + ((Os ++ [O]).length : ℤ) := by
    simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one, hOs]; ring
  have e₂ : ((d + 1 : ℕ) : ℤ) = 0 + (Os.length : ℤ) + 1 := by rw [hOs]; push_cast; ring
  have e₃ : (d : ℤ) = 0 + (Os.length : ℤ) := by rw [hOs]; ring
  refine chowGroup_eq_of_heq C f ((iteratedChernCapOnChow_heq_of_eq C f hlist 0
    (y := chowGroupCast C f e₁ a) ?_).trans ?_)
  · exact (chowGroupCast_heq C f _ a).trans (chowGroupCast_heq C f _ a).symm
  · rw [iteratedChernCapOnChow_append_singleton C f Os O 0 _ (chowGroupCast C f e₂ a)
      ((chowGroupCast_heq C f _ a).trans (chowGroupCast_heq C f _ a).symm)
      (chowGroupCast C f e₃ (O.capOnChow C f (d : ℤ)
          (chowGroupCast C f (by push_cast; ring) a)))]
    refine (chowGroupCast_heq C f _ _).trans ?_
    exact capOnChow_heq C f O e₃ ((chowGroupCast_heq C f _ a).trans
      (chowGroupCast_heq C f _ a).symm)

/-- **The degree is invariant under proper pushforward**: a zero cycle class and its proper
pushforward along a morphism of schemes proper over the field have the same degree. -/
theorem chowDegree_properChowPushforward {Y : Scheme.{u}} (fY : Y ⟶ Spec (.of k)) [IsProper fY]
    (g : Y ⟶ X) [IsProper g] (hg : g ≫ f = fY) (z : chowGroup (fieldChowSituation k) fY 0) :
    chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k) fY
        (IsLocalRing.closedPoint k) z =
      chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k) f
        (IsLocalRing.closedPoint k)
        (properChowPushforward (fieldChowSituation k) fY f g hg 0
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper (fieldChowSituation k)
            fY f g hg 0) z) := by
  subst hg
  simp only [chowDegree, AddMonoidHom.comp_apply]
  congr 1
  exact (properChowPushforward_properChowPushforward (fieldChowSituation k) (g ≫ f) f
    (𝟙 (fieldChowSituation k).S) g f rfl (Category.comp_id f) 0 z).symm

/-- **The degree of the iterated cap is invariant under proper pushforward**, by the projection
formula of Stacks 02SU:
`deg(c₁(g^*𝓛_1) ∩ ⋯ ∩ c₁(g^*𝓛_d) ∩ β) = deg(c₁(𝓛_1) ∩ ⋯ ∩ c₁(𝓛_d) ∩ g_*β)`. -/
theorem capDegree_properChowPushforward {Y : Scheme.{u}} (fY : Y ⟶ Spec (.of k)) [IsProper fY]
    (g : Y ⟶ X) [IsProper g] (hg : g ≫ f = fY) {d : ℕ} (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    (β : chowGroup (fieldChowSituation k) fY d) :
    capDegree k fY (fun j => (Scheme.Modules.pullback g).obj (L j)) β =
      capDegree k f L (properChowPushforward (fieldChowSituation k) fY f g hg d
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper (fieldChowSituation k)
          fY f g hg d) β) := by
  simp only [capDegree, iteratedFirstChernCap, AddMonoidHom.comp_apply,
    AddEquiv.coe_toAddMonoidHom]
  rw [chowDegree_properChowPushforward k f fY g hg]
  refine congrArg (chowDegree (fieldChowSituation k)
    (fieldChowSituation_dimensionFunction_eq_zero k) f (IsLocalRing.closedPoint k)) ?_
  set C := fieldChowSituation k
  have e₁ : (d : ℤ) = 0 + ((List.ofFn fun j =>
      invCap C fY ((Scheme.Modules.pullback g).obj (L j))).length : ℤ) := by simp
  have e₂ : (d : ℤ) = 0 + ((List.ofFn fun j => invCap C f (L j)).length : ℤ) := by simp
  set β' := properChowPushforward C fY f g hg d
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C fY f g hg d) β
  have hy : chowGroupCast C f e₂ β' ≍ properChowPushforward C fY f g hg _
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C fY f g hg _)
        (chowGroupCast C fY e₁ β) :=
    (chowGroupCast_heq C f e₂ β').trans (properChowPushforward_heq C fY f g hg e₁
      (chowGroupCast_heq C fY e₁ β).symm)
  exact properChowPushforward_iteratedChernCapOnChow_ofFn C fY f g hg L 0
    (chowGroupCast C fY e₁ β) (chowGroupCast C f e₂ β') hy

end CapDegree

/-! ### The intersection number is symmetric in the modules -/

section Permutation

open Stacks.SheafOfModules.Invertible

variable {X : Scheme.{u}} {r : ℕ} (L : Fin r → X.Modules)
  [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]

/-- Successive twists along two lists of indices which are permutations of each other give
isomorphic modules: an adjacent transposition of two factors is the interchange
`(M ⊗ A) ⊗ B ≅ (M ⊗ B) ⊗ A`. -/
theorem nonempty_twistList_iso_of_perm (e : Fin r → ℤ) {l l' : List (Fin r)} (h : l.Perm l')
    (M : X.Modules) : Nonempty (twistList L e l M ≅ twistList L e l' M) := by
  induction h generalizing M with
  | nil => exact ⟨Iso.refl _⟩
  | cons a _ ih => exact ih _
  | swap a b l =>
    exact ⟨twistListIso L e l (tensorProductSwapIso X.presheaf X.ringCatSheaf.2 M _ _)⟩
  | trans _ _ ih₁ ih₂ => exact ⟨(ih₁ M).some ≪≫ (ih₂ M).some⟩

/-- Reindexing the modules and the exponents along a map of the indices is twisting along the
image of the list of indices. -/
theorem twistList_comp {r' : ℕ} (σ : Fin r' → Fin r) (e : Fin r → ℤ) (l : List (Fin r'))
    (M : X.Modules) :
    haveI : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L (σ j)) :=
      fun _ => inferInstance
    twistList (fun j => L (σ j)) (fun j => e (σ j)) l M = twistList L e (l.map σ) M := by
  induction l generalizing M with
  | nil => rfl
  | cons a l ih => exact ih _

end Permutation

section IntersectionPermutation

variable (k : Type u) [Field k] {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
  (i : Z ⟶ X) [IsClosedImmersion i]

/-- **The intersection number is symmetric in the invertible modules**:
`(𝓛_{σ(1)} ⋯ 𝓛_{σ(d)} · Z) = (𝓛_1 ⋯ 𝓛_d · Z)` for every permutation `σ`. -/
theorem intersectionNumber_comp_perm (d : ℕ) (hd : topologicalKrullDim Z ≤ d)
    (L : Fin d → X.Modules) [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    (σ : Equiv.Perm (Fin d)) :
    haveI : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L (σ j)) :=
      fun _ => inferInstance
    intersectionNumber k f i d hd (fun j => L (σ j)) = intersectionNumber k f i d hd L := by
  classical
  have : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L (σ j)) :=
    fun j => inferInstance
  rw [intersectionNumber_eq_sum_chiOverField, intersectionNumber_eq_sum_chiOverField]
  refine Fintype.sum_equiv (Equiv.finsetCongr σ) _ _ fun T => ?_
  have hcard : (Equiv.finsetCongr σ T).card = T.card := by simp
  rw [hcard]
  congr 1
  refine chiOverField_eq_of_iso k (i ≫ f) (Nonempty.some ?_)
  have hexp : (fun q => if q ∈ T then (1 : ℤ) else 0) =
      fun q => (fun q' => if q' ∈ Equiv.finsetCongr σ T then (1 : ℤ) else 0) (σ q) := by
    funext q
    simp [Equiv.finsetCongr_apply]
  change Nonempty (twistList (fun q => (Scheme.Modules.pullback i).obj (L (σ q)))
      (fun q => if q ∈ T then 1 else 0) (List.finRange d) _ ≅
    twistList (fun q => (Scheme.Modules.pullback i).obj (L q))
      (fun q => if q ∈ Equiv.finsetCongr σ T then 1 else 0) (List.finRange d) _)
  rw [hexp]
  have h := twistList_comp (fun q => (Scheme.Modules.pullback i).obj (L q)) σ
    (fun q' => if q' ∈ Equiv.finsetCongr σ T then (1 : ℤ) else 0) (List.finRange d)
    (SheafOfModules.unit Z.ringCatSheaf)
  have hperm : ((List.finRange d).map σ).Perm (List.finRange d) :=
    (List.perm_ext_iff_of_nodup ((List.nodup_finRange d).map σ.injective)
      (List.nodup_finRange d)).2 fun q => by simpa using ⟨σ.symm q, σ.apply_symm_apply q⟩
  exact ⟨eqToIso h ≪≫ (nonempty_twistList_iso_of_perm _ _ hperm _).some⟩

end IntersectionPermutation

/-! ### Capping the fundamental cycle with the module of an effective Cartier divisor -/

section Divisor

open Opposite

/-- The image of the canonical section `1_D` of `𝒪_Z(D)` under an isomorphism `𝒪_Z(D) ≅ M` is a
regular section of `M` whose zero scheme is `D` ([Stacks, Tag 01X0]). -/
theorem exists_isRegularSection_zeroScheme_eq {Z : Scheme.{u}} (D : Z.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (M : Z.Modules)
    [SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property M]
    (e : Stacks.Divisors.invertibleSheaf' D ≅ M) :
    ∃ s : M.sections, IsRegularSection Z.sheaf.obj Z.ringCatSheaf.property s ∧
      zeroScheme Z M (s.eval (op ⊤)) = D := by
  let P :=
    EffectiveCartierDivisor.regularSectionPair (⟨D, inferInstance⟩ : EffectiveCartierDivisor Z)
  let t := Stacks.Divisors.canonicalSection' D
  let s := SheafOfModules.sectionsMap e.hom t
  have hst : M.unitHomEquiv.symm s = P.module.unitHomEquiv.symm t ≫ e.hom :=
    (SheafOfModules.unitHomEquiv_symm_comp t e.hom).symm
  have hs : IsRegularSection Z.sheaf.obj Z.ringCatSheaf.property s := by
    have hP : Mono (P.module.unitHomEquiv.symm t) := P.regular
    change Mono (M.unitHomEquiv.symm s)
    rw [hst]
    exact @mono_comp _ _ _ _ _ _ hP _ (@IsIso.mono_of_iso _ _ _ _ _ (Iso.isIso_hom e))
  let Q : RegularSectionPair Z := ⟨M, inferInstance, s, hs⟩
  refine ⟨s, hs, ?_⟩
  have hPQ : P.IsIsomorphic Q := ⟨e, hst.symm⟩
  exact (RegularSectionPair.zeroScheme_eq_of_isIsomorphic hPQ).symm.trans
    (EffectiveCartierDivisor.zeroScheme_regularSectionPair _)

/-- A regular section is injective on every stalk: it is injective on the sections over every
open. -/
theorem injective_stalk_of_isRegularSection {Z : Scheme.{u}} {M : Z.Modules} (s : M.sections)
    (hs : IsRegularSection Z.sheaf.obj Z.ringCatSheaf.property s) (z : Z) :
    Function.Injective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map
        ((Scheme.Modules.toPresheaf Z).map (M.unitHomEquiv.symm s)))) :=
  TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective
    (fun U => Scheme.Modules.injective_unitHomEquiv_symm_app_of_isRegularSection M s hs U) z

variable (k : Type u) [Field k]

/-- The case of an effective Cartier divisor of Stacks 02SQ: if the restriction of `𝓛` to a closed
subscheme `Z` of dimension at most `d + 1` is `𝒪_Z(D)` for an effective Cartier divisor `D ⊆ Z`,
then `c₁(𝓛) ∩ [Z]_{d+1} = [D]_d`. -/
theorem firstChernClassCapOfInvertible_cycle_eq_of_iso_invertibleSheaf {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ)
    (hd : topologicalKrullDim Z ≤ (d + 1 : ℕ)) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (D : Z.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (hL : (Scheme.Modules.pullback i).obj L ≅ Stacks.Divisors.invertibleSheaf' D) :
    firstChernClassCapOfInvertible (fieldChowSituation k) f d L
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f i ((d : ℤ) + 1)) =
      QuotientAddGroup.mk
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f (D.subschemeι ≫ i) d) := by
  have : SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property
      ((Scheme.Modules.pullback i).obj L) :=
    isInvertible_sheaf_of_presheaf ((Scheme.Modules.pullback i).obj L)
  obtain ⟨s, hs, hz⟩ := exists_isRegularSection_zeroScheme_eq D _ hL.symm
  have hY : schemeDeltaDimension (fieldChowSituation k) (i ≫ f) ≤ ((d : ℤ) + 1 : EInt) := by
    have := schemeDeltaDimension_fieldChowSituation_le_of_topologicalKrullDim_le k f i (d + 1) hd
    exact this.trans_eq (by push_cast; rfl)
  have hDdim : topologicalKrullDim D.subscheme ≤ (d : WithBot ℕ∞) :=
    topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor_of_isProper k f i d hd D
  have hz' : Stacks.Divisors.zeroScheme Z ((Scheme.Modules.pullback i).obj L) (s.eval (op ⊤)) =
      D := hz
  subst hz'
  have hD := schemeDeltaDimension_fieldChowSituation_le_of_topologicalKrullDim_le k f
    ((Stacks.Divisors.zeroScheme Z ((Scheme.Modules.pullback i).obj L)
      (s.eval (op ⊤))).subschemeι ≫ i) d hDdim
  simp only [Category.assoc] at hD
  exact Stacks.ChernCap42.firstChernClassCapOfInvertible_closedSubscheme_eq_zeroScheme
    (fieldChowSituation k) f i (d : ℤ) L s hY hD
    (fun ξ _ => injective_stalk_of_isRegularSection s hs _)

end Divisor

/-! ### Dimension zero -/

section DimensionZero

variable (k : Type u) [Field k]

/-- The dimension of the ring of global sections of a scheme over a field is unchanged along an
isomorphism over the field. -/
theorem finrank_globalSections_eq_of_iso {Y Z : Scheme.{u}} (p : Y ⟶ Spec (.of k)) (e : Z ≅ Y) :
    letI : Algebra k Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom.toAlgebra
    letI : Algebra k Γ(Z, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (e.hom ≫ p).appTop).hom.toAlgebra
    Module.finrank k Γ(Z, ⊤) = Module.finrank k Γ(Y, ⊤) := by
  let : Algebra k Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom.toAlgebra
  let : Algebra k Γ(Z, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (e.hom ≫ p).appTop).hom.toAlgebra
  have : IsIso e.hom.appTop := Scheme.Hom.instIsIsoCommRingCatApp e.hom ⊤
  let φ : Γ(Y, ⊤) ≃+* Γ(Z, ⊤) := (asIso e.hom.appTop).commRingCatIsoToRingEquiv
  have hc : (algebraMap k Γ(Z, ⊤)).comp (RingEquiv.refl k).toRingHom =
      φ.toRingHom.comp (algebraMap k Γ(Y, ⊤)) := by
    ext a
    simp only [RingHom.comp_apply]
    change (((Scheme.ΓSpecIso (.of k)).inv ≫ (e.hom ≫ p).appTop).hom a) =
      (e.hom.appTop).hom (((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom a)
    rw [Scheme.Hom.comp_appTop]
    rfl
  exact (Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl k) φ hc).symm

/-- **The empty intersection number of a closed subscheme of dimension at most zero** is the
dimension of its ring of global sections: the higher cohomology of `𝒪_Z` vanishes by
[Stacks, Tag 0AYT] (3). -/
theorem intersectionNumber_zero_eq_finrank_globalSections {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (hd : topologicalKrullDim Z ≤ (0 : ℕ)) (L : Fin 0 → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] :
    intersectionNumber k f i 0 hd L =
      letI : Algebra k Γ(Z, ⊤) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (i ≫ f).appTop).hom.toAlgebra
      (Module.finrank k Γ(Z, ⊤) : ℤ) := by
  have : (SheafOfModules.unit Z.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (i ≫ f)
  have hsupp : topologicalKrullDim
      (_root_.SheafOfModules.supp (SheafOfModules.unit Z.ringCatSheaf)) ≤ 0 :=
    (topologicalKrullDim_supp_unit Z).le.trans (by simpa using hd)
  have hz : ∀ m : ℕ, 1 ≤ m →
      Module.finrank k (cohomologyOverField k (i ≫ f) (SheafOfModules.unit Z.ringCatSheaf) m)
        = 0 := fun m hm =>
    have := ModuleCat.subsingleton_of_isZero
      (isZero_cohomologyOverField_of_topologicalKrullDim_supp_le_zero k (i ≫ f) _ hsupp m hm)
    Module.finrank_zero_of_subsingleton
  rw [intersectionNumber_zero]
  change ∑ᶠ m : ℕ, (-1 : ℤ) ^ m *
      (Module.finrank k (cohomologyOverField k (i ≫ f)
        (SheafOfModules.unit Z.ringCatSheaf) m) : ℤ) = _
  rw [finsum_eq_sum_of_support_subset
    (f := fun m : ℕ => (-1 : ℤ) ^ m *
      (Module.finrank k (cohomologyOverField k (i ≫ f)
        (SheafOfModules.unit Z.ringCatSheaf) m) : ℤ))
    (s := Finset.range 1) fun m hm => ?_]
  · rw [Finset.sum_range_one, pow_zero, one_mul,
      finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections]
  · by_contra hn
    simp only [Finset.coe_range, Set.mem_Iio, not_lt] at hn
    simp [hz m hn] at hm

/-- The formula of [Stacks, Tag 0BFI] in dimension zero: for a closed subscheme `Z` of dimension at
most zero the empty intersection number `χ(Z, 𝒪_Z)` is the degree of the zero cycle `[Z]_0`. -/
theorem intersectionNumber_eq_capDegree_zero {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (hd : topologicalKrullDim Z ≤ (0 : ℕ)) (L : Fin 0 → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] :
    intersectionNumber k f i 0 hd L =
      capDegree k f L (QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) f 0)
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f i 0)) := by
  rw [capDegree_zero, intersectionNumber_zero_eq_finrank_globalSections]
  refine Eq.trans ?_ (chowDegree_mk (fieldChowSituation k)
    (fieldChowSituation_dimensionFunction_eq_zero k) f _ _).symm
  rw [cycleAssociatedToClosedSubscheme_ker]
  set I := i.ker
  let e : Z ≅ I.subscheme := asIso i.toImage
  have he : e.hom ≫ I.subschemeι = i := i.toImage_imageι
  have hdimI : topologicalKrullDim I.subscheme ≤ (0 : ℕ) := by
    rw [← IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph]
    exact hd
  have : IsFinite (I.subschemeι ≫ f) :=
    isFinite_of_isProper_of_topologicalKrullDim_le_zero _ (by simpa using hdimI)
  refine Eq.trans ?_ (cycleDegree_cycleAssociatedToClosedSubscheme_eq_finrank_globalSections k f I
    (schemeDeltaDimension_fieldChowSituation_le_of_topologicalKrullDim_le k f I.subschemeι 0
      hdimI) _).symm
  have h := finrank_globalSections_eq_of_iso k (I.subschemeι ≫ f) e
  rw [← Category.assoc, he] at h
  exact congrArg (fun n : ℕ => (n : ℤ)) h

end DimensionZero

/-! ### The inductive step at an effective Cartier divisor -/

section EffectiveStep

variable (k : Type u) [Field k]

/-- The intersection number depends on the family of modules only through its values. -/
theorem intersectionNumber_congr_family {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ) (hd : topologicalKrullDim Z ≤ d)
    {L M : Fin d → X.Modules} [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M j)] (h : L = M) :
    intersectionNumber k f i d hd L = intersectionNumber k f i d hd M := by
  subst h
  rfl

/-- The class of the cycle of a closed subscheme, transported along an equality of degrees, is
the class of its cycle in the other degree. -/
theorem chowGroupCast_mk_cycleAssociatedToClosedSubscheme {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i] {a b : ℤ}
    (h : a = b) :
    chowGroupCast (fieldChowSituation k) f h
        (QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) f a)
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f i a)) =
      QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) f b)
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f i b) := by
  subst h
  rfl

/-- `finRotate` sends `castSucc t` to `succ t`. -/
theorem finRotate_castSucc {d : ℕ} (t : Fin d) : finRotate (d + 1) t.castSucc = t.succ :=
  Fin.ext (by rw [coe_finRotate_of_ne_last (Fin.castSucc_ne_last t)]; simp)

/-- The inductive step of [Stacks, Tag 0BFI] at an effective Cartier divisor: granted the
formula in dimension `d`, it holds for a closed subscheme `Z` of dimension at most `d + 1` and
a family of `d + 1` modules whose last one restricts on `Z` to `𝒪_Z(D)` for an effective
Cartier divisor `D ⊆ Z`: both sides are then the corresponding numbers for `D` and the first `d`
modules, by [Stacks, Tag 0BEU] numerically and by Stacks 02SQ on the side of the Chow groups. -/
theorem intersectionNumber_eq_capDegree_of_isEffectiveCartierDivisor (d : ℕ)
    (ih : ∀ {X' Z' : Scheme.{u}} (f' : X' ⟶ Spec (.of k)) [IsProper f'] (i' : Z' ⟶ X')
      [IsClosedImmersion i'] (hd' : topologicalKrullDim Z' ≤ (d : ℕ)) (L' : Fin d → X'.Modules)
      [∀ j, SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2 (L' j)],
      intersectionNumber k f' i' d hd' L' =
        capDegree k f' L' (QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) f' d)
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f' i' d)))
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (hd : topologicalKrullDim Z ≤ (d + 1 : ℕ)) (L : Fin (d + 1) → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    (D : Z.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (hL : (Scheme.Modules.pullback i).obj (L (Fin.last d)) ≅ Stacks.Divisors.invertibleSheaf' D) :
    intersectionNumber k f i (d + 1) hd L =
      capDegree k f L (QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) f _)
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f i ((d + 1 : ℕ) : ℤ))) := by
  -- the numerical side: rotate the last module to the front and apply Tag 0BEU
  set σ : Equiv.Perm (Fin (d + 1)) := (finRotate (d + 1)).symm with hσ
  have hσ0 : σ 0 = Fin.last d := by
    rw [hσ, Equiv.symm_apply_eq, finRotate_last]
  have hσs : ∀ t : Fin d, σ t.succ = t.castSucc := fun t => by
    rw [hσ, Equiv.symm_apply_eq, finRotate_castSucc]
  have : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L (σ j)) :=
    fun j => inferInstance
  have hL' : (Scheme.Modules.pullback i).obj (L (σ 0)) ≅ Stacks.Divisors.invertibleSheaf D :=
    eqToIso (by rw [hσ0]) ≪≫ hL
  have hD := topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor_of_isProper k f i d hd D
  rw [← intersectionNumber_comp_perm k f i (d + 1) hd L σ,
    intersectionNumber_eq_of_isEffectiveCartierDivisor k f i d hd (fun j => L (σ j)) D hD hL',
    intersectionNumber_congr_family k f (D.subschemeι ≫ i) d hD
      (M := fun t : Fin d => L t.castSucc) (funext fun t => by simp only [hσs]),
    ih f (D.subschemeι ≫ i) hD (fun t : Fin d => L t.castSucc)]
  -- the side of the Chow groups: peel off the last cap and apply Stacks 02SQ
  rw [capDegree_succ, chowGroupCast_mk_cycleAssociatedToClosedSubscheme, invCap_capOnChow_mk,
    firstChernClassCapOfInvertible_cycle_eq_of_iso_invertibleSheaf k f i d hd (L (Fin.last d)) D hL]
  rfl

end EffectiveStep

/-! ### The case of a scheme carrying an ample invertible module -/

section AmpleCase

variable (k : Type u) [Field k]

/-- The degree of the iterated cap depends on the family of modules only through its values. -/
theorem capDegree_congr_family {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] {d : ℕ}
    {L M : Fin d → X.Modules} [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M j)] (h : L = M) :
    capDegree k f L = capDegree k f M := by
  subst h
  rfl

/-- **Peeling off the innermost cap on the class of a closed subscheme.** -/
theorem capDegree_succ_mk {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X)
    [IsClosedImmersion i] {d : ℕ} (L : Fin (d + 1) → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] :
    capDegree k f L (QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) f _)
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f i ((d + 1 : ℕ) : ℤ))) =
      capDegree k f (fun j : Fin d => L j.castSucc)
        (firstChernClassCapOfInvertible (fieldChowSituation k) f d (L (Fin.last d))
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f i ((d : ℤ) + 1))) := by
  rw [capDegree_succ, chowGroupCast_mk_cycleAssociatedToClosedSubscheme, invCap_capOnChow_mk]

/-- The formula of [Stacks, Tag 0BFI] on a scheme carrying an ample invertible module, granted the
formula in dimension `d`. By [Stacks, Tag 0AYM] the last module is `𝒪(D) ⊗ 𝒪(D')^{⊗ -1}` for
effective Cartier divisors `D`, `D'`; both sides are additive in that module ([Stacks, Tag 0BER] and
Stacks 02SP) and invariant under isomorphism, so the formula follows from the inductive step at the
two effective Cartier divisors. -/
theorem intersectionNumber_eq_capDegree_of_isAmple (d : ℕ)
    (ih : ∀ {X' Z' : Scheme.{u}} (f' : X' ⟶ Spec (.of k)) [IsProper f'] (i' : Z' ⟶ X')
      [IsClosedImmersion i'] (hd' : topologicalKrullDim Z' ≤ (d : ℕ)) (L' : Fin d → X'.Modules)
      [∀ j, SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2 (L' j)],
      intersectionNumber k f' i' d hd' L' =
        capDegree k f' L' (QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) f' d)
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f' i' d)))
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k)) [IsProper g]
    (hY : topologicalKrullDim Y ≤ (d + 1 : ℕ)) (A : Y.Modules)
    [Stacks.Ample.IsInvertibleModule Y A] (hA : Stacks.Ample.IsAmple Y A)
    (M : Fin (d + 1) → Y.Modules)
    [∀ j, SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 (M j)] :
    intersectionNumber k g (𝟙 Y) (d + 1) hY M =
      capDegree k g M (QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) g _)
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) g (𝟙 Y) ((d + 1 : ℕ) : ℤ))) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace g
  have : IsNoetherian Y := ⟨⟩
  have : Stacks.Ample.IsInvertibleModule Y (M (Fin.last d)) :=
    (inferInstance : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 (M (Fin.last d)))
  obtain ⟨D, D', hD, hD', -, -, ⟨e⟩⟩ :=
    InvertibleSheafGeneral.exists_effectiveCartierDivisors_tensor_invertibleSheaf A hA
      (M (Fin.last d)) (Set.finite_empty)
  have : Stacks.Divisors.IsEffectiveCartierDivisor D := hD
  have : Stacks.Divisors.IsEffectiveCartierDivisor D' := hD'
  set OD : Y.Modules := Stacks.Divisors.invertibleSheaf' D with hOD
  set OD' : Y.Modules := Stacks.Divisors.invertibleSheaf' D' with hOD'
  have hinvD : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 OD :=
    Stacks.Divisors.invertibleSheaf_isInvertible D
  have hinvD' : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 OD' :=
    Stacks.Divisors.invertibleSheaf_isInvertible D'
  set T : Y.Modules := Scheme.Modules.tensorObj (M (Fin.last d)) OD' with hT
  have hinvT : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 T :=
    Stacks.SheafOfModules.isInvertible_tensorSheaf _ _ _ _
  -- the isomorphism of Tag 0AYM at the spelling of the tensor product sheaf
  have e' : T ≅ OD :=
    let := Stacks.SheafInternalHom.schemeMonoidalCategory Y
    (Stacks.TensorSheafSpellingIso.monoidalTensorIso Y _ _).symm ≪≫ e
  have hoff : ∀ (N : Y.Modules) (q : Fin (d + 1)), q ≠ Fin.last d →
      Function.update M (Fin.last d) N q = M q := fun N q hq => Function.update_of_ne hq _ _
  have hupd : ∀ (N : Y.Modules), Function.update M (Fin.last d) N (Fin.last d) = N :=
    fun N => Function.update_self _ _ _
  have : ∀ j, SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (Function.update M (Fin.last d) OD j) := isInvertible_update M _ _
  have : ∀ j, SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (Function.update M (Fin.last d) OD' j) := isInvertible_update M _ _
  have : ∀ j, SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (Function.update M (Fin.last d) T j) := isInvertible_update M _ _
  -- the numerical side
  have h₁ := intersectionNumber_tensor k g (𝟙 Y) (d + 1) hY (Fin.last d)
    (Function.update M (Fin.last d) T) M (Function.update M (Fin.last d) OD')
    (fun q hq => (hoff _ q hq).symm) (fun q hq => (hoff _ q hq).trans (hoff _ q hq).symm)
    (eqToIso (hupd T) ≪≫ eqToIso (congrArg (Scheme.Modules.tensorObj (M (Fin.last d)))
      (hupd OD').symm))
  have h₂ := intersectionNumber_eq_of_iso_at k g (𝟙 Y) (d + 1) hY
    (Function.update M (Fin.last d) T) (Function.update M (Fin.last d) OD) (Fin.last d)
    (fun q hq => (hoff _ q hq).trans (hoff _ q hq).symm)
    (eqToIso (hupd T) ≪≫ e' ≪≫ eqToIso (hupd OD).symm)
  -- the side of the Chow groups
  have hcast : ∀ N : Y.Modules, (fun j : Fin d => Function.update M (Fin.last d) N j.castSucc) =
      fun j => M j.castSucc := fun N => funext fun j => hoff _ _ (Fin.castSucc_ne_last j)
  have hc₁ := firstChernClassCapOfInvertible_tensorObj (fieldChowSituation k) g d
    (M (Fin.last d)) OD'
    (cycleAssociatedToClosedSubscheme (fieldChowSituation k) g (𝟙 Y) ((d : ℤ) + 1))
  have hc₂ := firstChernClassCapOfInvertible_congr (fieldChowSituation k) g d _ _ e'
    (cycleAssociatedToClosedSubscheme (fieldChowSituation k) g (𝟙 Y) ((d : ℤ) + 1))
  have hED : ∀ (N : Y.Modules) (E : Y.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor E]
      [∀ j, SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
        (Function.update M (Fin.last d) N j)]
      [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 N]
      (_ : N ≅ Stacks.Divisors.invertibleSheaf' E),
      intersectionNumber k g (𝟙 Y) (d + 1) hY (Function.update M (Fin.last d) N) =
        capDegree k g (fun j : Fin d => M j.castSucc)
          (firstChernClassCapOfInvertible (fieldChowSituation k) g d N
            (cycleAssociatedToClosedSubscheme (fieldChowSituation k) g (𝟙 Y) ((d : ℤ) + 1))) := by
    intro N E _ _ _ e
    have := intersectionNumber_eq_capDegree_of_isEffectiveCartierDivisor k d ih g (𝟙 Y) hY
      (Function.update M (Fin.last d) N) E
      ((Scheme.Modules.pullbackId Y).app _ ≪≫ eqToIso (hupd N) ≪≫ e)
    rwa [capDegree_succ_mk, capDegree_congr_family k g (hcast _),
      firstChernClassCapOfInvertible_congr (fieldChowSituation k) g d _ _ (eqToIso (hupd _))]
      at this
  rw [capDegree_succ_mk]
  have hsplit : intersectionNumber k g (𝟙 Y) (d + 1) hY M =
      intersectionNumber k g (𝟙 Y) (d + 1) hY (Function.update M (Fin.last d) OD) -
        intersectionNumber k g (𝟙 Y) (d + 1) hY (Function.update M (Fin.last d) OD') := by
    omega
  rw [hsplit, hED OD D (Iso.refl _), hED OD' D' (Iso.refl _), ← map_sub, ← hc₂, ← hc₁,
    add_sub_cancel_right]

end AmpleCase

/-! ### Chow's lemma for a proper integral scheme over a field -/

section ChowLemma

variable (k : Type u) [Field k]

/-- **Chow's lemma for a proper integral scheme over a field** ([Stacks, Tags 0200 and 0201]): an
integral scheme `W` proper over `k` is dominated by an integral scheme `Y` immersed in a
projective space over `k`, through a proper surjective morphism which is an isomorphism over a
nonempty open subscheme of `W`. -/
@[sga "4½ Arcata 3.4.3" "partial"]
theorem exists_integral_chowModification {W : Scheme.{u}} [IsIntegral W]
    (g : W ⟶ Spec (.of k)) [IsProper g] :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ W) (n : ℕ) (j : Y ⟶ ProjectiveSpace n (Spec (.of k)))
      (U : W.Opens), IsIntegral Y ∧ IsProper π ∧ Surjective π ∧ IsImmersion j ∧
        π ≫ g = j ≫ (ProjectiveSpace n (Spec (.of k)) ↘ Spec (.of k)) ∧
        (U : Set W).Nonempty ∧ IsIso (π ∣_ U) := by
  obtain ⟨n, X', π, i, U, hπ, -, himm, hcomm, hU, hiso⟩ := hasDenseChowModification g
  obtain ⟨Y, ρ, j, hρ, hsurj, hj, hcomm', -, hiso', hdense, hred⟩ :=
    exists_isReduced_chowModification g π i U hcomm hU hiso
  have hUne : (U : Set W).Nonempty := hU.nonempty
  have : Nonempty U := hUne.to_subtype
  have : IsIso (ρ ∣_ U) := hiso'
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have : IsIntegral (ρ ⁻¹ᵁ U).toScheme := IsIntegral.of_isIso (inv (ρ ∣_ U))
  have hV : Dense ((ρ ⁻¹ᵁ U : Y.Opens) : Set Y) := dense_of_isSchemeTheoreticallyDense _ hdense
  have hirr : IsIrreducible ((ρ ⁻¹ᵁ U : Y.Opens) : Set Y) := by
    have h := (IrreducibleSpace.isIrreducible_univ (ρ ⁻¹ᵁ U).toScheme).image
      (ρ ⁻¹ᵁ U).ι.base (ρ ⁻¹ᵁ U).ι.base.hom.continuous.continuousOn
    simpa only [Set.image_univ, Scheme.Opens.range_ι] using h
  have : IrreducibleSpace Y := by
    refine (irreducibleSpace_def _).mpr ?_
    simpa only [hV.closure_eq, Set.top_eq_univ] using hirr.closure
  have : IsReduced Y := hred
  exact ⟨Y, ρ, n, j, U, isIntegral_of_irreducibleSpace_of_isReduced Y, hρ, hsurj, hj, hcomm',
    hUne, hiso'⟩

/-- A morphism inducing an isomorphism of local rings at a point has residue degree one there. -/
theorem residueDegree_eq_one_of_isIso_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    [IsIso (f.stalkMap x)] : f.residueDegree x = 1 := by
  let : Algebra (Y.residueField (f x)) (X.residueField x) := (f.residueFieldMap x).hom.toAlgebra
  have hsurj : Function.Surjective (f.residueFieldMap x) := by
    intro b
    obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective (R := X.presheaf.stalk x) b
    obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (f.stalkMap x)).2 c
    exact ⟨Y.residue (f x) a, ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap f x) a⟩
  change Module.finrank (Y.residueField (f x)) (X.residueField x) = 1
  exact Module.finrank_of_bijective_algebraMap ⟨(f.residueFieldMap x).hom.injective, hsurj⟩

/-- **A proper surjective morphism of integral schemes over a field which is an isomorphism over a
nonempty open subscheme preserves the dimension.** Both dimensions are the dimension of the local
ring at a closed point over that open ([Stacks, Tag 02QO]), and the two local rings are
isomorphic. -/
theorem topologicalKrullDim_eq_of_isIso_morphismRestrict {Y W : Scheme.{u}} [IsIntegral Y]
    [IsIntegral W] (g : W ⟶ Spec (.of k)) [LocallyOfFiniteType g] (π : Y ⟶ W) [IsProper π]
    (U : W.Opens) (hU : (U : Set W).Nonempty) [Surjective π] [IsIso (π ∣_ U)] :
    topologicalKrullDim Y = topologicalKrullDim W := by
  have hδ : ∀ s : (fieldChowSituation k).S, IsClosed ({s} : Set (fieldChowSituation k).S) →
      (fieldChowSituation k).dimensionFunction s = 0 := fun _ _ => rfl
  have : JacobsonSpace (fieldChowSituation k).S :=
    inferInstanceAs (JacobsonSpace (Spec (.of k)))
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace (π ≫ g)
  have hV : ((π ⁻¹ᵁ U : Y.Opens) : Set Y).Nonempty := by
    obtain ⟨w, hw⟩ := hU
    obtain ⟨y, rfl⟩ := π.surjective w
    exact ⟨y, hw⟩
  obtain ⟨y, hy, hclosed⟩ := nonempty_inter_closedPoints hV (π ⁻¹ᵁ U).isOpen.isLocallyClosed
  have hclosed' : IsClosed ({π y} : Set W) := by
    simpa only [Set.image_singleton] using π.isClosedMap _ hclosed
  have := isIso_stalkMap_of_isIso_morphismRestrict π (U := U) inferInstance hy
  rw [topologicalKrullDim_eq_ringKrullDim_stalk_of_isClosed (fieldChowSituation k) hδ
      (π ≫ g) (𝟙 Y) y hclosed,
    topologicalKrullDim_eq_ringKrullDim_stalk_of_isClosed (fieldChowSituation k) hδ
      g (𝟙 W) (π y) hclosed']
  exact (ringKrullDim_eq_of_ringEquiv (asIso (π.stalkMap y)).commRingCatIsoToRingEquiv).symm

/-- A scheme proper over a field and immersed in a projective space over it carries an ample
invertible module ([Stacks, Tags 01VY and 01VK]). -/
theorem exists_isAmple_of_isImmersion {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k)) [IsProper g] (n : ℕ)
    (j : Y ⟶ ProjectiveSpace n (Spec (.of k))) [IsImmersion j]
    (hj : j ≫ (ProjectiveSpace n (Spec (.of k)) ↘ Spec (.of k)) = g) :
    ∃ (A : Y.Modules) (_ : Stacks.Ample.IsInvertibleModule Y A), Stacks.Ample.IsAmple Y A := by
  have : IsSeparated (ProjectiveSpace n (Spec (.of k)) ↘ Spec (.of k)) :=
    Stacks.HProjective.isSeparated_over n _
  have : QuasiCompact (j ≫ (ProjectiveSpace n (Spec (.of k)) ↘ Spec (.of k))) := by
    rw [hj]; infer_instance
  have hjqc : QuasiCompact j :=
    QuasiCompact.of_comp j (ProjectiveSpace n (Spec (.of k)) ↘ Spec (.of k))
  obtain ⟨-, A, hA, ha⟩ := Stacks.HProjective.isQuasiProjective_of_isHQuasiProjective g
    ⟨n, j, ‹IsImmersion j›, hjqc, hj⟩
  exact ⟨A, hA, (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple g A).mp ha⟩

end ChowLemma

/-! ### The case of an integral closed subscheme -/

section IntegralCase

variable (k : Type u) [Field k]

/-- The intersection number against a closed subscheme cut out by an ideal sheaf depends only on
that ideal sheaf. -/
theorem intersectionNumber_congr_ideal {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    {I J : X.IdealSheafData} (h : I = J) (d : ℕ) (hI : topologicalKrullDim I.subscheme ≤ d)
    (hJ : topologicalKrullDim J.subscheme ≤ d) (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] :
    intersectionNumber k f I.subschemeι d hI L = intersectionNumber k f J.subschemeι d hJ L := by
  subst h
  rfl

/-- The formula of [Stacks, Tag 0BFI] for an integral closed subscheme of dimension `d + 1`, granted
the formula in dimension `d`. By Chow's lemma ([Stacks, Tags 0200 and 0201]) the subscheme `W` is
dominated by an integral scheme `Y` immersed in a projective space, birationally; both sides are
unchanged by pulling back to `Y` — the intersection number by [Stacks, Tag 0BET], the degree of the
cap product by the projection formula of Stacks 02SU — and `Y` carries an ample invertible module,
which is the case of `AlgebraicGeometry.intersectionNumber_eq_capDegree_of_isAmple`. -/
theorem intersectionNumber_eq_capDegree_of_isIntegral (d : ℕ)
    (ih : ∀ {X' Z' : Scheme.{u}} (f' : X' ⟶ Spec (.of k)) [IsProper f'] (i' : Z' ⟶ X')
      [IsClosedImmersion i'] (hd' : topologicalKrullDim Z' ≤ (d : ℕ)) (L' : Fin d → X'.Modules)
      [∀ j, SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2 (L' j)],
      intersectionNumber k f' i' d hd' L' =
        capDegree k f' L' (QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) f' d)
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f' i' d)))
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (W : X.IdealSheafData)
    [IsIntegral W.subscheme] (hW : topologicalKrullDim W.subscheme = (d + 1 : ℕ))
    (L : Fin (d + 1) → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] :
    intersectionNumber k f W.subschemeι (d + 1) hW.le L =
      capDegree k f L (QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) f _)
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f W.subschemeι
          ((d + 1 : ℕ) : ℤ))) := by
  obtain ⟨Y, π, n, j, U, hYi, hπ, hsurj, hj, hcomm, hU, hiso⟩ :=
    exists_integral_chowModification k (W.subschemeι ≫ f)
  have := hYi; have := hπ; have := hsurj; have := hj; have := hiso
  have : IsDominant π := inferInstance
  have hYdim : topologicalKrullDim Y = (d + 1 : ℕ) :=
    (topologicalKrullDim_eq_of_isIso_morphismRestrict k (W.subschemeι ≫ f) π U hU).trans hW
  -- the ample invertible module on `Y`
  have hjg : j ≫ (ProjectiveSpace n (Spec (.of k)) ↘ Spec (.of k)) =
      (π ≫ W.subschemeι) ≫ f := by rw [Category.assoc, hcomm]
  obtain ⟨A, hAinv, hA⟩ := exists_isAmple_of_isImmersion k ((π ≫ W.subschemeι) ≫ f) n j hjg
  have hAmple := intersectionNumber_eq_capDegree_of_isAmple k d ih ((π ≫ W.subschemeι) ≫ f)
    hYdim.le A hA (fun j => (Scheme.Modules.pullback (π ≫ W.subschemeι)).obj (L j))
  -- the scheme-theoretic image of `Y` in `X` is `W`
  have := IsSchemeTheoreticallyDominant.of_isDominant π
  have hker : (𝟙 Y ≫ π ≫ W.subschemeι).ker = W := by
    rw [Category.id_comp, Scheme.Hom.ker_comp, π.ker_eq_bot,
      Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι]
  have hIm : topologicalKrullDim (𝟙 Y ≫ π ≫ W.subschemeι).image = (d + 1 : ℕ) := by
    change topologicalKrullDim (𝟙 Y ≫ π ≫ W.subschemeι).ker.subscheme = _
    rw [hker]; exact hW
  -- the degree of `Y` over `W` is one
  have : IsIntegral (𝟙 Y ≫ π ≫ W.subschemeι).image :=
    Stacks.Chow.isIntegral_image (𝟙 Y ≫ π ≫ W.subschemeι)
  have : IsProper (𝟙 Y ≫ π ≫ W.subschemeι).toImage :=
    Stacks.Chow.isProper_toImage (𝟙 Y ≫ π ≫ W.subschemeι)
  have hgen : π (genericPoint Y) ∈ U := by
    rw [Stacks.Divisors.base_genericPoint_of_isDominant π]
    exact ((genericPoint_spec W.subscheme).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  have := isIso_stalkMap_of_isIso_morphismRestrict π (U := U) inferInstance hgen
  have hdegπ : degreeOver π = 1 := by
    rw [degreeOver, finrank_functionField_eq_residueDegree π,
      residueDegree_eq_one_of_isIso_stalkMap π (genericPoint Y)]
  have hdeg : degreeOver (𝟙 Y ≫ π ≫ W.subschemeι).toImage = 1 := by
    rw [← degreeOver_eq_degreeOver_of_isIso π (𝟙 Y ≫ π ≫ W.subschemeι).toImage
      (eqToHom (congrArg Scheme.IdealSheafData.subscheme hker)) ?_, hdegπ]
    have key : ∀ {I J : X.IdealSheafData} (h : I = J),
        eqToHom (congrArg Scheme.IdealSheafData.subscheme h) ≫ J.subschemeι = I.subschemeι := by
      intro I J h; subst h; simp
    rw [← cancel_mono W.subschemeι, Category.assoc, key hker]
    exact (𝟙 Y ≫ π ≫ W.subschemeι).toImage_imageι.trans (Category.id_comp _)
  -- the numerical side, by Tag 0BET
  have hpull := intersectionNumber_pullback_eq_degreeOver_mul k ((π ≫ W.subschemeι) ≫ f) f
    (π ≫ W.subschemeι) rfl (𝟙 Y) (d + 1) hYdim L hIm
  rw [hdeg, Nat.cast_one, one_mul] at hpull
  rw [← intersectionNumber_congr_ideal k f hker (d + 1) hIm.le hW.le L, ← hpull, hAmple,
    capDegree_properChowPushforward k f ((π ≫ W.subschemeι) ≫ f) (π ≫ W.subschemeι) rfl L,
    properChowPushforward_mk]
  -- the side of the Chow groups: `Y` pushes forward to `W`
  congr 2
  have hnY := schemeDeltaDimension_fieldChowSituation_eq_of_topologicalKrullDim_eq
    (k := k) ((π ≫ W.subschemeι) ≫ f) hYdim
  have hnW := schemeDeltaDimension_fieldChowSituation_eq_of_topologicalKrullDim_eq
    (k := k) (W.subschemeι ≫ f) hW
  rw [← properPushforward_properPushforward (fieldChowSituation k) ((π ≫ W.subschemeι) ≫ f)
    (W.subschemeι ≫ f) f π W.subschemeι (Category.assoc _ _ _).symm rfl,
    properPushforward_fundamentalCycle (fieldChowSituation k) ((π ≫ W.subschemeι) ≫ f)
      (W.subschemeι ≫ f) hnY hnW π (Category.assoc _ _ _).symm]
  have hone : (letI : Algebra W.subscheme.functionField Y.functionField :=
      (dominantFunctionFieldMap π).toAlgebra
    (Module.finrank W.subscheme.functionField Y.functionField : ℤ)) = 1 := by
    exact_mod_cast hdegπ
  rw [hone, one_smul, properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp
    (fieldChowSituation k) (W.subschemeι ≫ f) f W.subschemeι rfl (𝟙 W.subscheme)]
  exact cycleAssociatedToClosedSubscheme_of_hom_eq (fieldChowSituation k) f
    (Category.id_comp W.subschemeι) _

end IntegralCase

/-! ### The cycle of a closed subscheme as a sum over its components -/

section Components

variable (k : Type u) [Field k]

/-- A closed subscheme of dimension at most `d` of a scheme proper over a field has finitely many
integral closed subschemes of dimension `d`: none if its dimension is smaller, and otherwise
they are its top-dimensional components. -/
theorem finite_dimIntegralSubscheme {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ) (hd : topologicalKrullDim Z ≤ (d : WithBot ℕ∞)) :
    Finite (DimIntegralSubscheme
      ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)) d) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  have hdimF : topologicalKrullDim (_root_.SheafOfModules.supp
      ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z))) =
      topologicalKrullDim Z := by
    rw [Stacks.Chow.supp_pushforwardStructureSheaf i, topologicalKrullDim_range_eq i]
  rcases lt_or_eq_of_le hd with hlt | heq
  · have := isEmpty_dimIntegralSubscheme_of_topologicalKrullDim_lt _ (hdimF.trans_lt hlt)
    infer_instance
  · have := finite_topDimIntegralSubscheme k f
      ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z))
    exact Finite.of_injective (β := TopDimIntegralSubscheme
        ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)))
      (fun W => ⟨W.1, W.2.1, W.2.2.1, by rw [hdimF, heq]; exact W.2.2.2⟩)
      (fun W W' h => Subtype.ext (by simpa using congrArg Subtype.val h))

/-- The integral closed subscheme attached to a point of a scheme locally of finite type over a
field has, as dimension, the relative dimension of that point. -/
theorem topologicalKrullDim_integralComponentAt {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : X) {n : ℕ}
    (hx : relativeDimension (fieldChowSituation k).dimensionFunction f x = n) :
    topologicalKrullDim (integralComponentAt x).subscheme = (n : WithBot ℕ∞) := by
  have : IsIntegral (integralComponentAt x).subscheme := isIntegral_integralComponentAt x
  have hδ := schemeDeltaDimension_integralComponentAt (fieldChowSituation k) f x
  rw [hx] at hδ
  have : JacobsonSpace (fieldChowSituation k).S :=
    inferInstanceAs (JacobsonSpace (Spec (.of k)))
  have hle : topologicalKrullDim (integralComponentAt x).subscheme ≤ (n : WithBot ℕ∞) :=
    topologicalKrullDim_le_of_schemeDeltaDimension_le (fieldChowSituation k) (fun _ _ => rfl)
      ((integralComponentAt x).subschemeι ≫ f) n hδ.le
  obtain ⟨m, hm⟩ : ∃ m : ℕ, topologicalKrullDim (integralComponentAt x).subscheme = m := by
    have hne : topologicalKrullDim (integralComponentAt x).subscheme ≠ ⊥ := by
      rw [Ne, topologicalKrullDim_eq_bot_iff_isEmpty]; exact not_isEmpty_of_nonempty _
    obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp hne
    have hat : a ≠ ⊤ := by
      rintro rfl
      rw [← ha] at hle
      have h2 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) := hle
      exact ENat.natCast_ne_top n (top_le_iff.mp (WithBot.coe_le_coe.mp h2))
    obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp hat
    exact ⟨m, ha.symm⟩
  have hδ' := schemeDeltaDimension_fieldChowSituation_eq_of_topologicalKrullDim_eq (k := k)
    ((integralComponentAt x).subschemeι ≫ f) hm
  rw [hδ] at hδ'
  have : (n : ℤ) = m := WithBotTop.coe_injective hδ'
  rw [hm]; exact_mod_cast this.symm

/-- **The cycle of a closed subscheme as a sum over its components**: for a closed subscheme
`Z` of dimension at most `d` with irreducible components `Z_i` of dimension `d` and
multiplicities `m_i`, `[Z]_d = ∑ m_i [Z_i]`. -/
theorem cycleAssociatedToClosedSubscheme_eq_finsum_dimComponents {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ)
    (hd : topologicalKrullDim Z ≤ (d : WithBot ℕ∞)) :
    cycleAssociatedToClosedSubscheme (fieldChowSituation k) f i d =
      ∑ᶠ W : DimIntegralSubscheme
          ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)) d,
        Stacks.Chow.sheafMultiplicity
            ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)) W.genericPt •
          cycleAssociatedToClosedSubscheme (fieldChowSituation k) f W.1.subschemeι d := by
  classical
  have := finite_dimIntegralSubscheme k f i d hd
  have : Fintype (DimIntegralSubscheme
      ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)) d) := Fintype.ofFinite _
  have hZ := schemeDeltaDimension_fieldChowSituation_le_of_topologicalKrullDim_le k f i d hd
  have h02QY := cycleAssociatedToClosedSubscheme_eq_cycleAssociatedToCoherentSheaf
    (fieldChowSituation k) f i (d : ℤ) hZ
  rw [h02QY, finsum_eq_sum_of_fintype]
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x => ?_)
  rw [cycleAssociatedToCoherentSheaf_apply]
  simp only [AddSubgroup.val_finsetSum, AddSubgroup.coe_zsmul,
    Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply,
    Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply, smul_eq_mul]
  -- the coefficients of the cycle of a `d`-dimensional integral closed subscheme
  have hgen : ∀ W : DimIntegralSubscheme
      ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)) d,
      relativeDimension (fieldChowSituation k).dimensionFunction f W.genericPt = d := by
    intro W
    have := W.2.1
    rw [DimIntegralSubscheme.genericPt, ← relativeDimension_comp_closedImmersion]
    exact relativeDimension_fieldChowSituation_genericPoint (W.1.subschemeι ≫ f) W.2.2.2
  have hcoef : ∀ W : DimIntegralSubscheme
      ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)) d,
      (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f W.1.subschemeι d).1 x =
        if x = W.genericPt then 1 else 0 := by
    intro W
    have := W.2.1
    split_ifs with hx
    · subst hx
      exact cycleAssociatedToClosedSubscheme_isIntegral_apply_genericPoint (fieldChowSituation k)
        f W.1.subschemeι (d : ℤ) (hgen W)
    · exact cycleAssociatedToClosedSubscheme_isIntegral_apply_of_ne (fieldChowSituation k) f
        W.1.subschemeι (d : ℤ) hx
  simp only [hcoef, mul_ite, mul_one, mul_zero]
  -- the generic point determines the component
  have hinj : ∀ W W' : DimIntegralSubscheme
      ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)) d,
      W.genericPt = W'.genericPt → W = W' := by
    intro W W' h
    refine Subtype.ext ?_
    rw [← integralComponentAt_genericPointOf W.1 W.2.1,
      ← integralComponentAt_genericPointOf W'.1 W'.2.1]
    exact congrArg integralComponentAt h
  split_ifs with hx
  · -- `x` is the generic point of the component it spans
    let W : DimIntegralSubscheme
        ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)) d :=
      ⟨integralComponentAt x, isIntegral_integralComponentAt x, by
        rw [coe_support_integralComponentAt, Stacks.Chow.supp_pushforwardStructureSheaf i]
        refine i.isClosedEmbedding.isClosed_range.closure_subset_iff.mpr
          (Set.singleton_subset_iff.mpr ?_)
        have hx1 := hx.1
        rwa [Stacks.Chow.supp_pushforwardStructureSheaf i] at hx1,
        topologicalKrullDim_integralComponentAt k f x hx.2⟩
    have hWx : W.genericPt = x := genericPointOf_integralComponentAt x
    rw [Finset.sum_eq_single W]
    · rw [ite_eq_left hWx.symm, hWx]
    · intro W' _ hW'
      rw [ite_eq_right]
      intro h
      exact hW' (hinj W' W (h.symm.trans hWx.symm))
    · simp
  · refine (Finset.sum_eq_zero fun W _ => ?_).symm
    rw [ite_eq_right]
    rintro rfl
    refine hx ⟨W.2.2.1 ?_, hgen W⟩
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨_, rfl⟩

end Components

/-! ### The main theorem -/

section Main

variable (k : Type u) [Field k]

/-- The formula of [Stacks, Tag 0BFI] for a closed subscheme of dimension at most `d`, by induction
on `d`: dimension zero is [Stacks, Tag 0AYT]; in positive dimension both sides are the weighted sums
over the `d`-dimensional components ([Stacks, Tag 0BES] and the decomposition of `[Z]_d`), and for
an integral component the formula is
`AlgebraicGeometry.intersectionNumber_eq_capDegree_of_isIntegral`. -/
theorem intersectionNumber_eq_capDegree_of_le (d : ℕ) {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (hd : topologicalKrullDim Z ≤ (d : ℕ)) (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] :
    intersectionNumber k f i d hd L =
      capDegree k f L (QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) f d)
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f i d)) := by
  induction d generalizing X Z with
  | zero => exact intersectionNumber_eq_capDegree_zero k f i hd L
  | succ d ih =>
    classical
    have := finite_dimIntegralSubscheme k f i (d + 1) hd
    have : Fintype (DimIntegralSubscheme
        ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)) (d + 1)) :=
      Fintype.ofFinite _
    rw [intersectionNumber_eq_sum_dimComponents k f i (d + 1) hd L,
      cycleAssociatedToClosedSubscheme_eq_finsum_dimComponents k f i (d + 1) hd,
      finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum, map_sum]
    refine Finset.sum_congr rfl fun W _ => ?_
    have := W.2.1
    rw [map_zsmul, map_zsmul, smul_eq_mul,
      intersectionNumber_eq_capDegree_of_isIntegral k d ih
        f W.1 W.2.2.2 L]

/-- Let `k` be a field, let `X` be a proper scheme over `k`, let `Z ⊆ X` be a closed subscheme of
dimension `d` and let `𝓛_1, …, 𝓛_d` be invertible `𝒪_X`-modules. Then

`(𝓛_1 ⋯ 𝓛_d · Z) = deg(c₁(𝓛_1) ∩ ⋯ ∩ c₁(𝓛_d) ∩ [Z]_d)`,

the left-hand side being the intersection number of [Stacks, Tag 0BEP] and the degree that of
[Stacks, Tag 0AZ1], for the Chow groups over `Spec k` with its zero dimension function. -/
theorem intersectionNumber_eq_chowDegree_iteratedFirstChernCap {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ)
    (dimZ : topologicalKrullDim Z = d) (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] :
    intersectionNumber k f i d dimZ.le L =
      chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k) f
        (IsLocalRing.closedPoint k)
        (iteratedFirstChernCap k f L
          (QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) f d)
            (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f i d))) :=
  intersectionNumber_eq_capDegree_of_le k d f i dimZ.le L

/-- For an ample invertible `𝒪_X`-module `𝓛` on a proper scheme `X` over `k` and a closed
subscheme `Z ⊆ X` of dimension `d`,

`deg_𝓛(Z) = deg(c₁(𝓛)^d ∩ [Z]_d)`,

the left-hand side being the degree of [Stacks, Tag 0BEW]. -/
theorem degreeWithRespectTo_eq_chowDegree_iteratedFirstChernCap {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ)
    (dimZ : topologicalKrullDim Z = d) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (ample : Scheme.Modules.IsAmple X L) :
    degreeWithRespectTo k f i d dimZ L ample =
      chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k) f
        (IsLocalRing.closedPoint k)
        (iteratedFirstChernCap k f (fun _ : Fin d => L)
          (QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) f d)
            (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f i d))) :=
  intersectionNumber_eq_capDegree_of_le k d f i dimZ.le (fun _ => L)

/-- Let `k` be a field, let `X` be a proper scheme over `k` and let `Z ⊆ X` be a closed
subscheme of dimension `d`. For invertible `𝒪_X`-modules `𝓛_1, …, 𝓛_d`,

`(𝓛_1 ⋯ 𝓛_d · Z) = deg(c₁(𝓛_1) ∩ ⋯ ∩ c₁(𝓛_d) ∩ [Z]_d)`,

and in particular, for an ample invertible `𝒪_X`-module `𝓛`,

`deg_𝓛(Z) = deg(c₁(𝓛)^d ∩ [Z]_d)`.

Here `(𝓛_1 ⋯ 𝓛_d · Z)` is the intersection number of [Stacks, Tag 0BEP], `deg_𝓛(Z)` the degree
of [Stacks, Tag 0BEW], and `deg` the degree of zero cycles of [Stacks, Tag 0AZ1], for the Chow
groups over `Spec k` with its zero dimension function. -/
@[stacks 0BFI]
theorem intersectionNumber_eq_chowDegree_iteratedFirstChernCap_and_ample {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ)
    (dimZ : topologicalKrullDim Z = d) :
    (∀ (L : Fin d → X.Modules) [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)],
      intersectionNumber k f i d dimZ.le L =
        chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k) f
          (IsLocalRing.closedPoint k)
          (iteratedFirstChernCap k f L
            (QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) f d)
              (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f i d)))) ∧
    (∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
      (ample : Scheme.Modules.IsAmple X L),
      degreeWithRespectTo k f i d dimZ L ample =
        chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k) f
          (IsLocalRing.closedPoint k)
          (iteratedFirstChernCap k f (fun _ : Fin d => L)
            (QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) f d)
              (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f i d)))) :=
  ⟨fun L _ => intersectionNumber_eq_chowDegree_iteratedFirstChernCap k f i d dimZ L,
    fun L _ ample => degreeWithRespectTo_eq_chowDegree_iteratedFirstChernCap k f i d dimZ L ample⟩

end Main

end AlgebraicGeometry
