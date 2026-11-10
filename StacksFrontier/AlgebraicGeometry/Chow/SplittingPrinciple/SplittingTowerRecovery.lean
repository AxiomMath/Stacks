module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapDivisorInduction
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.InvertibleCap
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.IteratedCap
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.ChernClasses
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.FlagBundleUnconditional
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.ProjectiveBundleTower
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelConstantRank
public import StacksFrontier.AlgebraicGeometry.RelativeProjDegreeOne.Tautological
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The splitting morphism as a tower of projective bundles, and recovering a class from it

Let `(S, δ)` be as in Situation 02QL, `X` locally of finite type over `S` and `ℰ_i` a finite
collection of finite locally free `𝒪_X`-modules of ranks `r_i`. The proof of Stacks 02UL builds
`π : P ⟶ X` by repeatedly passing to the projective bundle `𝐏(ℰ_i) ⟶ X` of a module of rank at
least two and replacing `ℰ_i` by the kernel of the tautological surjection `π^*ℰ_i ⟶ 𝒪(1)`.
Stacks 0FVE records that this morphism

1. is a finite composition of projective space bundles of finite locally free modules of constant
   rank, and
2. satisfies `α = π_*(ξ_1 ∩ ⋯ ∩ ξ_d ∩ π^*α)` for every `α ∈ CH_k(X)`, where each `ξ_j` is the
   first Chern class of an invertible `𝒪_P`-module.

Here the layers are the actual projective bundles `Stacks.Chow.bundle`, with flatness, relative
dimension and the projective bundle formula of Stacks 02TX, flat pullback on Chow groups by
Stacks 02S1 (`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general`), and the
tautological sequence from the epimorphism `π^*ℰ ⟶ 𝒪(1)`; nothing about a layer is assumed.
Clause (2) follows, as in the source, from clause (1) and Stacks 02TW
(`Stacks.Chow.projectiveBundle_projection_self`): along one layer `p : 𝐏(ℰ) ⟶ Y` of relative
dimension `m` one has `p_*(c₁(𝒪(1))^m ∩ p^*α) = α`, and capping with first Chern classes commutes
with flat pullback (Stacks 02SS), so the identities compose along the tower by Stacks 02RD and
Stacks 02R5.

## Main definitions

* `Stacks.Chow.projectiveBundleStep` — the projective bundle of a finite locally free module of
  rank `m + 2`, as one layer `Stacks.Chow.BundleStep` of the splitting tower, with every field
  proved.
* `Stacks.Chow.IsProjectiveBundleTower` — a splitting morphism which is the identity, or the
  projection of `Stacks.Chow.projectiveBundleStep` of a module of constant rank composed with
  such a tower.
* `Stacks.Chow.SplittingMorphism.RecoversByCaps` — the identity of clause (2) for a list of cap
  operators.

## Main results

* `Stacks.Chow.exists_splittingMorphism_isProjectiveBundleTower_recoversByCaps` —
  **Stacks 0FVE**.

## References

* [Stacks Project, Tag 0FVE](https://stacks.math.columbia.edu/tag/0FVE)
* [Stacks Project, Tag 02UL](https://stacks.math.columbia.edu/tag/02UL)
* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### One layer: the projective bundle of a module of rank at least two -/

/-- The two spellings of invertibility of a module on a scheme, through `X.sheaf.obj` and through
`X.presheaf`, agree. Stated for an arbitrary scheme, so that the comparison is never made at a
particular, large, scheme. -/
theorem isInvertible_presheaf_of_isInvertible_sheaf {P : Scheme.{u}} {L : P.Modules}
    (h : AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L) :
    AlgebraicGeometry.SheafOfModules.IsInvertible P.presheaf P.ringCatSheaf.2 L :=
  h

/-- The kernel sequence of an epimorphism of modules on a scheme is short exact. -/
theorem shortExact_kernel_of_epi {P : Scheme.{u}} {M L : P.Modules} (q : M ⟶ L) [Epi q] :
    (ShortComplex.mk (kernel.ι q) q (kernel.condition q)).ShortExact :=
  { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
    mono_f := inferInstanceAs (Mono (kernel.ι q))
    epi_g := inferInstanceAs (Epi q) }

section Step

variable {X : Scheme.{u}} (E : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- The kernel of the tautological map of the bundle of a module of rank `m + 2` is finite
locally free of rank `m + 1`. -/
theorem isFiniteLocallyFreeOfRank_kernel_bundleQuot (m : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (m + 1 + 1)) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (kernel (bundleTautological E)) (m + 1) :=
  Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi_isInvertible _
    (epi_bundleTautological E)
    (isInvertible_presheaf_of_isInvertible_sheaf (isInvertible_bundleTwist E)) m
    (@AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ (bundleProj E) E (m + 1 + 1) hE)

/-- The projection of the bundle of a module of rank `m + 2` is flat: Stacks 02TX. -/
theorem flat_bundleProj_ofRank' (m : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (m + 1 + 1)) :
    Flat (bundleProj E) :=
  let := hE
  flat_bundleProj E (m + 1)

end Step


section StepDef

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (E : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (m : ℕ)
  (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (m + 1 + 1))

/-- **Stacks 02TX, injectivity**, for the bundle of a module of rank `m + 2`, at the instance
spelling of this section. -/
theorem projectiveBundleRelationInjective_bundle' :
    letI := flat_bundleProj_ofRank' E m hE
    letI := locallyOfFiniteType_bundleProj E (m + 1)
    ProjectiveBundleRelationInjective C sX (bundleProj E ≫ sX) (bundleProj E) rfl (m + 1 + 1)
      (relativeDimension_bundleProj E (m + 1))
      (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ _ k)
      (bundleTwistCap E C sX) :=
  let := hE
  projectiveBundleRelationInjective_bundle E (m + 1) C sX

/-- The layer `Stacks.Chow.projectiveBundleStep`, for a module whose finite local freeness is
given as an instance. -/
def projectiveBundleLayer : BundleStep C sX E (m + 1) :=
  letI := flat_bundleProj_ofRank' E m hE
  letI := locallyOfFiniteType_bundleProj E (m + 1)
  { P := bundle E
    sP := bundleProj E ≫ sX
    π := bundleProj E
    hsP := rfl
    relDim := relativeDimension_bundleProj E (m + 1)
    hfac := fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ _ k
    twist := bundleTwistCap E C sX
    hinj := projectiveBundleRelationInjective_bundle' C sX E m hE
    twistModule := bundleTwist E
    twistModule_isInvertible :=
      isInvertible_presheaf_of_isInvertible_sheaf (isInvertible_bundleTwist E)
    sub := kernel (bundleTautological E)
    incl := kernel.ι (bundleTautological E)
    quot := bundleTautological E
    incl_comp_quot := kernel.condition (bundleTautological E)
    shortExact := haveI := epi_bundleTautological E; shortExact_kernel_of_epi (bundleTautological E)
    sub_rank := isFiniteLocallyFreeOfRank_kernel_bundleQuot E m hE }

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- **The projective bundle `𝐏(ℰ) ⟶ X` of a module of rank `m + 2`, as a layer of the splitting
tower.** Flatness and relative dimension `m + 1` are Stacks 02TX, properness Stacks 0800, the
descent of flat pullback Stacks 02S1, injectivity of the projective bundle map the injectivity
half of Stacks 02TX, and the tautological sequence `0 ⟶ 𝓕 ⟶ π^*ℰ ⟶ 𝒪(1) ⟶ 0` is the kernel
sequence of the tautological epimorphism, whose kernel is finite locally free of rank `m + 1`. -/
@[ega "IV 19.4.11" "special case"]
def projectiveBundleStep : BundleStep C sX E (m + 1) :=
  @projectiveBundleLayer C X sX _ E
    (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
      (m + 1 + 1)) m hE

end StepDef

/-! ### Towers of actual projective bundles: clause (1) -/

/-- **A splitting morphism presented as a finite composition of projective space bundles.**
`IsProjectiveBundleTower C sX d T` says that the morphism of `T` is the identity of `X`, or the
projection of the projective bundle `𝐏(ℰ) ⟶ X` of a finite locally free module `ℰ` of constant
rank `m + 2` (the layer `Stacks.Chow.projectiveBundleStep`, of relative dimension `m + 1`)
precomposed with such a tower over `𝐏(ℰ)`. -/
inductive IsProjectiveBundleTower (C : ChowSituation.{u}) : {X : Scheme.{u}} → (sX : X ⟶ C.S) →
    [LocallyOfFiniteType sX] → (d : ℕ) → SplittingMorphism C sX d → Prop
  /-- The identity of `X` is the empty tower. -/
  | id {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] :
      IsProjectiveBundleTower C sX 0 (SplittingMorphism.id C sX)
  /-- The projective bundle of a module of constant rank `m + 2`, composed with a tower over
  it. -/
  | compStep {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (E : X.Modules) (m : ℕ)
      (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (m + 1 + 1))
      (n : ℕ) (T : SplittingMorphism C (projectiveBundleStep C sX E m hE).sP n)
      (hT : IsProjectiveBundleTower C (projectiveBundleStep C sX E m hE).sP n T) :
      IsProjectiveBundleTower C sX (n + (m + 1))
        (SplittingMorphism.compStep (projectiveBundleStep C sX E m hE) T)

/-- A tower of actual projective bundles is in particular a tower of layers in the sense of
`Stacks.Chow.IsBundleTower`. -/
theorem IsProjectiveBundleTower.isBundleTower {C : ChowSituation.{u}} {X : Scheme.{u}}
    {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {d : ℕ} {T : SplittingMorphism C sX d}
    (h : IsProjectiveBundleTower C sX d T) : IsBundleTower C sX d T := by
  induction h with
  | id sX => exact IsBundleTower.id sX
  | compStep sX E m hE n T _ ih => exact IsBundleTower.compStep sX E (m + 1) hE _ n T ih

/-! ### Iterated caps -/

section Caps

variable (C : ChowSituation.{u})

/-- An invertible module on a scheme, at the spelling of `Stacks.Chow.invCap`. -/
abbrev InvertibleModule (P : Scheme.{u}) : Type _ :=
  {L : P.Modules // AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj
    P.ringCatSheaf.property L}

/-- The pullback of an invertible module along a morphism of schemes. -/
def InvertibleModule.pullback {P Q : Scheme.{u}} (L : InvertibleModule Q) (f : P ⟶ Q) :
    InvertibleModule P :=
  ⟨(Scheme.Modules.pullback f).obj L.1,
    by exact Stacks.WeilCohomology.isInvertible_pullback_obj f L.1 L.2⟩

/-- The first Chern class cap operators `c₁(L) ∩ -` of a list of invertible modules. -/
def invCapList {P : Scheme.{u}} (p : P ⟶ C.S) [LocallyOfFiniteType p]
    (Ls : List (InvertibleModule P)) : List (ChernCapOperator C p) :=
  Ls.map fun L ↦ @invCap C P p _ L.1 L.2

/-- The list of cap operators of `Ls` has the same length as `Ls`. -/
@[simp]
theorem length_invCapList {P : Scheme.{u}} (p : P ⟶ C.S) [LocallyOfFiniteType p]
    (Ls : List (InvertibleModule P)) : (invCapList C p Ls).length = Ls.length := by
  simp [invCapList]

/-- The cap operators of a concatenation are the concatenation of the cap operators. -/
theorem invCapList_append {P : Scheme.{u}} (p : P ⟶ C.S) [LocallyOfFiniteType p]
    (Ls Ms : List (InvertibleModule P)) :
    invCapList C p (Ls ++ Ms) = invCapList C p Ls ++ invCapList C p Ms := by
  simp [invCapList]

/-- The cap operators of `s` copies of `L` are `s` copies of `c₁(L) ∩ -`. -/
theorem invCapList_replicate {P : Scheme.{u}} (p : P ⟶ C.S) [LocallyOfFiniteType p] (s : ℕ)
    (L : InvertibleModule P) :
    invCapList C p (List.replicate s L) = List.replicate s (@invCap C P p _ L.1 L.2) := by
  simp [invCapList]

/-- Iterated caps of `invCapList` of `r` copies of `L` and of `r` copies of `c₁(L)` agree on
transports of one class. -/
private theorem iteratedChernCapOnChow_invCapList_replicate_heq {P : Scheme.{u}} (p : P ⟶ C.S)
    [LocallyOfFiniteType p] (L : InvertibleModule P) (r : ℕ) (k : ℤ) {d : ℤ} (x : chowGroup C p d)
    (h₁ : d = k + ((invCapList C p (List.replicate r L)).length : ℤ))
    (h₂ : d = k + ((List.replicate r (@invCap C P p _ L.1 L.2)).length : ℤ)) :
    iteratedChernCapOnChow C p (invCapList C p (List.replicate r L)) k (chowGroupCast C p h₁ x) ≍
      iteratedChernCapOnChow C p (List.replicate r (@invCap C P p _ L.1 L.2)) k
        (chowGroupCast C p h₂ x) :=
  iteratedChernCapOnChow_heq_of_eq C p (invCapList_replicate C p r L) k
    ((chowGroupCast_heq C p _ x).trans (chowGroupCast_heq C p _ x).symm)

/-- Transport commutes with flat pullback, up to heterogeneous equality. -/
private theorem chowGroupCast_heq_flatPullbackChow_cast {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Flat f] (hf : f ≫ sY = sX) (e : ℕ)
    (he : AlgebraicGeometry.RelativeDimension f e)
    (hfac : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sX sY f hf e he k)
    {a b a' b' : ℤ} (h : a = b) (h' : a' = b') (y : chowGroup C sY a) (y' : chowGroup C sX a')
    (hy : y' ≍ flatPullbackChow C sX sY f hf e he a (hfac a) y) :
    chowGroupCast C sX h' y' ≍
      flatPullbackChow C sX sY f hf e he b (hfac b) (chowGroupCast C sY h y) := by
  subst h h'
  exact hy

/-- **Stacks 02SS for iterated caps.** Flat pullback carries `c₁(L)^s ∩ -` to `c₁(f^*L)^s ∩ -`. -/
theorem flatPullbackChow_iteratedChernCapOnChow_replicate {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Flat f] (hf : f ≫ sY = sX) (e : ℕ)
    (he : AlgebraicGeometry.RelativeDimension f e)
    (hfac : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sX sY f hf e he k)
    (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]
    (L' : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L']
    (eL : L' ≅ (Scheme.Modules.pullback f).obj L) (s : ℕ) (j : ℤ)
    (y : chowGroup C sY (j + ((List.replicate s (invCap C sY L)).length : ℤ)))
    (y' : chowGroup C sX (j + (e : ℤ) + ((List.replicate s (invCap C sX L')).length : ℤ)))
    (hy : y' ≍ flatPullbackChow C sX sY f hf e he _ (hfac _) y) :
    flatPullbackChow C sX sY f hf e he j (hfac j)
        (iteratedChernCapOnChow C sY (List.replicate s (invCap C sY L)) j y) ≍
      iteratedChernCapOnChow C sX (List.replicate s (invCap C sX L')) (j + (e : ℤ)) y' := by
  induction s generalizing j with
  | zero =>
    refine HEq.trans ?_ (iteratedChernCapOnChow_replicate_zero_heq C sX _ _ y').symm
    refine HEq.trans ?_ hy.symm
    exact heq_apply_of_degree C sY sX (fun d ↦ d) (fun d ↦ d + (e : ℤ))
      (fun d ↦ flatPullbackChow C sX sY f hf e he d (hfac d)) (by simp)
      (iteratedChernCapOnChow_replicate_zero_heq C sY _ _ y)
  | succ s ih =>
    rw [iteratedChernCapOnChow_replicate_succ_heq C sY _ s j y
        (chowGroupCast C sY (by simp only [List.length_replicate] ; omega) y)
        (chowGroupCast_heq C sY _ y).symm,
      iteratedChernCapOnChow_replicate_succ_heq C sX _ s (j + (e : ℤ)) y'
        (chowGroupCast C sX (by simp only [List.length_replicate] ; omega) y')
        (chowGroupCast_heq C sX _ y').symm]
    have hIH := ih (j + 1) (chowGroupCast C sY (by simp only [List.length_replicate] ; omega) y)
      (chowGroupCast C sX (by simp only [List.length_replicate] ; omega) y')
      (chowGroupCast_heq_flatPullbackChow_cast C sX sY f hf e he hfac _ _ y y' hy)
    refine flatPullbackChow_firstChernClassCapChow_heq C sX sY f hf e he hfac L L' eL j _ _ ?_
    refine HEq.trans ?_ hIH.symm
    exact iteratedChernCapOnChow_heq C sX _ (by ring)
      ((chowGroupCast_heq C sX _ y').trans (chowGroupCast_heq C sX _ y').symm)

end Caps

/-! ### Clause (2) -/

namespace BundleStep

variable {C : ChowSituation.{u}} {X : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
  {E : X.Modules} {r : ℕ}

/-- The tautological invertible module `𝒪(1)` of a layer. -/
def twistInvertible (D : BundleStep C sX E r) : InvertibleModule D.P :=
  ⟨D.twistModule, by exact D.twistModule_isInvertible⟩

/-- **The top case of Stacks 02TW for a layer** of relative dimension `r` and an invertible module
`L` on it: `p_*(c₁(L)^r ∩ p^*α) = α` for every `α ∈ CH_k(X)`. -/
def RecoversByCaps (D : BundleStep C sX E r) (L : InvertibleModule D.P) : Prop :=
  ∀ (k : ℤ) (h : k + (r : ℤ) = k + ((invCapList C D.sP (List.replicate r L)).length : ℤ))
    (α : chowGroup C sX k),
    properChowPushforward C D.sP sX D.π D.hsP k
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C D.sP sX D.π D.hsP k)
        (iteratedChernCapOnChow C D.sP (invCapList C D.sP (List.replicate r L)) k
          (chowGroupCast C D.sP h (D.pullbackChow k α))) = α

end BundleStep

namespace SplittingMorphism

variable {C : ChowSituation.{u}} {X : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]

/-- **The identity of clause (2) of Stacks 0FVE** for a list `Os = [ξ_1, …, ξ_d]` of cap
operators on the source of `T : P ⟶ X`: `π_*(ξ_1 ∩ ⋯ ∩ ξ_d ∩ π^*α) = α` for every
`α ∈ CH_k(X)`. The degree `k + d` of `π^*α` is identified with `k + |Os|` along any proof `h` of
their equality. -/
def RecoversByCaps {d : ℕ} (T : SplittingMorphism C sX d) (Os : List (ChernCapOperator C T.sP)) :
    Prop :=
  ∀ (k : ℤ) (h : k + (d : ℤ) = k + (Os.length : ℤ)) (α : chowGroup C sX k),
    properChowPushforward C T.sP sX T.π T.hsP k
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C T.sP sX T.π T.hsP k)
        (iteratedChernCapOnChow C T.sP Os k (chowGroupCast C T.sP h (T.pullbackChow k α))) = α

/-- The identity recovers every class with no caps at all. -/
theorem recoversByCaps_id (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] : (SplittingMorphism.id C sX).RecoversByCaps [] := by
  intro k h α
  change properChowPushforward C sX sX (𝟙 X) (Category.id_comp sX) k
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sX sX (𝟙 X)
      (Category.id_comp sX) k) _ = α
  rw [properChowPushforward_id]
  change iteratedChernCapOnChow C sX [] k (chowGroupCast C sX h
    (flatPullbackChow C sX sX (𝟙 X) (Category.id_comp sX) 0 (relativeDimension_identity X) k
      (flatPullbackFactorsThroughRationalEquivalence_id C sX k) α)) = α
  refine chowGroup_eq_of_heq C sX ((iteratedChernCapOnChow_nil_heq C sX k _).trans
    ((chowGroupCast_heq C sX _ _).trans ?_))
  rw [flatPullbackChow_id]
  exact chowGroupCast_heq C sX _ α

/-- **One layer of clause (2).** If a layer `p : D.P ⟶ X` of relative dimension `r` satisfies
`p_*(c₁(L)^r ∩ p^*α) = α`, and a splitting morphism `T` over `D.P` recovers every class by the
caps `Os`, then `T` followed by `p` recovers every class by `Os` followed by `r` copies of
`c₁(T^*L)`: by Stacks 02SS the inner caps are the flat pullback along `T` of `c₁(L)^r ∩ p^*α`,
which `T` recovers, and flat pullback and proper pushforward compose (Stacks 02RD, 02R5). -/
theorem recoversByCaps_compStep {E : X.Modules} {r : ℕ} (D : BundleStep C sX E r)
    (L : InvertibleModule D.P) (hD : D.RecoversByCaps L) {n : ℕ}
    (T : SplittingMorphism C D.sP n) (Os : List (ChernCapOperator C T.sP)) (hOs : Os.length = n)
    (hT : T.RecoversByCaps Os) :
    (SplittingMorphism.compStep D T).RecoversByCaps
      (Os ++ invCapList C T.sP (List.replicate r (L.pullback T.π))) := by
  have := L.2
  have := (L.pullback T.π).2
  rw [invCapList_replicate]
  intro k h α
  -- the class `β = c₁(L)^r ∩ p^*α` on the layer, and Stacks 02TW for it
  have h02TW := hD k (by simp only [length_invCapList, List.length_replicate]) α
  set β := iteratedChernCapOnChow C D.sP (invCapList C D.sP (List.replicate r L)) k
    (chowGroupCast C D.sP (by simp only [length_invCapList, List.length_replicate])
      (D.pullbackChow k α)) with hβ
  have hβ' : β ≍ iteratedChernCapOnChow C D.sP (List.replicate r (invCap C D.sP L.1)) k
      (chowGroupCast C D.sP (by simp only [List.length_replicate]) (D.pullbackChow k α)) :=
    iteratedChernCapOnChow_invCapList_replicate_heq C D.sP L r k _ _ _
  -- the inner caps are the pullback of `β` along `T`
  have hB := flatPullbackChow_iteratedChernCapOnChow_replicate C T.sP D.sP T.π T.hsP n T.relDim
    T.hfac L.1 (L.pullback T.π).1 (Iso.refl _) r k
    (chowGroupCast C D.sP (by simp only [List.length_replicate]) (D.pullbackChow k α))
    (chowGroupCast C T.sP (by simp only [List.length_replicate] ; omega)
      (T.pullbackChow (k + (r : ℤ)) (D.pullbackChow k α)))
    (chowGroupCast_heq_flatPullbackChow_cast C T.sP D.sP T.π T.hsP n T.relDim T.hfac _ _ _ _
      HEq.rfl)
  have hinner : iteratedChernCapOnChow C T.sP (List.replicate r (invCap C T.sP (L.pullback T.π).1))
        (k + (Os.length : ℤ))
        (chowGroupCast C T.sP (by simp only [List.length_replicate, hOs] ; omega)
          (T.pullbackChow (k + (r : ℤ)) (D.pullbackChow k α))) ≍
      T.pullbackChow k β := by
    refine HEq.trans ?_ (HEq.trans hB.symm ?_)
    · exact iteratedChernCapOnChow_heq C T.sP _ (by rw [hOs])
        ((chowGroupCast_heq C T.sP _ _).trans (chowGroupCast_heq C T.sP _ _).symm)
    · exact heq_apply_of_degree C D.sP T.sP (fun d ↦ d) (fun d ↦ d + (n : ℤ))
        (fun d ↦ T.pullbackChow d) rfl hβ'.symm
  -- the pullback along the composite is the composite of the pullbacks
  have hpull : (SplittingMorphism.compStep D T).pullbackChow k α ≍
      T.pullbackChow (k + (r : ℤ)) (D.pullbackChow k α) :=
    (flatPullbackChow_comp C T.sP D.sP sX T.π D.π T.hsP D.hsP n r T.relDim D.relDim
      k (T.hfac _) (D.hfac k) _ α).symm
  have hsplit := iteratedChernCapOnChow_append C T.sP Os
    (List.replicate r (invCap C T.sP (L.pullback T.π).1)) k
    (chowGroupCast C T.sP h ((SplittingMorphism.compStep D T).pullbackChow k α))
    (chowGroupCast C T.sP (by simp only [List.length_replicate, hOs] ; omega)
      (T.pullbackChow (k + (r : ℤ)) (D.pullbackChow k α)))
    ((chowGroupCast_heq C T.sP _ _).trans (hpull.trans (chowGroupCast_heq C T.sP _ _).symm))
  have hT' := hT k (by rw [hOs]) β
  have hcomp := properChowPushforward_comp C T.sP D.sP sX T.π D.π T.hsP D.hsP k
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C T.sP D.sP T.π T.hsP k)
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C D.sP sX D.π D.hsP k)
  refine Eq.trans (congrArg (properChowPushforward C T.sP sX (T.π ≫ D.π)
    (by rw [Category.assoc, D.hsP, T.hsP]) k
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C T.sP sX (T.π ≫ D.π)
      (by rw [Category.assoc, D.hsP, T.hsP]) k)) hsplit) ?_
  refine Eq.trans (DFunLike.congr_fun hcomp _).symm ?_
  refine Eq.trans (congrArg (properChowPushforward C D.sP sX D.π D.hsP k
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C D.sP sX D.π D.hsP k))
    (Eq.trans ?_ hT')) h02TW
  refine congrArg (properChowPushforward C T.sP D.sP T.π T.hsP k
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C T.sP D.sP T.π T.hsP k))
    (congrArg (iteratedChernCapOnChow C T.sP Os k) ?_)
  exact chowGroup_eq_of_heq C T.sP (hinner.trans (chowGroupCast_heq C T.sP _ _).symm)

end SplittingMorphism

section Recovery

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (E : X.Modules) (m : ℕ)
  (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (m + 1 + 1))

/-- **Stacks 02TW, the top power, for the layer `𝐏(ℰ) ⟶ X`**:
`p_*(c₁(𝒪(1))^{m+1} ∩ p^*α) = α`. This is `Stacks.Chow.projectiveBundle_projection_self`. -/
theorem projectiveBundleStep_recoversByCaps :
    (projectiveBundleStep C sX E m hE).RecoversByCaps
      (projectiveBundleStep C sX E m hE).twistInvertible := by
  let := hE
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
    (m + 1 + 1)
  let := flat_bundleProj E (m + 1)
  let := locallyOfFiniteType_bundleProj E (m + 1)
  intro k h α
  have key := projectiveBundle_projection_self E (m + 1) C sX k α
  refine Eq.trans ?_ key
  change properChowPushforward C (bundleProj E ≫ sX) sX (bundleProj E) rfl k
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sX _ rfl k) _ =
    properChowPushforward C (bundleProj E ≫ sX) sX (bundleProj E) rfl k
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sX _ rfl k)
      (capPow C (bundleProj E ≫ sX) (invCap C (bundleProj E ≫ sX) (bundleTwist E)) (m + 1)
        (k + ((m + 1 : ℕ) : ℤ)) k (by ring)
        (bundlePullback C sX (bundleProj E ≫ sX) (bundleProj E) rfl (m + 1)
          (relativeDimension_bundleProj E (m + 1)) k α))
  congr 1
  have hcap : capPow C (bundleProj E ≫ sX) (invCap C (bundleProj E ≫ sX) (bundleTwist E))
      (m + 1) (k + ((m + 1 : ℕ) : ℤ)) k (by ring)
      (bundlePullback C sX (bundleProj E ≫ sX) (bundleProj E) rfl (m + 1)
        (relativeDimension_bundleProj E (m + 1)) k α) =
      iteratedChernCapOnChow C (bundleProj E ≫ sX)
        (List.replicate (m + 1) (invCap C (bundleProj E ≫ sX) (bundleTwist E))) k
        (chowGroupCast C (bundleProj E ≫ sX) (by simp only [List.length_replicate])
          (bundlePullback C sX (bundleProj E ≫ sX) (bundleProj E) rfl (m + 1)
            (relativeDimension_bundleProj E (m + 1)) k α)) := by
    rw [← capPow_eq_iteratedChernCapOnChow, capPow_cast]
  rw [hcap]
  exact chowGroup_eq_of_heq C _ (iteratedChernCapOnChow_invCapList_replicate_heq C _ _ _ k _ _ _)

end Recovery

/-! ### Stacks 0FVE -/

/-- The splitting tower, in the form the strong induction on `∑ binom(r_i, 2)` proves: the total
relative dimension is the induction variable. -/
private theorem exists_splittingMorphism_isProjectiveBundleTower_aux (C : ChowSituation.{u}) :
    ∀ (n : ℕ) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (I : Type)
      [Fintype I] (E : I → X.Modules) (r : I → ℕ),
      (∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (E i) (r i)) →
      ∑ i, (r i).choose 2 = n →
      ∃ T : SplittingMorphism C sX n, IsProjectiveBundleTower C sX n T ∧
        (∀ i, Stacks.WeilCohomology.HasInvertibleFiltration T.P
          ((Scheme.Modules.pullback T.π).obj (E i)) (r i)) ∧
        ∃ Ls : List (InvertibleModule T.P), Ls.length = n ∧
          T.RecoversByCaps (invCapList C T.sP Ls) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X sX _ I _ E r hE hn
    by_cases hr : ∀ i, r i ≤ 1
    · -- every rank is at most one: the identity of `X` is the empty tower
      have hn0 : n = 0 := by
        rw [← hn, Finset.sum_eq_zero]
        intro i _
        exact Nat.choose_eq_zero_of_lt (by have := hr i; omega)
      subst hn0
      refine ⟨SplittingMorphism.id C sX, IsProjectiveBundleTower.id (C := C) sX, fun i ↦ ?_,
        [], rfl, SplittingMorphism.recoversByCaps_id C sX⟩
      exact Stacks.WeilCohomology.hasInvertibleFiltration_of_rank_le_one _ (r i)
        (@AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ (𝟙 X) (E i) (r i) (hE i))
        (hr i)
    -- some rank exceeds one: the bottom layer is the projective bundle of that module
    obtain ⟨i, hi⟩ := not_forall.mp hr
    obtain ⟨m, hm⟩ : ∃ m, r i = m + 1 + 1 := ⟨r i - 2, by omega⟩
    have hEi : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (E i)
        (m + 1 + 1) := hm ▸ hE i
    set D := projectiveBundleStep C sX (E i) m hEi with hDdef
    have hE' : ∀ j, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (Function.update (fun j ↦ (Scheme.Modules.pullback D.π).obj (E j)) i D.sub j)
        (Function.update r i (m + 1) j) := by
      intro j
      by_cases hj : j = i
      · rw [hj]
        simpa only [Function.update_self] using D.sub_rank
      · simpa only [Function.update_of_ne hj] using
          @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ D.π (E j) (r j) (hE j)
    have hchoose : (m + 1).choose 2 + (m + 1) = (r i).choose 2 := by
      have key : (m + 1 + 1).choose 2 = (m + 1).choose 2 + (m + 1) := by
        change Nat.choose (m + 1 + 1) (1 + 1) = _
        rw [Nat.choose_succ_succ, Nat.choose_one_right]
        change m + 1 + Nat.choose (m + 1) 2 = Nat.choose (m + 1) 2 + (m + 1)
        omega
      rw [hm, key]
    have hA : (∑ j, (Function.update r i (m + 1) j).choose 2) =
        (m + 1).choose 2 + ∑ j ∈ Finset.univ.erase i, (r j).choose 2 := by
      rw [← Finset.add_sum_erase Finset.univ
        (fun j ↦ (Function.update r i (m + 1) j).choose 2) (Finset.mem_univ i),
        Function.update_self]
      exact congrArg _ (Finset.sum_congr rfl fun j hj ↦ by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
    have hB : (∑ j, (r j).choose 2) =
        (r i).choose 2 + ∑ j ∈ Finset.univ.erase i, (r j).choose 2 :=
      (Finset.add_sum_erase Finset.univ (fun j ↦ (r j).choose 2) (Finset.mem_univ i)).symm
    have hsum : (∑ j, (Function.update r i (m + 1) j).choose 2) + (m + 1) = n := by
      rw [hA, ← hn, hB]; omega
    have hlt : (∑ j, (Function.update r i (m + 1) j).choose 2) < n := by
      rw [hA, ← hn, hB]; omega
    obtain ⟨T, hTtower, hT, Ls, hLs, hTrec⟩ := ih _ hlt D.sP I
      (Function.update (fun j ↦ (Scheme.Modules.pullback D.π).obj (E j)) i D.sub)
      (Function.update r i (m + 1)) hE' rfl
    subst hsum
    refine ⟨SplittingMorphism.compStep D T,
      IsProjectiveBundleTower.compStep (C := C) sX (E i) m hEi _ T hTtower, fun j ↦ ?_,
      Ls ++ List.replicate (m + 1) (D.twistInvertible.pullback T.π), by simp [hLs], ?_⟩
    · simp only [SplittingMorphism.compStep_P, SplittingMorphism.compStep_π]
      have comp₁ : (Scheme.Modules.pullback T.π).obj
            ((Scheme.Modules.pullback D.π).obj (E j)) ≅
          (Scheme.Modules.pullback (T.π ≫ D.π)).obj (E j) :=
        (Scheme.Modules.pullbackComp T.π D.π).app (E j)
      by_cases hj : j = i
      · rw [hj] at comp₁ ⊢
        rw [hm]
        have hDx : ((ShortComplex.mk D.incl D.quot D.incl_comp_quot).map
            (Scheme.Modules.pullback T.π)).ShortExact :=
          Stacks.WeilCohomology.shortExact_map_pullback T.π _ D.shortExact
        have hleft : Stacks.WeilCohomology.HasInvertibleFiltration T.P
            ((Scheme.Modules.pullback T.π).obj D.sub) (m + 1) := by
          simpa only [Function.update_self] using hT i
        have hrank : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
            ((Scheme.Modules.pullback T.π).obj
              ((Scheme.Modules.pullback D.π).obj (E i))) (m + 1 + 1) :=
          @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ T.π _ _
            (@AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ D.π (E i) _ hEi)
        exact Stacks.WeilCohomology.HasInvertibleFiltration.of_iso comp₁
          (Stacks.WeilCohomology.HasInvertibleFiltration.step _ _ _ hDx
            (Stacks.WeilCohomology.isInvertible_pullback_obj T.π D.twistModule
              D.twistModule_isInvertible)
            hrank.isFiniteLocallyFree hleft)
      · refine Stacks.WeilCohomology.HasInvertibleFiltration.of_iso comp₁ ?_
        simpa only [Function.update_of_ne hj] using hT j
    · have hrec := SplittingMorphism.recoversByCaps_compStep D D.twistInvertible
        (projectiveBundleStep_recoversByCaps C sX (E i) m hEi) T _
        (by rw [length_invCapList, hLs]) hTrec
      rw [← invCapList_append] at hrec
      exact hrec

/-- **Stacks 0FVE.** Let `(S, δ)` be as in Situation 02QL, `X` locally of finite type over `S`
and `ℰ_i` (`i ∈ I`, finite) finite locally free `𝒪_X`-modules of ranks `r_i`. The morphism
`π : P ⟶ X` built in the proof of Stacks 02UL — flat and proper of relative dimension
`d = ∑_i binom(r_i, 2)`, with injective flat pullback on Chow groups, such that each `π^*ℰ_i` has
a filtration with invertible successive quotients — has the further properties

1. `π` is a finite composition of projective space bundles associated to finite locally free
   modules of constant rank (`Stacks.Chow.IsProjectiveBundleTower`, whose layers are the actual
   projective bundles `Stacks.Chow.bundle`), and
2. there are invertible `𝒪_P`-modules `L_1, …, L_d` such that, with `ξ_j = c₁(L_j)`, every
   `α ∈ CH_k(X)` satisfies `α = π_*(ξ_1 ∩ ⋯ ∩ ξ_d ∩ π^*α)`. -/
@[stacks 0FVE]
theorem exists_splittingMorphism_isProjectiveBundleTower_recoversByCaps (C : ChowSituation.{u})
    {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (I : Type) [Fintype I]
    (E : I → X.Modules) (r : I → ℕ)
    (hE : ∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (E i) (r i)) :
    ∃ T : SplittingMorphism C sX (∑ i, (r i).choose 2),
      (∀ i, Stacks.WeilCohomology.HasInvertibleFiltration T.P
        ((Scheme.Modules.pullback T.π).obj (E i)) (r i)) ∧
      IsProjectiveBundleTower C sX (∑ i, (r i).choose 2) T ∧
      ∃ (Ls : List (InvertibleModule T.P)) (hLs : Ls.length = ∑ i, (r i).choose 2),
        ∀ (k : ℤ) (α : chowGroup C sX k),
          properChowPushforward C T.sP sX T.π T.hsP k
              (properPushforwardFactorsThroughRationalEquivalence_of_isProper C T.sP sX T.π
                T.hsP k)
              (iteratedChernCapOnChow C T.sP (invCapList C T.sP Ls) k
                (chowGroupCast C T.sP (by rw [length_invCapList, hLs])
                  (T.pullbackChow k α))) = α := by
  obtain ⟨T, htower, hfilt, Ls, hLs, hrec⟩ :=
    exists_splittingMorphism_isProjectiveBundleTower_aux C _ sX I E r hE rfl
  exact ⟨T, hfilt, htower, Ls, hLs, fun k α ↦ hrec k _ α⟩

end Stacks.Chow

end
