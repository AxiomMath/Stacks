module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageDerived

/-!
# Base change for bounded below complexes along a limit of cartesian diagrams of schemes

Let `I` be a preordered set and let `(X_i)`, `(S_i)`, `(T_i)`, `(Y_i)` be inverse systems of
schemes over `I` fitting into an inverse system of squares

```
X_i  ←-h_i-  Y_i
|f_i         |e_i
S_i  ←-g_i-  T_i
```

Writing `X = lim X_i`, `S = lim S_i`, `T = lim T_i`, `Y = lim Y_i` with projections
`r_i : X ⟶ X_i`, `s_i : S ⟶ S_i`, `p_i : T ⟶ T_i`, `q_i : Y ⟶ Y_i`, the four limit morphisms
`f`, `g`, `h`, `e` form a cartesian square on the limits, which is the setup of Stacks 0EZT; the
square is cartesian by
`Stacks.EtaleCohomology.LimitBaseChange.isPullback_limitSquare`.

Stacks 0GJL is the derived refinement of conclusion (2) of Stacks 0EZT. Fix `0 ∈ I` and an object
`K_0` of `D^+(T_{0, étale})`, let `K_i` be the pullback of `K_0` to `T_i` for `i ≥ 0` and `K` the
pullback of `K_0` to `T`. If `f_i^{-1}Rg_{i, *}K_i = Rh_{i, *}e_i^{-1}K_i` for all `i ≥ 0`, then
`f^{-1}Rg_*K = Rh_*e^{-1}K`.

## Main definitions

* `Stacks.EtaleCohomology.LimitBaseChangeDerived.stageObj`,
  `Stacks.EtaleCohomology.LimitBaseChangeDerived.limitObj` — the objects `K_i` of
  `D^+(T_{i, étale})` and `K` of `D^+(T_étale)`, the derived inverse images of `K_0` along the
  transition `T_i ⟶ T_0` and along the projection `p_0 : T ⟶ T_0`.
* `Stacks.EtaleCohomology.LimitBaseChangeDerived.derivedSourceTerm`,
  `Stacks.EtaleCohomology.LimitBaseChangeDerived.derivedTargetTerm` — the terms
  `s_i^{-1}H^p(Rg_{i, *}L)` and `r_i^{-1}H^p(Rh_{i, *}Re_i^{-1}L)` of the two colimit diagrams of
  Stacks 0GIU.
* `Stacks.EtaleCohomology.LimitBaseChangeDerived.derivedStageComparison` — the derived base change
  map of the `i`-th square, read on cohomology sheaves and pulled back to `X`, as a map
  `f^{-1}s_i^{-1}H^p(Rg_{i, *}L) ⟶ r_i^{-1}H^p(Rh_{i, *}Re_i^{-1}L)`.
* `Stacks.EtaleCohomology.LimitBaseChangeDerived.derivedLimitComparison` — the derived base change
  map of the limit square, read on cohomology sheaves, as a map
  `f^{-1}H^p(Rg_*M) ⟶ H^p(Rh_*Re^{-1}M)`.
* `Stacks.EtaleCohomology.LimitBaseChangeDerived.ColimitPresentation` — the two instances of the
  colimit assertion of Stacks 0GIU that the source's proof cites, in a fixed degree `p`, together
  with their comparison.

## Main results

* `Stacks.EtaleCohomology.LimitBaseChangeDerived.isIso_derivedStageComparison` — the stagewise
  comparison is invertible as soon as the derived base change map of the `i`-th square is.
* `Stacks.EtaleCohomology.LimitBaseChangeDerived.isIso_of_forall_isIso_derivedLimitComparison` —
  **the first reduction of the source's proof**: a map of `D^+` is invertible as soon as it is
  invertible on all cohomology sheaves, so it suffices to prove that
  `f^{-1}R^pg_*K ⟶ R^ph_*e^{-1}K` is an isomorphism for every `p ∈ ℤ`.
* `Stacks.EtaleCohomology.LimitBaseChangeDerived.isIso_derivedLimitComparison` — the limit
  comparison in a fixed degree `p` is invertible, given the colimit presentations of that degree
  and the stagewise hypothesis.
* `Stacks.EtaleCohomology.LimitBaseChangeDerived.isIso_smallEtaleDerivedBaseChangeAb_limit` —
  **Stacks 0GJL**: the derived base change map of the limit square at `K` is an isomorphism.

## Implementation notes

The geometric setup is the `variable` block of
`Stacks.EtaleCohomology.LimitBaseChange`, reproduced verbatim: the four systems, the four
morphisms of systems, four cones and the four limit morphisms carried as named morphisms together
with the equations `f ≫ s_i = r_i ≫ f_i` characterising them. As in that file only the
commutativity `wL` of the limit square is used, not its cartesianness, and the hypotheses of the
source that `I` be directed, the transitions affine and the `g_i` quasi-compact and quasi-separated
do not enter: they are what the colimit assertion of Stacks 0GIU needs.

The source's proof is in two steps. The first, that it suffices to check the base change map on
cohomology sheaves, is `isIso_of_forall_isIso_derivedLimitComparison` and is proved here from
`DerivedCategory.Plus.isIso_iff`. The second is the argument of Stacks 0EZT with
the reference to Stacks 0EYM replaced by one to Stacks 0GIU, and is
`isIso_derivedLimitComparison`.

The colimit assertion of Stacks 0GIU, `R^pg_*K = colim_{i ≥ 0} s_i^{-1}R^pg_{i, *}K_i`, is *not*
available in this repository:
`Stacks.EtaleCohomology.LimitHigherDirectImage.pullbackProjectionMap` constructs the comparison
maps of Stacks 0GIU and records in its own clause string that the colimit assertion is not proved,
being a formal consequence of the colimit assertion of Stacks 0EYM, which is itself unproved there
— indeed the colimit cannot even be *formed*, for that needs the cocycle compatibility of Stacks
0E47 for the bounded below derived base change map, which is also unavailable. Accordingly
`isIso_smallEtaleDerivedBaseChangeAb_limit` carries the two instances of Stacks 0GIU that the
source's proof cites — one for `g` with the objects `K_i`, one for `h` with the objects
`Re_i^{-1}K_i` — in the single bundled hypothesis `ColimitPresentation`, exactly as
`Stacks.EtaleCohomology.LimitBaseChange.isIso_higherBaseChangeMapAb_limit` carries the two
instances of Stacks 0EYM: a diagram over an index category `J`, isomorphisms identifying its terms
with `derivedSourceTerm` resp. `derivedTargetTerm`, and a colimit cocone whose vertex is the
cohomology sheaf of the higher direct image at the limit. It also carries the comparison `α` of the
two diagrams and its compatibility with the terms and with the legs, which is the pasting of base
change maps of Stacks 0E47. What is proved from those inputs is the source's own argument: inverse
image is a left adjoint, so it carries the first presentation to a colimit presentation of
`f^{-1}H^p(Rg_*K)`, and a map of colimit cocones which is invertible on every term is invertible.

The index category `J` of the presentation, together with the family of stages `σ : J → Iᵒᵖ` and
of transitions `τ j : σ j ⟶ 0` it refers to, is a parameter rather than a field, and is shared by
all degrees `p`: in the source it is the directed set `{i ∈ I | i ≥ 0}` for every `p`.

## References

* [Stacks Project, Tag 0GJL](https://stacks.math.columbia.edu/tag/0GJL)
* [Stacks Project, Tag 0EZT](https://stacks.math.columbia.edu/tag/0EZT)
* [Stacks Project, Tag 0GIU](https://stacks.math.columbia.edu/tag/0GIU)
* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)

Tags covered: 0GJL (from the two instances of the colimit assertion of Stacks 0GIU and the
pasting of Stacks 0E47).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe w₁ w₂ v u

namespace Stacks.EtaleCohomology.LimitBaseChangeDerived

attribute [local instance] HasDerivedCategory.standard

open Stacks.EtaleCohomology.LimitHigherDirectImage
  (PlusAb homologyAb derivedPushforwardAb derivedPullbackAb)

variable {I : Type v} [Preorder I] {DX DS DT DY : Iᵒᵖ ⥤ Scheme.{u}}
  (f : DX ⟶ DS) (g : DT ⟶ DS) (h : DY ⟶ DX) (e : DY ⟶ DT)
  (cX : Cone DX) (cS : Cone DS) (cT : Cone DT) (cY : Cone DY)
  (fL : cX.pt ⟶ cS.pt) (gL : cT.pt ⟶ cS.pt) (hL : cY.pt ⟶ cX.pt) (eL : cY.pt ⟶ cT.pt)

/-! ### The objects `K_i` and `K` -/

/-- The object `K_i` of `D^+(T_{i, étale})` for `i ≥ 0`: the total derived inverse image of
`K_0 ∈ D^+(T_{0, étale})` along the transition `T_i ⟶ T_0`. Inverse image is exact, so this is
`K_0` pulled back degreewise. -/
abbrev stageObj {i₀ : Iᵒᵖ} (K₀ : PlusAb (DT.obj i₀)) {i : Iᵒᵖ} (a : i ⟶ i₀) :
    PlusAb (DT.obj i) :=
  (derivedPullbackAb (DT.map a)).obj K₀

/-- The object `K` of `D^+(T_étale)`: the total derived inverse image of
`K_0 ∈ D^+(T_{0, étale})` along the projection `p_0 : T ⟶ T_0` of the cone on the system of the
`T_i`. -/
abbrev limitObj {i₀ : Iᵒᵖ} (K₀ : PlusAb (DT.obj i₀)) : PlusAb cT.pt :=
  (derivedPullbackAb (cT.π.app i₀)).obj K₀

/-! ### The two colimit diagrams and the stagewise base change map -/

/-- The term `s_i^{-1}H^p(Rg_{i, *}L)` on `S` of the colimit diagram of Stacks 0GIU for `g`. -/
abbrev derivedSourceTerm (p : ℤ) (i : Iᵒᵖ) (L : PlusAb (DT.obj i)) :
    Sheaf (smallEtaleTopology cS.pt) Ab.{u + 1} :=
  (smallEtalePullbackAb (cS.π.app i)).obj
    ((homologyAb (DS.obj i) p).obj ((derivedPushforwardAb (g.app i)).obj L))

/-- The term `r_i^{-1}H^p(Rh_{i, *}Re_i^{-1}L)` on `X` of the colimit diagram of Stacks 0GIU for
`h` and the derived inverse images `Re_i^{-1}L`. -/
abbrev derivedTargetTerm (p : ℤ) (i : Iᵒᵖ) (L : PlusAb (DT.obj i)) :
    Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1} :=
  (smallEtalePullbackAb (cX.π.app i)).obj
    ((homologyAb (DX.obj i) p).obj
      ((derivedPushforwardAb (h.app i)).obj ((derivedPullbackAb (e.app i)).obj L)))

/-- **The stagewise comparison of the two colimit diagrams of Stacks 0GIU**: the derived base
change map of the `i`-th square at `L`, read on degree-`p` cohomology sheaves and pulled back to
`X` along the projection `r_i`, the source being identified using exactness of `f_i^{-1}` and the
comparison `Stacks.EtaleCohomology.LimitBaseChange.projectionPullbackComparison` of the two
composite inverse images of the projection square `f ≫ s_i = r_i ≫ f_i`. -/
def derivedStageComparison (p : ℤ)
    (w : ∀ i : Iᵒᵖ, h.app i ≫ f.app i = e.app i ≫ g.app i)
    (hfL : ∀ i : Iᵒᵖ, fL ≫ cS.π.app i = cX.π.app i ≫ f.app i) (i : Iᵒᵖ)
    (L : PlusAb (DT.obj i)) :
    (smallEtalePullbackAb fL).obj (derivedSourceTerm g cS p i L) ⟶
      derivedTargetTerm h e cX p i L :=
  (LimitBaseChange.projectionPullbackComparison f cX cS fL hfL i).hom.app
      ((homologyAb (DS.obj i) p).obj ((derivedPushforwardAb (g.app i)).obj L)) ≫
    (smallEtalePullbackAb (cX.π.app i)).map
      ((Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso
            (smallEtalePullbackAb (f.app i)) p).inv.app
          ((derivedPushforwardAb (g.app i)).obj L) ≫
        (homologyAb (DX.obj i) p).map
          ((smallEtaleDerivedBaseChangeAb (f.app i) (g.app i) (h.app i) (e.app i) (w i)).app L))

/-- The stagewise comparison is invertible as soon as the derived base change map of the `i`-th
square is: the other two factors are isomorphisms. -/
theorem isIso_derivedStageComparison (p : ℤ)
    (w : ∀ i : Iᵒᵖ, h.app i ≫ f.app i = e.app i ≫ g.app i)
    (hfL : ∀ i : Iᵒᵖ, fL ≫ cS.π.app i = cX.π.app i ≫ f.app i) (i : Iᵒᵖ)
    (L : PlusAb (DT.obj i))
    (hi : IsIso ((smallEtaleDerivedBaseChangeAb (f.app i) (g.app i) (h.app i) (e.app i)
      (w i)).app L)) :
    IsIso (derivedStageComparison f g h e cX cS fL p w hfL i L) := by
  have := hi
  exact inferInstanceAs (IsIso (_ ≫ _))

/-! ### The comparison at the limit and the first reduction -/

/-- **The base change map of the limit square on cohomology sheaves**, the map
`f^{-1}R^pg_*M ⟶ R^ph_*e^{-1}M` of the source: the derived base change comparison of the limit
square at `M`, read on degree-`p` cohomology sheaves, the source being identified using exactness
of `f^{-1}`. -/
def derivedLimitComparison (wL : hL ≫ fL = eL ≫ gL) (p : ℤ) (M : PlusAb cT.pt) :
    (smallEtalePullbackAb fL).obj
        ((homologyAb cS.pt p).obj ((derivedPushforwardAb gL).obj M)) ⟶
      (homologyAb cX.pt p).obj
        ((derivedPushforwardAb hL).obj ((derivedPullbackAb eL).obj M)) :=
  (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso (smallEtalePullbackAb fL) p).inv.app
      ((derivedPushforwardAb gL).obj M) ≫
    (homologyAb cX.pt p).map ((smallEtaleDerivedBaseChangeAb fL gL hL eL wL).app M)

/-- **The first reduction of the proof of Stacks 0GJL**: it suffices to show that the base change
map `f^{-1}Rg_*M ⟶ Rh_*e^{-1}M` induces an isomorphism on cohomology sheaves, a map of the bounded
below derived category being invertible exactly when all its cohomology sheaf maps are. The
identification of the source of `H^p` of the base change map with `f^{-1}H^p(Rg_*M)`, which uses
exactness of `f^{-1}`, is an isomorphism, so it may be absorbed. -/
theorem isIso_of_forall_isIso_derivedLimitComparison (wL : hL ≫ fL = eL ≫ gL)
    (M : PlusAb cT.pt)
    (hM : ∀ p : ℤ, IsIso (derivedLimitComparison cX cS cT cY fL gL hL eL wL p M)) :
    IsIso ((smallEtaleDerivedBaseChangeAb fL gL hL eL wL).app M) := by
  rw [DerivedCategory.Plus.isIso_iff]
  intro p
  exact (isIso_comp_left_iff _ _).1 (hM p)

/-! ### The colimit presentations of Stacks 0GIU -/

/-- The two instances of the colimit assertion of Stacks 0GIU cited by the proof of Stacks 0GJL,
in a fixed degree `p`, together with their comparison: a diagram `Kg` over `J` presenting
`H^p(Rg_*K)` as `colim_j s_{σ j}^{-1}H^p(Rg_{σ j, *}K_{σ j})`, a diagram `Kh` presenting
`H^p(Rh_*Re^{-1}K)` as `colim_j r_{σ j}^{-1}H^p(Rh_{σ j, *}Re_{σ j}^{-1}K_{σ j})`, and a map `α`
of the inverse image of the first diagram to the second which realizes the stagewise comparisons
on terms and the limit comparison on the legs. -/
structure ColimitPresentation
    (w : ∀ i : Iᵒᵖ, h.app i ≫ f.app i = e.app i ≫ g.app i) (wL : hL ≫ fL = eL ≫ gL)
    (hfL : ∀ i : Iᵒᵖ, fL ≫ cS.π.app i = cX.π.app i ≫ f.app i)
    {i₀ : Iᵒᵖ} (K₀ : PlusAb (DT.obj i₀)) (J : Type w₁) [Category.{w₂} J] (σ : J → Iᵒᵖ)
    (τ : ∀ j : J, σ j ⟶ i₀) (p : ℤ) where
  /-- The colimit diagram of Stacks 0GIU for `g` and the objects `K_i`, on `S`. -/
  Kg : J ⥤ Sheaf (smallEtaleTopology cS.pt) Ab.{u + 1}
  /-- Its terms are the `s_{σ j}^{-1}H^p(Rg_{σ j, *}K_{σ j})`. -/
  ρg : ∀ j : J, Kg.obj j ≅ derivedSourceTerm g cS p (σ j) (stageObj K₀ (τ j))
  /-- Its legs to `H^p(Rg_*K)`. -/
  κg : Kg ⟶ (Functor.const J).obj
    ((homologyAb cS.pt p).obj ((derivedPushforwardAb gL).obj (limitObj cT K₀)))
  /-- The legs exhibit `H^p(Rg_*K)` as the colimit, which is the assertion of Stacks 0GIU. -/
  hκg : IsColimit (Cocone.mk _ κg)
  /-- The colimit diagram of Stacks 0GIU for `h` and the objects `Re_i^{-1}K_i`, on `X`. -/
  Kh : J ⥤ Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1}
  /-- Its terms are the `r_{σ j}^{-1}H^p(Rh_{σ j, *}Re_{σ j}^{-1}K_{σ j})`. -/
  ρh : ∀ j : J, Kh.obj j ≅ derivedTargetTerm h e cX p (σ j) (stageObj K₀ (τ j))
  /-- Its legs to `H^p(Rh_*Re^{-1}K)`. -/
  κh : Kh ⟶ (Functor.const J).obj
    ((homologyAb cX.pt p).obj ((derivedPushforwardAb hL).obj
      ((derivedPullbackAb eL).obj (limitObj cT K₀))))
  /-- The legs exhibit `H^p(Rh_*Re^{-1}K)` as the colimit, which is the assertion of Stacks 0GIU
  applied to `h` and the system of derived inverse images. -/
  hκh : IsColimit (Cocone.mk _ κh)
  /-- The comparison of the inverse image of the first diagram with the second. -/
  α : Kg ⋙ smallEtalePullbackAb fL ⟶ Kh
  /-- On terms the comparison is the stagewise base change map. -/
  hα : ∀ j : J, (smallEtalePullbackAb fL).map (ρg j).hom ≫
    derivedStageComparison f g h e cX cS fL p w hfL (σ j) (stageObj K₀ (τ j)) =
      α.app j ≫ (ρh j).hom
  /-- On the legs the comparison is the base change map of the limit square. -/
  hκ : ∀ j : J, (smallEtalePullbackAb fL).map (κg.app j) ≫
    derivedLimitComparison cX cS cT cY fL gL hL eL wL p (limitObj cT K₀) = α.app j ≫ κh.app j

/-! ### Stacks 0GJL -/

/-- **The second step of the proof of Stacks 0GJL**, which is the argument of Stacks 0EZT with the
reference to Stacks 0EYM replaced by one to Stacks 0GIU: in a fixed degree `p`, the base change
map `f^{-1}R^pg_*K ⟶ R^ph_*e^{-1}K` is an isomorphism. Inverse image is a left adjoint, so it
carries the colimit presentation of `H^p(Rg_*K)` to one of `f^{-1}H^p(Rg_*K)`; the comparison of
the two presentations is invertible on every term because the derived base change map of every
stage is; and a map of colimit cocones which is invertible on every term is invertible. -/
theorem isIso_derivedLimitComparison
    (w : ∀ i : Iᵒᵖ, h.app i ≫ f.app i = e.app i ≫ g.app i) (wL : hL ≫ fL = eL ≫ gL)
    (hfL : ∀ i : Iᵒᵖ, fL ≫ cS.π.app i = cX.π.app i ≫ f.app i)
    {i₀ : Iᵒᵖ} (K₀ : PlusAb (DT.obj i₀)) (J : Type w₁) [Category.{w₂} J] (σ : J → Iᵒᵖ)
    (τ : ∀ j : J, σ j ⟶ i₀) (p : ℤ)
    (P : ColimitPresentation f g h e cX cS cT cY fL gL hL eL w wL hfL K₀ J σ τ p)
    (hstage : ∀ (i : Iᵒᵖ) (a : i ⟶ i₀),
      IsIso ((smallEtaleDerivedBaseChangeAb (f.app i) (g.app i) (h.app i) (e.app i) (w i)).app
        (stageObj K₀ a))) :
    IsIso (derivedLimitComparison cX cS cT cY fL gL hL eL wL p (limitObj cT K₀)) := by
  have := (smallEtaleAdjunctionAb fL).leftAdjoint_preservesColimits
  refine LimitBaseChange.isIso_of_isColimit
    (isColimitOfPreserves (smallEtalePullbackAb fL) P.hκg) P.hκh P.α
    (fun j => ?_) _ fun j => P.hκ j
  have h₁ := isIso_derivedStageComparison f g h e cX cS fL p w hfL (σ j) (stageObj K₀ (τ j))
      (hstage (σ j) (τ j))
  have h₂ : IsIso (P.α.app j ≫ (P.ρh j).hom) := by rw [← P.hα j]; infer_instance
  exact IsIso.of_isIso_comp_right (P.α.app j) (P.ρh j).hom

/-- **Stacks 0GJL.** Let `(X_i, Y_i, S_i, T_i, f_i, h_i, e_i, g_i)` be an inverse system of
squares as in the setup of Stacks 0EZT, with limit square `(X, Y, S, T, f, h, e, g)`. Let
`0 ∈ I`, let `K_0` be an object of `D^+(T_{0, étale})`, let `K_i` be the pullback of `K_0` to
`T_i` for `i ≥ 0` and `K` the pullback of `K_0` to `T`. If `f_i^{-1}Rg_{i, *}K_i =
Rh_{i, *}e_i^{-1}K_i` for all `i ≥ 0`, then `f^{-1}Rg_*K = Rh_*e^{-1}K`. -/
@[stacks 0GJL "if the derived base change map of the `i`-th square is an isomorphism at `K_i` \
for all `i ≥ 0`, then the derived base change map of the limit square is an isomorphism at `K`, \
with `K_i` and `K` the derived inverse images of `K_0 ∈ D^+(T_{0, étale})` to `T_i` and to `T`. \
Both steps of the source's proof are carried out: the reduction to cohomology sheaves is \
`isIso_of_forall_isIso_derivedLimitComparison` and the colimit argument of Stacks 0EZT, with the \
reference to Stacks 0EYM replaced by one to Stacks 0GIU, is `isIso_derivedLimitComparison`. \
EXTRA HYPOTHESIS: the single bundled hypothesis `P` grants, in each degree `p`, the two \
instances of the colimit assertion of Stacks 0GIU that the source's proof cites — `H^p(Rg_*K) = \
colim_{i ≥ 0} s_i^{-1}H^p(Rg_{i, *}K_i)` and `H^p(Rh_*Re^{-1}K) = colim_{i ≥ 0} \
r_i^{-1}H^p(Rh_{i, *}Re_i^{-1}K_i)` — presented as in \
`Stacks.EtaleCohomology.LimitBaseChange.isIso_higherBaseChangeMapAb_limit`, namely a diagram \
with terms identified with `derivedSourceTerm` resp. `derivedTargetTerm` and a colimit cocone \
with the stated vertex, together with the comparison of the two diagrams and its compatibility \
with terms and legs, which is the pasting of base change maps of Stacks 0E47. That colimit \
assertion is NOT available in this repository: \
`Stacks.EtaleCohomology.LimitHigherDirectImage.pullbackProjectionMap`, the carrier of Stacks \
0GIU, states in its own clause string that it is not proved and that the colimit cannot even be \
formed, both because the colimit assertion of Stacks 0EYM is unproved and because the cocycle \
compatibility of Stacks 0E47 is unavailable for the bounded below derived base change map. The \
hypothesis does not restate the goal: it says nothing about any base change map being \
invertible, only that the two sides are the asserted colimits and that the comparison maps \
assemble."]
theorem isIso_smallEtaleDerivedBaseChangeAb_limit
    (w : ∀ i : Iᵒᵖ, h.app i ≫ f.app i = e.app i ≫ g.app i) (wL : hL ≫ fL = eL ≫ gL)
    (hfL : ∀ i : Iᵒᵖ, fL ≫ cS.π.app i = cX.π.app i ≫ f.app i)
    {i₀ : Iᵒᵖ} (K₀ : PlusAb (DT.obj i₀)) (J : Type w₁) [Category.{w₂} J] (σ : J → Iᵒᵖ)
    (τ : ∀ j : J, σ j ⟶ i₀)
    (P : ∀ p : ℤ,
      ColimitPresentation f g h e cX cS cT cY fL gL hL eL w wL hfL K₀ J σ τ p)
    (hstage : ∀ (i : Iᵒᵖ) (a : i ⟶ i₀),
      IsIso ((smallEtaleDerivedBaseChangeAb (f.app i) (g.app i) (h.app i) (e.app i) (w i)).app
        (stageObj K₀ a))) :
    IsIso ((smallEtaleDerivedBaseChangeAb fL gL hL eL wL).app (limitObj cT K₀)) :=
  isIso_of_forall_isIso_derivedLimitComparison cX cS cT cY fL gL hL eL wL (limitObj cT K₀)
    fun p => isIso_derivedLimitComparison f g h e cX cS cT cY fL gL hL eL w wL hfL K₀ J σ τ p
      (P p) hstage

end Stacks.EtaleCohomology.LimitBaseChangeDerived

end
