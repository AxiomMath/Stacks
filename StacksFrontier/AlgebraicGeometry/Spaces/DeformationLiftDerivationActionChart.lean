module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceRingSurjectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpChartLiftComorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpLiftReduction

/-!
# Morphisms into a thickening realizing a comorphism-level solution, free of Theorem 04KL

Let `Z ⊆ X` be a thickening of algebraic spaces and `c : X ⟶ W` a morphism.  A solution of the
lifting problem at the level of comorphisms — a map of sheaves of rings agreeing with the
comorphism of `c` on the functions read from the base and reducing to the comorphism of `c|_Z` —
is induced by a morphism of algebraic spaces, and as a consequence the existence clause of
[Stacks Project, Tag 04D0] holds at the source's hypotheses.

## Main results

* `AlgebraicGeometry.Space.isChartLift_thickeningLiftChartHom`: both clauses of the lifting
  condition for the morphism of charts attached to a solution of the lifting problem, for an
  arbitrary thickening.
* `AlgebraicGeometry.Space.exists_hom_of_thickeningLiftSolution`: **a comorphism-level solution
  of the lifting problem is induced by a morphism of algebraic spaces**.
* `AlgebraicGeometry.Space.exists_hom_structureSharpThroughThickeningAt_eq`: **the comorphism of
  that morphism is the given solution**, on the nose and not merely chartwise, and
  `AlgebraicGeometry.Space.exists_hom_restrictedSharpThroughThickening_eq` is the same statement
  in the spelling in which a pair of morphisms agreeing on the thickening becomes a
  `Stacks.Sites.LiftDifferenceData`.
* `AlgebraicGeometry.Space.existsUnique_hom_structureSharpThroughThickeningAt_eq`: existence
  and uniqueness of that morphism for a first order thickening.
* `exists_hom_restrictedSharpThroughThickening_eq_restrictedLiftSolutionOfHom_of_square`:
  **the existence clause of [Stacks Project, Tag 04D0] at the source's hypotheses**.  A prescribed
  `𝒪_Z`-linear map `θ` is realised by a morphism over the base agreeing with the given one on the
  thickening, its comorphism being the modification of the given one by the derivation attached
  to `θ`, the solution `AlgebraicGeometry.Space.restrictedLiftSolutionOfHom`.

## References

* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0)
* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
* [Stacks Project, Tag 05ZN](https://stacks.math.columbia.edu/tag/05ZN)
* [Stacks Project, Tag 0611](https://stacks.math.columbia.edu/tag/0611)
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
-/

@[expose] public section

open CategoryTheory Opposite
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space


section ChartLiftBypass

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X W Bas : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

/-- **Both clauses of the lifting condition hold for the morphism of charts attached to a
solution of the lifting problem.** For a thickening `Z ⊆ X`, a morphism `c : X ⟶ W`, a solution
`a` of the lifting problem agreeing with the comorphism of `c` on the functions read from `Bas`
and reducing to the comorphism of `c|_Z`, the morphism of charts which `a` attaches over an
affine chart of `W` carrying an affine chart diagram over `r` is a section of the sheaf of lifts
of [Stacks Project, Tag 061D]. -/
theorem isChartLift_thickeningLiftChartHom (hZ : IsThickening B S hS X Z.1) (c : X ⟶ W)
    (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c) (r : W ⟶ Bas)
    (hbase : ∀ (V : SmallEtale B S hS W.1)
        (s : ToType ((structureRingSheafInverseImage B S hS r).obj.obj (op V))),
      a.hom.app (op V) ((structureSharpRingInverseImage B S hS r).hom.app (op V) s) =
        (structureSharpThroughThickening B S hS Z c).hom.app (op V)
          ((structureSharpRingInverseImage B S hS r).hom.app (op V) s))
    (hred : a ≫ thickeningLiftReduction B S hS Z c =
      structureSharp B S hS (subspaceInclusion B S hS X Z ≫ c))
    (p : X ⟶ Bas) (hp : c.hom ≫ r.hom = p.hom) (az : Z.1.toFunctor ⟶ W.1)
    (haz : Z.1.ι ≫ c.hom = az) (V : SmallEtale B S hS W.1)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V))]
    (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op)
    (ψ : (SmallEtale.toOver B S hS X.1).obj j.right.unop ⟶
      (SmallEtale.toOver B S hS W.1).obj V)
    (hV : HasAffineChartDiagram B S hS r V)
    (hψ : (BigFppfOver.toScheme B S hS).map ψ =
      thickeningLiftChartHom B S hS Z hZ c a V j) :
    IsChartLift B S hS p r az j.right.unop (yoneda.map ψ ≫ V.1.hom) := by
  obtain ⟨V', qq, hqq, hV'aff⟩ := hV.2
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((SmallEtale.toOver B S hS Bas.1).obj V')) := hV'aff
  let D : ChartDiagram B S hS W.1 Bas.1 r.hom := ⟨V, V', qq, hqq.symm⟩
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS W.1).obj (indexOfChartDiagram B S hS r D).right.unop)) :=
    (inferInstance : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS W.1).obj V)))
  refine ⟨?_, fun Ww k t hkt ↦ ?_⟩
  · refine (yoneda_map_comp_chart_hom_comp_eq B S hS Z hZ c a r V'
      (indexOfChartDiagram B S hS r D) j (fun s ↦ hbase _ s) ψ hψ).trans ?_
    rw [← hp]
  · refine (yoneda_map_comp_chart_hom_eq_restriction B S hS Z hZ c a hred V j ψ hψ
      Ww k t hkt).trans ?_
    rw [haz]

/-- **A comorphism-level solution of the lifting problem is induced by a morphism of algebraic
spaces, with no appeal to Properties of Spaces, Theorem [Stacks Project, Tag 04KL].**

Let `Z ⊆ X` be a thickening of algebraic spaces, `c : X ⟶ W`, `r : W ⟶ Bas`, and let `a` be a
solution of the lifting problem which agrees with the comorphism of `c` on the regular functions
read from `Bas` (`hbase`) and whose reduction is the comorphism of `c|_Z` (`hred`). Then there is
a morphism `ε : X ⟶ W` over `Bas` restricting to `c|_Z` on `Z`, whose restriction to any chart of
`X` carrying an index over any affine chart of `W` is the morphism of charts attached to `a`. -/
theorem exists_hom_of_thickeningLiftSolution (hZ : IsThickening B S hS X Z.1) (c : X ⟶ W)
    (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c) (r : W ⟶ Bas)
    (hbase : ∀ (V : SmallEtale B S hS W.1)
        (s : ToType ((structureRingSheafInverseImage B S hS r).obj.obj (op V))),
      a.hom.app (op V) ((structureSharpRingInverseImage B S hS r).hom.app (op V) s) =
        (structureSharpThroughThickening B S hS Z c).hom.app (op V)
          ((structureSharpRingInverseImage B S hS r).hom.app (op V) s))
    (hred : a ≫ thickeningLiftReduction B S hS Z c =
      structureSharp B S hS (subspaceInclusion B S hS X Z ≫ c))
    (p : X ⟶ Bas) (hp : c.hom ≫ r.hom = p.hom) (az : Z.1.toFunctor ⟶ W.1)
    (haz : Z.1.ι ≫ c.hom = az) :
    ∃ ε : X.1 ⟶ W.1, ε ≫ r.hom = p.hom ∧ Z.1.ι ≫ ε = az ∧
      ∀ (V : SmallEtale B S hS W.1)
        [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V))]
        (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op)
        (ψ : (SmallEtale.toOver B S hS X.1).obj j.right.unop ⟶
          (SmallEtale.toOver B S hS W.1).obj V),
        (BigFppfOver.toScheme B S hS).map ψ = thickeningLiftChartHom B S hS Z hZ c a V j →
        j.right.unop.1.hom ≫ ε = yoneda.map ψ ≫ V.1.hom :=
  exists_hom_eq_thickeningLiftChartSiteHom B S hS Z hZ c a r hbase p r az
    fun V _ j ψ hV hψ ↦
      isChartLift_thickeningLiftChartHom B S hS Z hZ c a r hbase hred p hp az haz V j ψ hV hψ

/-! ### The glued morphism's comorphism is the prescribed solution -/

/-- **A solution of the lifting problem is the comorphism of a morphism of algebraic spaces which
realizes it, with no appeal to Properties of Spaces, Theorem [Stacks Project, Tag 04KL].**

Let `Z ⊆ X` be a thickening of algebraic spaces, `c : X ⟶ W`, `r : W ⟶ Bas`, and let `a` be a
solution of the lifting problem which agrees with the comorphism of `c` on the regular functions
read from `Bas` (`hbase`) and whose reduction is the comorphism of `c|_Z` (`hred`). Then there is
a morphism `c' : X ⟶ W` over `Bas`, agreeing with `c` on `Z`, whose comorphism read in the common
target `(i ≫ c)_*(i^{-1}𝒪_X)` of the morphisms agreeing on the thickening *is* `a`. -/
theorem exists_hom_structureSharpThroughThickeningAt_eq (hZ : IsThickening B S hS X Z.1)
    (c : X ⟶ W) (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    (r : W ⟶ Bas)
    (hbase : ∀ (V : SmallEtale B S hS W.1)
        (s : ToType ((structureRingSheafInverseImage B S hS r).obj.obj (op V))),
      a.hom.app (op V) ((structureSharpRingInverseImage B S hS r).hom.app (op V) s) =
        (structureSharpThroughThickening B S hS Z c).hom.app (op V)
          ((structureSharpRingInverseImage B S hS r).hom.app (op V) s))
    (hred : a ≫ thickeningLiftReduction B S hS Z c =
      structureSharp B S hS (subspaceInclusion B S hS X Z ≫ c))
    (p : X ⟶ Bas) (hp : c.hom ≫ r.hom = p.hom) :
    ∃ (c' : X ⟶ W) (hcc : subspaceInclusion B S hS X Z ≫ c' =
        subspaceInclusion B S hS X Z ≫ c),
      c'.hom ≫ r.hom = p.hom ∧
        structureSharpThroughThickeningAt B S hS Z c'
          (subspaceInclusion B S hS X Z ≫ c) hcc = a := by
  obtain ⟨ε, hsrc, hres, hchart⟩ :=
    exists_hom_of_thickeningLiftSolution B S hS Z hZ c a r hbase hred p hp
      (Z.1.ι ≫ c.hom) rfl
  refine ⟨_, ObjectProperty.hom_ext _ hres, hsrc, ?_⟩
  exact structureSharpThroughThickeningAt_eq_of_thickeningLiftChartHom B S hS Z hZ c _ _ a hred r
    hbase fun Q hQaff j ψ hψ ↦ @hchart Q hQaff j ψ hψ

/-- **A prescribed solution of the lifting problem is realized by exactly one morphism, with no
appeal to Properties of Spaces, Theorem [Stacks Project, Tag 04KL]**, for a first order
thickening. Given a solution `a` of the lifting problem which is a map of algebras over the base
(`hbase`) and fits the source's commuting square with the two closed immersions (`hred`), there
is exactly one morphism `c' : X ⟶ W` over `Bas` agreeing with `c` on `Z` whose comorphism is
`a`. -/
theorem existsUnique_hom_structureSharpThroughThickeningAt_eq
    (hZ : IsFirstOrderThickening B S hS X Z.1) (c : X ⟶ W)
    (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c) (r : W ⟶ Bas)
    (hbase : ∀ (V : SmallEtale B S hS W.1)
        (s : ToType ((structureRingSheafInverseImage B S hS r).obj.obj (op V))),
      a.hom.app (op V) ((structureSharpRingInverseImage B S hS r).hom.app (op V) s) =
        (structureSharpThroughThickening B S hS Z c).hom.app (op V)
          ((structureSharpRingInverseImage B S hS r).hom.app (op V) s))
    (hred : a ≫ thickeningLiftReduction B S hS Z c =
      structureSharp B S hS (subspaceInclusion B S hS X Z ≫ c))
    (p : X ⟶ Bas) (hp : c.hom ≫ r.hom = p.hom) :
    ∃! c' : X ⟶ W, ∃ hcc : subspaceInclusion B S hS X Z ≫ c' =
        subspaceInclusion B S hS X Z ≫ c,
      c'.hom ≫ r.hom = p.hom ∧
        structureSharpThroughThickeningAt B S hS Z c'
          (subspaceInclusion B S hS X Z ≫ c) hcc = a := by
  obtain ⟨c', hcc, hsrc, hAt⟩ :=
    exists_hom_structureSharpThroughThickeningAt_eq B S hS Z hZ.1 c a r hbase hred p hp
  refine ⟨c', ⟨hcc, hsrc, hAt⟩, ?_⟩
  rintro c'' ⟨hcc'', -, hAt''⟩
  exact eq_of_structureSharpThroughThickeningAt_eq B S hS Z hZ c'' c'
    (subspaceInclusion B S hS X Z ≫ c) hcc'' hcc (hAt''.trans hAt.symm)

/-- **The same comparison in the spelling the difference of two lifts consumes.** For a closed
subspace `W₀ ⊆ W` and a morphism `e₀ : Z ⟶ W₀` that `c` restricts to, a solution `g` of the
lifting problem read on the small étale site of `W₀` is the transported comorphism of a morphism
`c' : X ⟶ W` over `Bas` agreeing with `c` on `Z`. -/
theorem exists_hom_restrictedSharpThroughThickening_eq (hZ : IsThickening B S hS X Z.1)
    (c : X ⟶ W) (W₀ : ClosedSubspaces B S hS W.1)
    (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
    (hce : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    (g : structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W W₀) ⟶
      restrictedThickeningLiftRingSheaf B S hS Z W₀ e₀)
    (r : W ⟶ Bas)
    (hbase : ∀ (V : SmallEtale B S hS W.1)
        (s : ToType ((structureRingSheafInverseImage B S hS r).obj.obj (op V))),
      (thickeningLiftOfIndex B S hS Z c (e₀ ≫ subspaceInclusion B S hS W W₀) hce
            (liftRestrictedSharpThroughThickening B S hS Z W₀ e₀ g)).hom.app (op V)
          ((structureSharpRingInverseImage B S hS r).hom.app (op V) s) =
        (structureSharpThroughThickening B S hS Z c).hom.app (op V)
          ((structureSharpRingInverseImage B S hS r).hom.app (op V) s))
    (hred : thickeningLiftOfIndex B S hS Z c (e₀ ≫ subspaceInclusion B S hS W W₀) hce
          (liftRestrictedSharpThroughThickening B S hS Z W₀ e₀ g) ≫
        thickeningLiftReduction B S hS Z c =
      structureSharp B S hS (subspaceInclusion B S hS X Z ≫ c))
    (p : X ⟶ Bas) (hp : c.hom ≫ r.hom = p.hom) :
    ∃ (c' : X ⟶ W) (hcc : subspaceInclusion B S hS X Z ≫ c' =
        e₀ ≫ subspaceInclusion B S hS W W₀),
      c'.hom ≫ r.hom = p.hom ∧
        restrictedSharpThroughThickening B S hS Z W₀ c' e₀ hcc = g := by
  obtain ⟨c', hcc, hsrc, hAt⟩ :=
    exists_hom_structureSharpThroughThickeningAt_eq B S hS Z hZ c _ r hbase hred p hp
  replace hcc := hcc.trans hce
  refine ⟨c', hcc, hsrc, ?_⟩
  refine liftRestrictedSharpThroughThickening_injective B S hS Z W₀ e₀ _ g ?_
  refine (liftRestrictedSharpThroughThickening_restrictedSharpThroughThickening B S hS Z W₀ c' e₀
    hcc).trans ?_
  exact structureSharpThroughThickeningAt_eq_of_eq_thickeningLiftOfIndex B S hS Z c c'
    (e₀ ≫ subspaceInclusion B S hS W W₀) hce hcc _ hAt

/-! ### The lift realizing a prescribed linear map: the existence clause of Tag 04D0 -/

section DerivationExistence

open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback

/-- **The solution of the lifting problem attached to an `𝒪_X`-linear map `θ`**, in the
restricted spelling.  For a thickening `Z ⊆ X` of first order, a closed subspace `W₀ ⊆ W` with
`e₀ : Z ⟶ W₀` that `c : X ⟶ W` restricts to, and an `𝒪_Z`-linear map
`θ : (e₀)^*Ω_{W₀/Bas₀} ⟶ 𝒞_{Z/X}`, this is the map

`g = c^♯ − ι ∘ D ∘ j^♯ : j^{-1}𝒪_W ⟶ (e₀)_*(i^{-1}𝒪_X)`

of the source's proof of [Stacks Project, Tag 04D0], where `D = d_{W₀/Bas₀} ∘ θ` is the
derivation attached to `θ` by Equation (0619).  It is
`AlgebraicGeometry.Space.liftDifferenceDataOfHom` taken at the transported comorphism of `c`. -/
noncomputable def restrictedLiftSolutionOfHom (hZ : IsFirstOrderThickening B S hS X Z.1)
    (c : X ⟶ W) (W₀ : ClosedSubspaces B S hS W.1)
    (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
    (hce : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    {Bas₀ : AlgebraicSpaces B S hS}
    (b : (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS) ⟶ Bas₀)
    (θ : (modulePullback B S hS e₀).obj (sheafOfDifferentials B S hS b) ⟶
      conormalModule B S hS X Z) :
    structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W W₀) ⟶
      restrictedThickeningLiftRingSheaf B S hS Z W₀ e₀ :=
  (liftDifferenceDataOfHom B S hS b e₀ (conormalModule B S hS X Z)
    (E := restrictedSquareZeroValues B S hS Z W₀ e₀ hZ)
    (restrictedSharpThroughThickening B S hS Z W₀ c e₀ hce)
    (fun _ x m ↦ restrictedSquareZeroValues_ι_smul B S hS Z W₀ e₀ hZ c hce x m) θ).g

/-- **Moving the comorphism of `c` by the derivation attached to `θ` does not change its
reduction**, so the solution still restricts to `e₀ ≫ j` on the thickening.  The difference of
the two solutions takes its values in the ideal `(e₀)_*𝒞_{Z/X}`, which the reduction kills, by
`AlgebraicGeometry.Space.app_reduction_restrictedSquareZeroValues_ι_eq_zero`. -/
theorem restrictedLiftSolutionOfHom_comp_reduction
    (hZ : IsFirstOrderThickening B S hS X Z.1) (c : X ⟶ W)
    (W₀ : ClosedSubspaces B S hS W.1)
    (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
    (hce : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    {Bas₀ : AlgebraicSpaces B S hS}
    (b : (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS) ⟶ Bas₀)
    (θ : (modulePullback B S hS e₀).obj (sheafOfDifferentials B S hS b) ⟶
      conormalModule B S hS X Z) :
    restrictedLiftSolutionOfHom B S hS Z hZ c W₀ e₀ hce b θ ≫
        pullbackRingSheafMap (SmallEtale.topology B S hS
            (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
          (smallToposMorphismTypeU B S hS e₀).pushforward
          (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z)) =
      structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀) ≫
        structureSharp B S hS e₀ := by
  let := isLocallySurjective_structureSharpRingInverseImage B S hS
    (subspaceInclusion B S hS W W₀) W₀.2.2
  exact (liftDifferenceDataOfHom_g_comp_eq B S hS b e₀ (conormalModule B S hS X Z)
      (E := restrictedSquareZeroValues B S hS Z W₀ e₀ hZ)
      (restrictedSharpThroughThickening B S hS Z W₀ c e₀ hce)
      (fun _ x m ↦ restrictedSquareZeroValues_ι_smul B S hS Z W₀ e₀ hZ c hce x m) θ _
      (app_reduction_restrictedSquareZeroValues_ι_eq_zero B S hS Z W₀ e₀ hZ)).trans
    (restrictedSharpThroughThickening_comp_reduction_structureSharp B S hS Z W₀ e₀ c hce)

/-- **The solution attached to `θ` agrees with the comorphism of `c` on the regular functions
read from the base**, which is what makes the morphism it induces a morphism over `Bas`.

The hypothesis `hD` is that the derivation attached to `θ` by Equation (0619) kills the
functions read from `Bas` along `r` — the source's "`D` is an `𝒪_B`-derivation", which is the
field `d_app` of Equation (0619) once the two readings of the pullback are identified by the
square relating `r` to `b`. -/
theorem inverseImage_comp_restrictedLiftSolutionOfHom_eq
    (hZ : IsFirstOrderThickening B S hS X Z.1) (c : X ⟶ W)
    (W₀ : ClosedSubspaces B S hS W.1)
    (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
    (hce : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    {Bas₀ : AlgebraicSpaces B S hS}
    (b : (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS) ⟶ Bas₀)
    (θ : (modulePullback B S hS e₀).obj (sheafOfDifferentials B S hS b) ⟶
      conormalModule B S hS X Z)
    (r : W ⟶ Bas)
    (hD : ∀ (V : (SmallEtale B S hS
          (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
        (x : ToType (((inverseImageRingFunctor (smallToposMorphismTypeU B S hS
            (subspaceInclusion B S hS W W₀))).obj
          (structureRingSheafInverseImage B S hS r)).obj.obj V)),
      derivationFamilyOfHom B S hS b e₀ (conormalModule B S hS X Z) θ V
        ((structureSharpRingInverseImage B S hS
            (subspaceInclusion B S hS W W₀)).hom.app V
          (((inverseImageRingFunctor (smallToposMorphismTypeU B S hS
                (subspaceInclusion B S hS W W₀))).map
              (structureSharpRingInverseImage B S hS r)).hom.app V x)) = 0) :
    (inverseImageRingFunctor (smallToposMorphismTypeU B S hS
          (subspaceInclusion B S hS W W₀))).map
        (structureSharpRingInverseImage B S hS r) ≫
      restrictedLiftSolutionOfHom B S hS Z hZ c W₀ e₀ hce b θ =
    (inverseImageRingFunctor (smallToposMorphismTypeU B S hS
          (subspaceInclusion B S hS W W₀))).map
        (structureSharpRingInverseImage B S hS r) ≫
      restrictedSharpThroughThickening B S hS Z W₀ c e₀ hce := by
  let := isLocallySurjective_structureSharpRingInverseImage B S hS
    (subspaceInclusion B S hS W W₀) W₀.2.2
  exact comp_liftDifferenceDataOfHom_g_eq B S hS b e₀ (conormalModule B S hS X Z)
    (E := restrictedSquareZeroValues B S hS Z W₀ e₀ hZ)
    (restrictedSharpThroughThickening B S hS Z W₀ c e₀ hce)
    (fun _ x m ↦ restrictedSquareZeroValues_ι_smul B S hS Z W₀ e₀ hZ c hce x m) θ _ hD

/-- **The existence clause of [Stacks Project, Tag 04D0], with no appeal to Properties of
Spaces, Theorem [Stacks Project, Tag 04KL].**

Let `Z ⊆ X` be a first order thickening of algebraic spaces, `W₀ ⊆ W` a closed subspace,
`e₀ : Z ⟶ W₀` a morphism that `c : X ⟶ W` restricts to, `r : W ⟶ Bas` and `p : X ⟶ Bas` with
`c` over `Bas`.  Let `θ : (e₀)^*Ω_{W₀/Bas₀} ⟶ 𝒞_{Z/X}` be an `𝒪_Z`-linear map whose attached
derivation kills the functions read from `Bas` (`hD`).  Then there is a morphism `c' : X ⟶ W`
over `Bas`, agreeing with `c` on `Z`, whose comorphism read in the common target of the
morphisms agreeing on the thickening is exactly the modification
`c^♯ − ι ∘ (d_{W₀/Bas₀} ∘ θ) ∘ j^♯` of the comorphism of `c` by the derivation attached to `θ`.
The uniqueness half of the tag is not claimed here. -/
theorem exists_hom_restrictedSharpThroughThickening_eq_restrictedLiftSolutionOfHom
    (hZ : IsFirstOrderThickening B S hS X Z.1) (c : X ⟶ W)
    (W₀ : ClosedSubspaces B S hS W.1)
    (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
    (hce : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    {Bas₀ : AlgebraicSpaces B S hS}
    (b : (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS) ⟶ Bas₀)
    (θ : (modulePullback B S hS e₀).obj (sheafOfDifferentials B S hS b) ⟶
      conormalModule B S hS X Z)
    (r : W ⟶ Bas)
    (hD : ∀ (V : (SmallEtale B S hS
          (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
        (x : ToType (((inverseImageRingFunctor (smallToposMorphismTypeU B S hS
            (subspaceInclusion B S hS W W₀))).obj
          (structureRingSheafInverseImage B S hS r)).obj.obj V)),
      derivationFamilyOfHom B S hS b e₀ (conormalModule B S hS X Z) θ V
        ((structureSharpRingInverseImage B S hS
            (subspaceInclusion B S hS W W₀)).hom.app V
          (((inverseImageRingFunctor (smallToposMorphismTypeU B S hS
                (subspaceInclusion B S hS W W₀))).map
              (structureSharpRingInverseImage B S hS r)).hom.app V x)) = 0)
    (p : X ⟶ Bas) (hp : c.hom ≫ r.hom = p.hom) :
    ∃ (c' : X ⟶ W) (hcc : subspaceInclusion B S hS X Z ≫ c' =
        e₀ ≫ subspaceInclusion B S hS W W₀),
      c'.hom ≫ r.hom = p.hom ∧
        restrictedSharpThroughThickening B S hS Z W₀ c' e₀ hcc =
          restrictedLiftSolutionOfHom B S hS Z hZ c W₀ e₀ hce b θ :=
  exists_hom_restrictedSharpThroughThickening_eq B S hS Z hZ.1 c W₀ e₀ hce
    (restrictedLiftSolutionOfHom B S hS Z hZ c W₀ e₀ hce b θ) r
    (fun V s ↦ app_thickeningLiftOfIndex_eq_structureSharpThroughThickening B S hS Z c
      (e₀ ≫ subspaceInclusion B S hS W W₀) hce _ r
      (fun V' s' ↦ app_liftRestrictedSharpThroughThickening_eq B S hS Z W₀ c e₀ hce r _
        (inverseImage_comp_restrictedLiftSolutionOfHom_eq B S hS Z hZ c W₀ e₀ hce b θ r hD)
        (op V') s')
      V s)
    (thickeningLiftOfIndex_comp_reduction B S hS Z c
      (e₀ ≫ subspaceInclusion B S hS W W₀) hce _
      (liftRestrictedSharpThroughThickening_comp_reduction B S hS Z W₀ e₀ _
        (restrictedLiftSolutionOfHom_comp_reduction B S hS Z hZ c W₀ e₀ hce b θ)))
    p hp

/-- **The derivation attached to `θ` by Equation (0619) kills the regular functions read from
the base**, so the hypothesis `hD` above is not a standing assumption but a consequence of the
geometry. -/
theorem derivationFamilyOfHom_app_base_eq_zero
    (W₀ : ClosedSubspaces B S hS W.1)
    (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
    {Bas₀ : AlgebraicSpaces B S hS}
    (b : (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS) ⟶ Bas₀)
    (θ : (modulePullback B S hS e₀).obj (sheafOfDifferentials B S hS b) ⟶
      conormalModule B S hS X Z)
    (r : W ⟶ Bas) (ib : Bas₀ ⟶ Bas)
    (hsq : subspaceInclusion B S hS W W₀ ≫ r = b ≫ ib)
    (V : (SmallEtale B S hS
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (x : ToType (((smallEtaleInverseImageRing B S hS
        (subspaceInclusion B S hS W W₀)).obj
      (inverseImageStructureSheaf B S hS r)).obj.obj V)) :
    derivationFamilyOfHom B S hS b e₀ (conormalModule B S hS X Z) θ V
      ((structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).hom.app V
        (((inverseImageRingFunctor (smallToposMorphismTypeU B S hS
              (subspaceInclusion B S hS W W₀))).map
            (structureSharpRingInverseImage B S hS r)).hom.app V x)) = 0 := by
  have hval : (structureSharpRingInverseImage B S hS
        (subspaceInclusion B S hS W W₀)).hom.app V
      (((inverseImageRingFunctor (smallToposMorphismTypeU B S hS
            (subspaceInclusion B S hS W W₀))).map
          (structureSharpRingInverseImage B S hS r)).hom.app V x) =
      (structureSharpInverseImage B S hS b).hom.app V
        (((smallEtaleInverseImageRing B S hS b).map
            (structureSharpInverseImage B S hS ib)).hom.app V
          ((smallEtaleRingedToposHom_squareInverseImageRingIso B S hS hsq).hom.hom.app V x)) :=
    (congrArg (fun z ↦ (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).hom.app V z)
        (app_inverseImage_structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS W W₀) r V x)).trans
      ((structureSharpRingInverseImage_app B S hS
            (subspaceInclusion B S hS W W₀) V _).trans
        (ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg
          (h := smallEtaleRingedToposHom_squareInverseImageRingIso_fSharpInverseImage B S hS hsq)
            (fun m ↦ m.hom)) V) x).symm)
  rw [hval]
  exact derivationFamilyOfHom_app B S hS b e₀ (conormalModule B S hS X Z) θ V _

/-- **The existence clause of [Stacks Project, Tag 04D0] at the source's hypotheses, with no
appeal to Properties of Spaces, Theorem [Stacks Project, Tag 04KL].**

Let `Z ⊆ X` be a first order thickening of algebraic spaces, `W₀ ⊆ W` a closed subspace with
inclusion `j`, `e₀ : Z ⟶ W₀` a morphism that `c : X ⟶ W` restricts to, and let `c` be a morphism
over `Bas` along `r : W ⟶ Bas`.  Let `b : W₀ ⟶ Bas₀` and `ib : Bas₀ ⟶ Bas` satisfy the square
`j ≫ r = b ≫ ib`, so that the differentials `Ω_{W₀/Bas₀}` are the ones of the source.  Then
**every** `𝒪_Z`-linear map `θ : (e₀)^*Ω_{W₀/Bas₀} ⟶ 𝒞_{Z/X}` is realized: there is a morphism
`c' : X ⟶ W` over `Bas`, agreeing with `c` on `Z`, whose comorphism read in the common target of
the morphisms agreeing on the thickening is the modification
`c^♯ − ι ∘ (d_{W₀/Bas₀} ∘ θ) ∘ j^♯` of the comorphism of `c` by the derivation attached to `θ`.
The uniqueness half of the tag is not claimed here. -/
@[stacks 04D0 "the existence clause at the source's hypotheses: a prescribed O_X-linear map \
theta is realized by a morphism over the base agreeing with the given one on the thickening, \
its comorphism being the modification of the given one by the derivation d o theta of \
Equation 0619 -- with no appeal to Theorem 04KL. Uniqueness is not claimed here"]
theorem exists_hom_restrictedSharpThroughThickening_eq_restrictedLiftSolutionOfHom_of_square
    (hZ : IsFirstOrderThickening B S hS X Z.1) (c : X ⟶ W)
    (W₀ : ClosedSubspaces B S hS W.1)
    (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
    (hce : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    {Bas₀ : AlgebraicSpaces B S hS}
    (b : (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS) ⟶ Bas₀)
    (θ : (modulePullback B S hS e₀).obj (sheafOfDifferentials B S hS b) ⟶
      conormalModule B S hS X Z)
    (r : W ⟶ Bas) (ib : Bas₀ ⟶ Bas)
    (hsq : subspaceInclusion B S hS W W₀ ≫ r = b ≫ ib)
    (p : X ⟶ Bas) (hp : c.hom ≫ r.hom = p.hom) :
    ∃ (c' : X ⟶ W) (hcc : subspaceInclusion B S hS X Z ≫ c' =
        e₀ ≫ subspaceInclusion B S hS W W₀),
      c'.hom ≫ r.hom = p.hom ∧
        restrictedSharpThroughThickening B S hS Z W₀ c' e₀ hcc =
          restrictedLiftSolutionOfHom B S hS Z hZ c W₀ e₀ hce b θ :=
  exists_hom_restrictedSharpThroughThickening_eq_restrictedLiftSolutionOfHom B S hS Z hZ c W₀
    e₀ hce b θ r
    (derivationFamilyOfHom_app_base_eq_zero B S hS Z W₀ e₀ b θ r ib hsq) p hp

end DerivationExistence

end ChartLiftBypass

end AlgebraicGeometry.Space

end
