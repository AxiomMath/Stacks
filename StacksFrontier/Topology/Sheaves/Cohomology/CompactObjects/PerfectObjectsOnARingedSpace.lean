module

public import StacksFrontier.AlgebraicGeometry.RingedSpace.KFlatResolution
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.CohomologyDirectSums
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CompactObjects.PerfectObjectsAreCompact
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.VanishingTransfer
import StacksCore.Tactic.StacksAttribute

/-!
# Compactness of a perfect object on a ringed space

Let `X` be a ringed space whose underlying topological space is quasi-compact, has a basis of
quasi-compact opens, and in which the intersection of two quasi-compact opens is quasi-compact.
**Stacks 09J7** asserts, for `K` a perfect object of `D(O_X)`, that

* **(a)** `K` is compact relative to `D⁺(O_X)`: if `M = ⨁_{i ∈ I} M_i` is bounded below then
  `Hom(K, M) = ⨁_{i ∈ I} Hom(K, M_i)`; and
* **(b)** if `X` has finite cohomological dimension, that is if `Hⁱ(X, F) = 0` for `i > d` and
  some fixed `d`, then `K` is a compact object of `D(O_X)`.

Both clauses are proved here. A ringed space is a ringed site — the poset of its opens with the
open-cover topology — so the statements are the ringed-site ones, Stacks 09JC, read off along
`AlgebraicGeometry.RingedSpace.ringedSite`. What 09J7 adds to 09JC is the derivation of the
ringed-site inputs from the three topological hypotheses: for (b) the commutation of the
cohomology functors `F ↦ Hᵖ(X, F)` with direct sums, which is the source's appeal to Stacks 01FF
and is supplied by `Stacks.Cohomology.DirectSum.preservesColimitsOfShape_discrete_Hfunctor` read
through `Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso`; and for (a) the
covering data `B` and `Cov` of Stacks 0G22, supplied by `compactHypercovers` and conclusion (C3)
of Stacks 0069.

## Main results

* `Stacks.Cohomology.RingedSpaceCompact.preservesColimitsOfShape_discrete_rightDerived_evaluation`:
  on a space with a basis of quasi-compact opens whose pairwise intersections are quasi-compact,
  the module-valued cohomology functors over a quasi-compact open commute with arbitrary direct
  sums.
* `Stacks.Cohomology.RingedSpaceCompact.compactHypercovers`,
  `Stacks.Cohomology.RingedSpaceCompact.hasIntersectionsIn_of_mem_compactHypercovers` and
  `Stacks.Cohomology.RingedSpaceCompact.exists_mem_compactHypercovers_sieve₀_le`: the covering
  data of Stacks 0G22 for the opens of such a space.
* `Stacks.Cohomology.RingedSpaceCompact.hom_coproduct_bijective_of_isPerfect`:
  **Stacks 09J7 (a)**.
* `Stacks.Cohomology.RingedSpaceCompact.isCompactObject_of_isPerfect`: **Stacks 09J7 (b)**.

## Implementation notes

Hypotheses (1), (2) and (3) of the tag are hypotheses here: quasi-compactness of the space as
`CompactSpace`, and the two conditions on quasi-compact opens as Mathlib's `PrespectralSpace`
and `QuasiSeparatedSpace`. Finite cohomological dimension is the vanishing of `Hᵖ(X, F)` beyond
a fixed integer bound, in the abelian-group spelling `Hgroup`, which
`Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup` converts
to the module-valued one that Stacks 094D consumes. Sheafification of abelian groups on the site
of opens and `WEqualsLocallyBijective` for it synthesize for the opens of any topological space,
and enough injectives is supplied by `ringedSpaceModulesEnoughInjectives`.

Both clauses take the reduction the source performs first as an explicit hypothesis `hreduce`,
in the shape Stacks 09JC states it: by Stacks 08DQ (08JJ at a ringed site) the dual `K^∨` of a
perfect `K` satisfies `Hom_{D(O_X)}(K, N) = H⁰(X, K^∨ ⊗^L_{O_X} N)` naturally in `N`, and
`K^∨ ⊗^L_{O_X} -` commutes with direct sums. Perfectness of `K` is used only through `hreduce`.
The reduction is discharged in
`Stacks.Cohomology.RingedSpaceCompact.isCompactObject_of_isPerfect_of_finiteCohomDim` (b) and
`Stacks.Cohomology.RingedSpaceCompact.hom_coproduct_bijective_of_isPerfect_of_compactSpace` (a),
where the family in clause (a) is indexed by a type in the universe of the space; the conditional
`hom_coproduct_bijective_of_isPerfect` below allows an index type in an arbitrary universe.

In clause (a) the hypothesis that `⨁ M_i` is bounded below enters only through `hreduce`, as the
requirement that `T(⨁ M_i)` be bounded below: the implication from the finite tor-amplitude of a
perfect complex (Stacks 08G8) is available only locally on the site, so `hreduce` carries the
boundedness of `T(⨁ M_i)` rather than of `⨁ M_i`. The conclusion is therefore asserted for every
family admitting a coproduct, exactly as in Stacks 09JC (a).

## References

* [Stacks Project, Tag 09J7](https://stacks.math.columbia.edu/tag/09J7)
* [Stacks Project, Tag 09JC](https://stacks.math.columbia.edu/tag/09JC)
* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
* [Stacks Project, Tag 094D](https://stacks.math.columbia.edu/tag/094D)
* [Stacks Project, Tag 0G22](https://stacks.math.columbia.edu/tag/0G22)
* [Stacks Project, Tag 0069](https://stacks.math.columbia.edu/tag/0069)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u i

namespace Stacks.Cohomology.RingedSpaceCompact

/-! ### Cohomology over a quasi-compact open commutes with direct sums -/

/-- **The module-valued cohomology over a quasi-compact open commutes with arbitrary direct
sums.** The hypotheses are those of Stacks 01FF: a basis of quasi-compact opens with
quasi-compact pairwise intersections, and a quasi-compact open `U`.

`Stacks.Cohomology.DirectSum.preservesColimitsOfShape_discrete_Hfunctor` is the same statement
for the `AddCommGrpCat`-valued cohomology functor; the transfer is by reflection along
`forget₂ (ModuleCat (R(U))) AddCommGrpCat`, which reflects colimits because colimits of modules
are computed on underlying abelian groups, and
`Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso` identifies the composite
with the group-valued functor. -/
theorem preservesColimitsOfShape_discrete_rightDerived_evaluation
    {Y : Type u} [TopologicalSpace Y]
    (R : Sheaf (Opens.grothendieckTopology Y) RingCat.{u})
    (hBasis : PrespectralSpace Y) (hInter : QuasiSeparatedSpace Y)
    (U : Opens Y) (hU : IsCompact (U : Set Y)) (q : ℕ) (J : Type u) :
    PreservesColimitsOfShape (Discrete J)
      ((SheafOfModules.evaluation R (op U)).rightDerived q) := by
  have h1 : PreservesColimitsOfShape (Discrete J) (Hfunctor R U q) :=
    Stacks.Cohomology.DirectSum.preservesColimitsOfShape_discrete_Hfunctor
      R hBasis hInter U hU q J
  have h2 : PreservesColimitsOfShape (Discrete J)
      ((SheafOfModules.evaluation R (op U)).rightDerived q ⋙
        forget₂ (ModuleCat.{u} (R.obj.obj (op U))) AddCommGrpCat.{u}) :=
    @preservesColimitsOfShape_of_natIso _ _ _ _ _ _ _ _
      (Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso R U q).symm h1
  exact preservesColimitsOfShape_of_reflects_of_preserves _
    (forget₂ (ModuleCat.{u} (R.obj.obj (op U))) AddCommGrpCat.{u})

/-! ### The covering data of Stacks 0G22 for the opens of a space -/

section Coverings

variable {Y : Type u} [TopologicalSpace Y]

/-- **The infimum of a nonempty family of opens is a wide pullback over a common upper bound.**
In the poset of opens a cone over a family of opens below `U` is exactly a common lower bound of
them, so the infimum, with the inclusions, is a wide pullback cone. -/
noncomputable def iInfWidePullbackCone {U : Opens Y} {κ : Type*} [Nonempty κ]
    {V : κ → Opens Y} (g : ∀ k, V k ⟶ U) : WidePullbackCone g :=
  WidePullbackCone.mk
    (homOfLE ((iInf_le V (Classical.arbitrary κ)).trans (leOfHom (g (Classical.arbitrary κ)))))
    (fun k => homOfLE (iInf_le V k)) (fun _ => Subsingleton.elim _ _)

/-- The vertex of `iInfWidePullbackCone` is the infimum of the family. -/
theorem iInfWidePullbackCone_pt {U : Opens Y} {κ : Type*} [Nonempty κ]
    {V : κ → Opens Y} (g : ∀ k, V k ⟶ U) :
    (iInfWidePullbackCone g).pt = ⨅ k, V k := rfl

/-- `iInfWidePullbackCone` is limiting: a cone over the family is a common lower bound, hence
factors through the infimum, and uniquely so because the opens form a poset. -/
noncomputable def isLimit_iInfWidePullbackCone {U : Opens Y} {κ : Type*} [Nonempty κ]
    {V : κ → Opens Y} (g : ∀ k, V k ⟶ U) : IsLimit (iInfWidePullbackCone g) :=
  WidePullbackCone.IsLimit.mk _ (fun t => homOfLE (le_iInf fun k => leOfHom (t.π k)))
    (fun _ => Subsingleton.elim _ _) (fun _ _ => Subsingleton.elim _ _)
    (fun _ _ _ _ => Subsingleton.elim _ _)

/-- **The finite coverings of a quasi-compact open by quasi-compact opens**, in the
`PreZeroHypercover` shape: the collection `Cov` of Stacks 0G22 for the site of opens of `Y`. The
collection `B` it is paired with is `Stacks.Cohomology.Basis.compactOpens`, the quasi-compact
opens. -/
def compactHypercovers (U : Opens Y) : Set (PreZeroHypercover.{0} U) :=
  {E | Finite E.I₀ ∧ IsCompact (U : Set Y) ∧ (∀ i, IsCompact (E.X i : Set Y)) ∧
    E.sieve₀ ∈ Opens.grothendieckTopology Y U}

/-- A member of `compactHypercovers` covers its target. -/
theorem sieve₀_mem_of_mem_compactHypercovers {U : Opens Y} (E : PreZeroHypercover.{0} U)
    (hE : E ∈ compactHypercovers U) : E.sieve₀ ∈ Opens.grothendieckTopology Y U := hE.2.2.2

/-- **A finite covering by quasi-compact opens has quasi-compact iterated intersections**, by
hypothesis (3) of the tag. The iterated fibre product in the poset of opens is the infimum
(`isLimit_iInfWidePullbackCone`), and a nonempty finite infimum of quasi-compact opens is
quasi-compact (`Stacks.Cohomology.Vanishing.isCompact_coe_iInf`). -/
theorem hasIntersectionsIn_of_mem_compactHypercovers (hInter : QuasiSeparatedSpace Y)
    {U : Opens Y} (E : PreZeroHypercover.{0} U) (hE : E ∈ compactHypercovers U) :
    Stacks.Cohomology.HasIntersectionsIn (Stacks.Cohomology.Basis.compactOpens Y) E :=
  ⟨hE.1, hE.2.1, hE.2.2.1, fun _n a =>
    ⟨iInfWidePullbackCone (fun i => E.f (a i)), ⟨isLimit_iInfWidePullbackCone _⟩,
      Stacks.Cohomology.Vanishing.isCompact_coe_iInf hInter (fun i => E.X (a i))
        (fun i => hE.2.2.1 (a i))⟩⟩

/-- **A sieve on an open contains every inclusion of a smaller open into it** as soon as it
contains one inclusion of a larger one: the opens form a poset, so there is at most one morphism
between two of them, and a sieve is closed under precomposition. -/
theorem mem_sieve_of_le {U V V' : Opens Y} (S : Sieve U) {f : V' ⟶ U} (hf : S f)
    (h : V ≤ V') (g : V ⟶ U) : S g :=
  Subsingleton.elim (homOfLE h ≫ f) g ▸ S.downward_closed hf (homOfLE h)

/-- **Every covering sieve of a quasi-compact open is refined by a finite covering by
quasi-compact opens**: the cofinality hypothesis of Stacks 0G22, which is conclusion (C3) of
Stacks 0069 (`hasCofinalCompactRefinements_of_isCompact_isOpen`) applied to the family of the
members of the sieve. Each member of the refinement is contained in a member of the sieve, and a
sieve is closed under precomposition, so the refinement's sieve is contained in it. -/
@[sga "4 II 3.0.4" "2)"]
theorem exists_mem_compactHypercovers_sieve₀_le (hBasis : PrespectralSpace Y)
    (hInter : QuasiSeparatedSpace Y) (U : Opens Y)
    (hU : U ∈ Stacks.Cohomology.Basis.compactOpens Y)
    (S : Sieve U) (hS : S ∈ Opens.grothendieckTopology Y U) :
    ∃ E : PreZeroHypercover.{0} U, E ∈ compactHypercovers U ∧ E.sieve₀ ≤ S := by
  classical
  have hUc : IsCompact (U : Set Y) := hU
  have hcov : (U : Set Y) ⊆ ⋃ k : {V : Opens Y // ∃ f : V ⟶ U, S f}, (k.1 : Set Y) := by
    intro x hx
    obtain ⟨V, f, hf, hxV⟩ := (Opens.mem_grothendieckTopology Y).1 hS x hx
    exact Set.mem_iUnion.mpr ⟨⟨V, f, hf⟩, hxV⟩
  obtain ⟨ι, Jf, W, hWopen, hWcompact, hWcover, -, hWref⟩ :=
    hasCofinalCompactRefinements_of_isCompact_isOpen hBasis hInter U.isOpen hUc
      (fun k : {V : Opens Y // ∃ f : V ⟶ U, S f} => (k.1 : Set Y))
      (fun k => k.1.isOpen) hcov
  have hmemU : ∀ x, x ∈ (U : Set Y) ↔ ∃ j, ∃ _ : j ∈ Jf, x ∈ W j := fun x => by
    rw [hWcover, Set.mem_iUnion₂]
  have hmem : ∀ (j : ι) (hj : j ∈ Jf), (⟨W j, hWopen j hj⟩ : Opens Y) ≤ U :=
    fun j hj x hx => (hmemU x).2 ⟨j, hj, hx⟩
  let Xf : {j : ι // j ∈ Jf} → Opens Y := fun j => ⟨W j.1, hWopen j.1 j.2⟩
  let ff : ∀ j, Xf j ⟶ U := fun j => homOfLE (hmem j.1 j.2)
  refine ⟨{ I₀ := {j : ι // j ∈ Jf}, X := Xf, f := ff }, ⟨inferInstance, hUc,
    fun j => hWcompact j.1 j.2, ?_⟩, ?_⟩
  · refine (Opens.mem_grothendieckTopology Y).2 fun x hx => ?_
    obtain ⟨j, hj, hxj⟩ := (hmemU x).1 hx
    exact ⟨Xf ⟨j, hj⟩, ff ⟨j, hj⟩, Sieve.ofArrows_mk Xf ff ⟨j, hj⟩, hxj⟩
  · intro V g hg
    rw [Sieve.mem_ofArrows_iff] at hg
    obtain ⟨j, p, rfl⟩ := hg
    obtain ⟨k, hk⟩ := hWref j.1 j.2
    obtain ⟨f₀, hf₀⟩ := k.2
    exact S.downward_closed (mem_sieve_of_le S hf₀ hk _) p

end Coverings

/-! ### The tag -/

/-- The top open of a compact space is compact. -/
private theorem isCompact_coe_top (Y : Type u) [TopologicalSpace Y] [CompactSpace Y] :
    IsCompact ((⊤ : Opens Y) : Set Y) := by
  simpa using CompactSpace.isCompact_univ

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u})

/-- Sheaves of modules on a ringed space have enough injectives, through the ringed site of its
opens. -/
local instance ringedSpaceModulesEnoughInjectives :
    EnoughInjectives
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O)) :=
  Stacks.Cohomology.enoughInjectives_of_ringedSite.{u, u, u, u} (RingedSpace.ringedSite X)

/-- **Compactness of a perfect object from a reduction functor.** Let `X` be a ringed space
whose underlying topological space is quasi-compact, has a basis of quasi-compact opens, and has
quasi-compact intersections of quasi-compact opens, and assume `X` has finite cohomological
dimension. Let `K` be a perfect object of `D(O_X)`, and let `T` be an endofunctor of `D(O_X)`
commuting with direct sums such that morphisms out of `K` are, naturally in the target, the
morphisms out of `j_{X!}O_X` into `T` of the target. Then `K` is a compact object of `D(O_X)`.

The topological conditions make the cohomology functors `F ↦ Hᵖ(X, F)` commute with arbitrary
direct sums (Stacks 01FF), which with the dimension bound makes `j_{X!}O_X` compact
(Stacks 094D); this is Stacks 09JC (b) at the ringed site of the opens of `X`. -/
theorem isCompactObject_of_isPerfect [CompactSpace X.carrier]
    (hBasis : PrespectralSpace X.carrier)
    (hInter : QuasiSeparatedSpace X.carrier)
    (K : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O)))
    (hK : (RingedSpace.ringedSite X).IsPerfect K)
    (hcd : ∃ d : ℤ, ∀ (p : ℕ)
      (F : SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O)),
      d < (p : ℤ) →
        IsZero (Hgroup (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O) ⊤ p F))
    (hreduce : (RingedSpace.ringedSite X).IsPerfect K →
      ∃ T : DerivedCategory (SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O)) ⥤
          DerivedCategory (SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O)),
        ∃ _ : ∀ I : Type u, PreservesColimitsOfShape (Discrete I) T,
          ∃ e : ∀ N : DerivedCategory (SheafOfModules.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O)), (K ⟶ N) ≃+
              ((DerivedCategory.singleFunctor (SheafOfModules.{u}
                (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O)) 0).obj
                ((SheafOfModules.pullback.{u}
                  (F := Over.forget (⊤ : (RingedSpace.ringedSite X).C))
                  (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O).over
                    (⊤ : (RingedSpace.ringedSite X).C)))).obj
                  (SheafOfModules.unit
                    ((Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O).over
                      (⊤ : (RingedSpace.ringedSite X).C)))) ⟶ T.obj N),
            ∀ {N N' : DerivedCategory (SheafOfModules.{u}
                (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O))}
              (f : K ⟶ N) (g : N ⟶ N'), e N' (f ≫ g) = e N f ≫ T.map g) :
    IsCompactObject.{u} K := by
  have hvanish : ∃ d : ℤ, ∀ (p : ℕ)
      (F : SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O)), d < (p : ℤ) →
      IsZero (((SheafOfModules.evaluation.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O)
        (op (⊤ : (RingedSpace.ringedSite X).C))).rightDerived p).obj F) := by
    obtain ⟨d, hd⟩ := hcd
    exact ⟨d, fun p F hp =>
      (Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup
        (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O) ⊤ p F).2 (hd p F hp)⟩
  have hsums : ∀ (p : ℕ) (I : Type u), PreservesColimitsOfShape (Discrete I)
      ((SheafOfModules.evaluation.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O)
        (op (⊤ : (RingedSpace.ringedSite X).C))).rightDerived p) := fun p I =>
    preservesColimitsOfShape_discrete_rightDerived_evaluation
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O) hBasis hInter ⊤
      (isCompact_coe_top _) p I
  exact Stacks.Cohomology.isCompactObject_of_isPerfect (RingedSpace.ringedSite X)
    (⊤ : (RingedSpace.ringedSite X).C) K hK hvanish hsums hreduce

/-- **Compactness relative to bounded below objects, from a reduction functor.** Let `X` be a
ringed space whose underlying topological space is quasi-compact, has a basis of quasi-compact
opens, and has quasi-compact intersections of quasi-compact opens. Let `K` be a perfect object of
`D(O_X)`, let `M : I → D(O_X)` be a family with a coproduct, and let `T` be an endofunctor of
`D(O_X)` preserving the coproduct of `M`, with `T(⨁ M_i)` bounded below, such that morphisms out
of `K` are, naturally in the target, the morphisms out of `j_{X!}O_X` into `T` of the target.
Then `Hom(K, ⨁ M_i) = ⨁ Hom(K, M_i)`.

The topological conditions supply the covering data of Stacks 0G22: the quasi-compact opens, the
finite coverings of a quasi-compact open by quasi-compact opens (`compactHypercovers`), whose
iterated intersections are quasi-compact (`hasIntersectionsIn_of_mem_compactHypercovers`) and
which are cofinal among the covering sieves (`exists_mem_compactHypercovers_sieve₀_le`). This is
Stacks 09JC (a) at the ringed site of the opens of `X`. -/
theorem hom_coproduct_bijective_of_isPerfect [CompactSpace X.carrier]
    (hBasis : PrespectralSpace X.carrier)
    (hInter : QuasiSeparatedSpace X.carrier)
    (K : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O)))
    (hK : (RingedSpace.ringedSite X).IsPerfect K)
    {I : Type i} [DecidableEq I]
    (M : I → DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O)))
    [HasCoproduct M]
    (hreduce : (RingedSpace.ringedSite X).IsPerfect K →
      ∃ T : DerivedCategory (SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O)) ⥤
          DerivedCategory (SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O)),
        ∃ _ : PreservesColimit (Discrete.functor M) T,
          (DerivedCategory.TStructure.t
              (C := SheafOfModules.{u}
                (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O))).plus
            (T.obj (∐ M)) ∧
          ∃ e : ∀ N : DerivedCategory (SheafOfModules.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O)), (K ⟶ N) ≃+
              ((DerivedCategory.singleFunctor (SheafOfModules.{u}
                (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O)) 0).obj
                (Stacks.Sites.OverModules.extensionByZeroUnit.{u, u, u, u}
                  (RingedSpace.ringedSite X).J
                  (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O)
                  (⊤ : (RingedSpace.ringedSite X).C)) ⟶ T.obj N),
            ∀ {N N' : DerivedCategory (SheafOfModules.{u}
                (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O))}
              (f : K ⟶ N) (g : N ⟶ N'), e N' (f ≫ g) = e N f ≫ T.map g) :
    Function.Bijective
      (DirectSum.toAddMonoid fun j => Preadditive.rightComp K (Limits.Sigma.ι M j)) := by
  exact Stacks.Cohomology.hom_coproduct_bijective_of_isPerfect (RingedSpace.ringedSite X)
    (Stacks.Cohomology.Basis.compactOpens (X.carrier : Type u))
    (fun U => compactHypercovers U)
    (fun _ E hE => sieve₀_mem_of_mem_compactHypercovers E hE)
    (fun _ E hE => hasIntersectionsIn_of_mem_compactHypercovers hInter E hE)
    (fun U hU S hS => exists_mem_compactHypercovers_sieve₀_le hBasis hInter U hU S hS)
    (⊤ : (RingedSpace.ringedSite X).C) (isCompact_coe_top _) K hK M hreduce

end Stacks.Cohomology.RingedSpaceCompact

end
