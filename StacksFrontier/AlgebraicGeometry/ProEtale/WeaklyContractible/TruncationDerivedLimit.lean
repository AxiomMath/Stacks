module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SeparatorUnivLE
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftFiniteColimits
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.Situation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.AcyclicObject
public import StacksFrontier.CategoryTheory.Sites.Cohomology.WeaklyContractible.CohomologyOverAWeaklyContractibleObject
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorTriangleOfTower
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen

/-!
# A complex of modules is the derived limit of its truncations on a weakly contractible site

Let `(C, O)` be a ringed site carrying a covering collection of weakly contractible objects and
let `K` be an object of the unbounded derived category of `O`-modules. Then `K` is a derived
limit of the tower `n ↦ τ_{≥ -n} K` of its canonical truncations from below:
`K = R lim τ_{≥ -n} K`. This is Stacks 0947(2).

The source deduces it from the convergence criterion of Stacks 0D6P with degree bound `d = 0`,
whose hypothesis is that every cohomology sheaf of `K` be acyclic on the members of a covering
collection. That hypothesis holds here for every sheaf of modules at once: sections over a weakly
contractible object are exact on abelian sheaves (Stacks 0946(1)), forgetting a sheaf of modules
to its underlying abelian sheaf is exact, and an exact functor has no higher right derived
functors.

## Main results

Both in the namespace `Stacks.WeaklyContractible`:

* `isZero_rightDerived_evaluation_of_isWeaklyContractible`: a sheaf of modules has no higher
  cohomology over a weakly contractible object.
* `exists_isDerivedLimit_truncGETower_of_weaklyContractibleObjectsSituation`: **Stacks 0947(2)**,
  `K` is a derived limit of its truncation tower.

## Implementation notes

The vanishing is stated as vanishing of the right derived functors of
`SheafOfModules.evaluation`, which is the shape the convergence criterion
`Stacks.Cohomology.AcyclicCover.isIso_to_isDerivedLimit_truncGETower_of_acyclic` consumes. It is
obtained from the abelian-group-valued statement by
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso`, which commutes an exact functor past a
right derived functor; the two composites it compares are definitionally equal, so the comparison
is the identity isomorphism of functors and nothing is chosen.

That an exact functor has vanishing higher right derived functors is
`isZero_rightDerived_succ_of_preservesHomology`, read off the chosen injective resolution: its
cocomplex is exact in positive degrees, and an exact functor commutes with the homology of a
cochain complex.

The product of the truncation tower is part of the conclusion rather than a hypothesis; it exists
because every stage is bounded below
(`Stacks.Cohomology.HypercohomologyEdge.hasProduct_truncGETower`, Stacks 0BK7). Exactness of
countable products, which an arbitrary product in the derived category would need, is available
here — it is Stacks 0947(4) — but the bounded-below route does not use it.

The derived category is `HasDerivedCategory.standard`, as a local instance, because that is the
model in which the convergence criterion is stated.

Enough injectives for `Mod(O)` is proved, not assumed: it is what makes the right derived
functors of evaluation exist, and `SheafOfModules.enoughInjectives_of_univLE` supplies it from
Grothendieck abelianness. That theorem needs the module universe to dominate those of the site,
of its homs and of the sheaf of rings, which is why the tagged statement is at module universe
`max u v w t` — the source's setting, where every object lives in one universe. Below that
threshold there is no separator to build an injective embedding from, so the general form
`isZero_rightDerived_evaluation_of_isWeaklyContractible` keeps the instance argument and the
tagged statement does not.

## References

* [Stacks Project, Tag 0947](https://stacks.math.columbia.edu/tag/0947), part (2)
* [Stacks Project, Tag 0D6P](https://stacks.math.columbia.edu/tag/0D6P)
* [Stacks Project, Tag 0946](https://stacks.math.columbia.edu/tag/0946)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe w v u t

namespace Stacks.WeaklyContractible

/-- An exact additive functor has no higher right derived functors: on the chosen injective
resolution of an object, the cocomplex is exact in every positive degree, and an exact functor
commutes with the homology of a cochain complex. -/
private theorem isZero_rightDerived_succ_of_preservesHomology
    {A B : Type*} [Category* A] [Abelian A] [HasInjectiveResolutions A]
    [Category* B] [Abelian B] (T : A ⥤ B) [T.Additive] [T.PreservesHomology]
    (M : A) (n : ℕ) :
    IsZero ((T.rightDerived (n + 1)).obj M) := by
  refine IsZero.of_iso ?_ ((injectiveResolution M).isoRightDerivedObj T (n + 1))
  refine IsZero.of_iso ?_
    ((Stacks.Cohomology.ModuleComparison.homologyMapFunctorIso T (n + 1)).app
      (injectiveResolution M).cocomplex)
  exact T.map_isZero (((injectiveResolution M).cocomplex_exactAt_succ n).isZero_homology)

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- **Acyclicity of modules over a weakly contractible object.** A sheaf of `O`-modules has no
higher cohomology over a weakly contractible object of the site: the right derived functors of
evaluation there vanish in positive degrees.

This is the module form of Stacks 0946(2); weak contractibility is tested on sheaves of sets in
the universe of the modules. -/
theorem isZero_rightDerived_evaluation_of_isWeaklyContractible
    (O : Sheaf J RingCat.{w}) [HasSheafify J AddCommGrpCat.{t}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
    [EnoughInjectives (SheafOfModules.{t} O)] (V : C)
    (hV : ∀ (F G : Sheaf J (Type t)) (φ : F ⟶ G), Sheaf.IsLocallySurjective φ →
      Function.Surjective (φ.hom.app (op V)))
    (F : SheafOfModules.{t} O) (p : ℕ) (hp : 0 < p) :
    IsZero (((SheafOfModules.evaluation O (op V)).rightDerived p).obj F) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  have hex := Stacks.WeaklyContractible.exact_sheafSections_of_isWeaklyContractible.{t} J V hV
  let h1 : PreservesFiniteLimits ((sheafSections J AddCommGrpCat.{t}).obj (op V)) := hex.1
  let h2 : PreservesFiniteColimits ((sheafSections J AddCommGrpCat.{t}).obj (op V)) := hex.2
  let hcol : PreservesFiniteColimits (SheafOfModules.toSheaf.{t} O) :=
    Stacks.SheafOfModules.toSheaf_preservesFiniteColimits O
  let T : SheafOfModules.{t} O ⥤ AddCommGrpCat.{t} :=
    SheafOfModules.toSheaf.{t} O ⋙ (sheafSections J AddCommGrpCat.{t}).obj (op V)
  let hlimT : PreservesFiniteLimits T := Limits.comp_preservesFiniteLimits _ _
  let hcolT : PreservesFiniteColimits T := Limits.comp_preservesFiniteColimits _ _
  let haddT : T.Additive := Functor.additive_of_preserves_binary_products _
  let hhomT : T.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels _
  let haddE : (SheafOfModules.evaluation O (op V)).Additive := by
    dsimp [SheafOfModules.evaluation]
    infer_instance
  have hiso : SheafOfModules.evaluation O (op V) ⋙
      forget₂ (ModuleCat.{t} (O.obj.obj (op V))) AddCommGrpCat.{t} ≅ T := Iso.refl _
  exact ModuleCat.isZero_iff_subsingleton.2 (AddCommGrpCat.subsingleton_of_isZero
    (IsZero.of_iso (isZero_rightDerived_succ_of_preservesHomology T F n)
      ((Stacks.Cohomology.ModuleComparison.rightDerivedCompIso
        (SheafOfModules.evaluation O (op V))
        (forget₂ (ModuleCat.{t} (O.obj.obj (op V))) AddCommGrpCat.{t}) T hiso (n + 1)).app F)))

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 0947(2).** On a ringed site with a covering collection of weakly contractible
objects, every object `E` of the unbounded derived category of sheaves of modules *is* a derived
limit of the tower `n ↦ τ_{≥ -n} E` of its canonical truncations from below:
`E = R lim τ_{≥ -n} E`. The product of the tower exists because each of its stages is bounded
below, and is part of the conclusion. -/
@[stacks 0947 "(2)"]
theorem exists_isDerivedLimit_truncGETower_of_weaklyContractibleObjectsSituation
    [HasSheafify J AddCommGrpCat.{max u v w t}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w t}]
    (S : WeaklyContractibleObjectsSituation.{w, v, u, max u v w t} C J)
    (E : DerivedCategory (SheafOfModules.{max u v w t} S.O)) :
    ∃ _ : HasProduct fun n : ℕ ↦
        (Stacks.DerivedLimit.truncGETower (SheafOfModules.{max u v w t} S.O) E).obj ⟨n⟩,
      IsDerivedLimit (Stacks.DerivedLimit.truncGETower (SheafOfModules.{max u v w t} S.O) E)
        E := by
  have : EnoughInjectives (SheafOfModules.{max u v w t} S.O) :=
    SheafOfModules.enoughInjectives_of_univLE.{max u v w t, v, u, w} S.O
  have hvan : ∀ V : C, S.B V → ∀ p : ℕ, 0 < p → ∀ q : ℤ,
      IsZero (((SheafOfModules.evaluation S.O (op V)).rightDerived p).obj
        ((DerivedCategory.homologyFunctor (SheafOfModules.{max u v w t} S.O) q).obj E)) :=
    fun V hV p hp q ↦ isZero_rightDerived_evaluation_of_isWeaklyContractible S.O V
      (S.isWeaklyContractible hV) _ p hp
  have hprod := Stacks.Cohomology.HypercohomologyEdge.hasProduct_truncGETower S.O E
  obtain ⟨δ, hδ⟩ := Stacks.InverseSystem.exists_distTriang_milnor_of_isIso
    (Stacks.DerivedLimit.truncGETower (SheafOfModules.{max u v w t} S.O) E)
    (fun n : ℕ ↦ (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E)
    (fun n ↦ by
      rw [Stacks.DerivedLimit.truncGETower_map_homOfLE_succ]
      exact DerivedCategory.TStructure.t.π_natTransTruncGEOfLE_app
        (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega) E)
    fun L c pr d hL hc ↦
      Stacks.Cohomology.AcyclicCover.isIso_to_isDerivedLimit_truncGETower_of_acyclic
        S.O E S.B S.hasEnoughObjects hvan L c pr d hL hc
  exact ⟨hprod, _, δ, hδ⟩

end Stacks.WeaklyContractible

end
