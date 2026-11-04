module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.FilteredLimitChow
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.Injective
public import StacksFrontier.AlgebraicGeometry.Chow.PerfectClosureCycles
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Chow groups over an algebraic field extension

Let `K/k` be an algebraic extension of fields and let `X` be a quasi-compact scheme of finite
type over `k`. The finite subextensions `K/k'/k` form a directed set, and the spectra `Spec k'`
form a cofiltered inverse system of base schemes with limit `Spec K`, because `K` is the filtered
colimit of its finite subextensions and `Spec` carries a colimit of rings to a limit of schemes.
That system is a `Stacks.Chow.FilteredBaseChangeSystem`, so the comparison homomorphisms of
Stacks 0FVQ are available for it.

The Chow groups of the stages form a filtered system of abelian groups over the finite
subextensions, and the comparison homomorphisms to `CH_k(X_K)` assemble into a homomorphism out
of its colimit which is an isomorphism, which is Stacks 0FH6. On cycle groups injectivity holds
outright, because the spectrum of a field is a single point and so every morphism between two
of them is surjective.

## Main definitions

* `Stacks.Chow.FiniteSubextension` — the finite subextensions of `K/k`, ordered by inclusion.
* `Stacks.Chow.finiteSubextensionRingDiagram`, `Stacks.Chow.finiteSubextensionRingCocone` — the
  directed system of the finite subextensions as commutative rings, and its cocone with vertex
  `K`.
* `Stacks.Chow.finiteSubextensionDiagram`, `Stacks.Chow.finiteSubextensionCone` — the cofiltered
  inverse system `k' ↦ Spec k'` of base schemes, and its cone with vertex `Spec K`.
* `Stacks.Chow.algebraicExtensionSystem` — the situation of Stacks 0FVQ attached to `K/k` and
  `X`.
* `Stacks.Chow.FilteredBaseChangeSystem.chowDiagram`,
  `Stacks.Chow.FilteredBaseChangeSystem.chowCocone` — the system `i ↦ CH_k(X_i)` of abelian
  groups and its cocone with vertex `CH_k(X')`.
* `Stacks.Chow.FilteredBaseChangeSystem.chowColimitComparison` — the induced homomorphism
  `colim_i CH_k(X_i) ⟶ CH_k(X')`.
* `Stacks.Chow.chowColimitAddEquiv_algebraicExtensionSystem` — the isomorphism
  `colim_{k'} CH_i(X_{k'}) ≃+ CH_i(X_K)` of Stacks 0FH6.

## Main results

* `Stacks.Chow.isColimit_finiteSubextensionRingCocone` — an algebraic extension is the filtered
  colimit of its finite subextensions.
* `Stacks.Chow.isLimit_finiteSubextensionCone` — `Spec K` is the limit of the spectra of the
  finite subextensions.
* `Stacks.Chow.flatPullbackWeight_id` — the flat pullback multiplicity along an identity is one.
* `Stacks.Chow.FilteredBaseChangeSystem.transitionCyclePullback_id` — the comparison map on
  cycle groups along an identity transition is the identity.
* `Stacks.Chow.FilteredBaseChangeSystem.surjective_chowColimitComparison`,
  `Stacks.Chow.FilteredBaseChangeSystem.injective_chowColimitComparison` — the homomorphism out
  of the colimit is surjective, and injective.
* `Stacks.Chow.injective_baseChangeCyclePullbackOfIsPullback` — the base change on cycle groups
  along a cartesian square is injective when the base-change morphism is surjective.
* `Stacks.Chow.injective_stageCyclePullback_algebraicExtensionSystem`,
  `Stacks.Chow.injective_transitionCyclePullback_algebraicExtensionSystem` — the comparison
  homomorphisms on cycle groups of the system of a field extension are injective.
* `Stacks.Chow.bijective_chowColimitComparison_algebraicExtensionSystem` — **Stacks 0FH6**: the
  comparison homomorphism `colim_{k'} CH_i(X_{k'}) ⟶ CH_i(X_K)` of an algebraic extension is
  bijective, whence the isomorphism
  `Stacks.Chow.chowColimitAddEquiv_algebraicExtensionSystem`.

## Implementation notes

The identity case of the functoriality of the comparison homomorphisms is proved here rather
than alongside their construction, because it is only needed to form the colimit. On cycle
groups it is read coefficientwise: a coefficient of a comparison map is a coefficient of the
cycle at the image point times a multiplicity. For the identity the multiplicity is one, which
is `Stacks.Chow.flatPullbackWeight_id`: the inverse image of the reduced closure of a point
along the identity is that reduced closure, which is integral and so has multiplicity one at
its generic point.

The index category of the scheme system is the opposite of the finite subextensions: fields form
a direct system and their spectra an inverse one. Its morphisms are inequalities, so it is
cofiltered as soon as the finite subextensions are directed, which holds because a compositum of
two finite subextensions is finite.

## References

* [Stacks Project, Tag 0FH6](https://stacks.math.columbia.edu/tag/0FH6)
* [Stacks Project, Tag 0FVQ](https://stacks.math.columbia.edu/tag/0FVQ)
* [Stacks Project, Tag 0FVG](https://stacks.math.columbia.edu/tag/0FVG)
* [Stacks Project, Tag 0FVP](https://stacks.math.columbia.edu/tag/0FVP)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
* [Stacks Project, Section 0H4E](https://stacks.math.columbia.edu/tag/0H4E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe w v u

namespace Stacks.Chow

/-! ### The flat pullback multiplicity along an identity -/

/-- The multiplicity with which a point of relative dimension `k` enters the flat pullback of a
`k`-cycle along the identity is one: the inverse image of the reduced closure of the point is
that reduced closure, and an integral closed subscheme has multiplicity one at its generic
point. -/
theorem flatPullbackWeight_id (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) (x : X)
    (hx : relativeDimension C.dimensionFunction f x = k) :
    flatPullbackWeight C f (𝟙 X) k x = 1 := by
  have hbase : (𝟙 X : X ⟶ X).base x = x := by simp
  have hI : (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({(𝟙 X : X ⟶ X).base x} : Set X))).comap (𝟙 X) =
      integralComponentAt x := by
    rw [hbase]
    exact Scheme.IdealSheafData.comap_id _
  have hcoeff : flatPullbackWeight C f (𝟙 X) k x =
      closedSubschemeCycleCoeff C f (integralComponentAt x).subschemeι k x :=
    closedSubschemeCycleCoeff_congr_idealSheaf C f hI k x
  rw [hcoeff]
  exact cycleAssociatedToClosedSubscheme_integralComponentAt_self C f x
    (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C f x hx)

/-! ### Injectivity of the base change along a cartesian square -/

/-- A morphism of schemes whose source is nonempty and whose target has at most one point is
surjective. -/
theorem surjective_of_subsingleton {X Y : Scheme.{u}} (f : X ⟶ Y) [Nonempty X]
    [Subsingleton Y] : Surjective f :=
  ⟨fun _ ↦ ⟨Classical.arbitrary X, Subsingleton.elim _ _⟩⟩

/-- **Injectivity of the base-change homomorphism on cycle groups along a cartesian square.** For
a flat base change of Chow situations with vanishing dimension shift whose base-change morphism
is surjective on points, the homomorphism `Z_k(X) ⟶ Z_k(Y)` attached to a cartesian square
realizing `Y` as the base change of `X` is injective.

The homomorphism along the square is the one along the chosen fibre product read through the
comparison isomorphism, so it is injective because that one is, by
`Stacks.Chow.injective_baseChangeCyclePullback_of_surjective`. -/
theorem injective_baseChangeCyclePullbackOfIsPullback (B : FlatBaseChangeSituation.{u})
    (hc : B.c = 0) [Surjective B.g] {X Y : Scheme.{u}} (f : X ⟶ B.base.S)
    [LocallyOfFiniteType f] {p : Y ⟶ X} {q : Y ⟶ B.baseChange.S} [LocallyOfFiniteType q]
    (sq : IsPullback p q f B.g) (k : ℤ) :
    Function.Injective (baseChangeCyclePullbackOfIsPullback B hc f sq k) := by
  intro z z' h
  refine injective_baseChangeCyclePullback_of_surjective B f k ?_
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro w
  have hw : sq.isoPullback.hom.base (sq.isoPullback.inv.base w) = w := by simp
  have hy := congrArg (fun c : CycleGroup B.baseChange q k ↦ c.1 (sq.isoPullback.inv.base w)) h
  rw [baseChangeCyclePullbackOfIsPullback_apply B hc f sq k z,
    baseChangeCyclePullbackOfIsPullback_apply B hc f sq k z', hw] at hy
  exact hy

/-! ### Functoriality of the comparison homomorphisms -/

namespace FilteredBaseChangeSystem

variable {I : Type v} [Category.{w} I] [IsCofiltered I] [EssentiallySmall.{u} I]
  (s : FilteredBaseChangeSystem.{w, v, u} I)

/-- The comparison homomorphism on cycle groups along an identity transition is the identity. -/
theorem transitionCyclePullback_id (i : I) (k : ℤ)
    (z : CycleGroup (s.stageSituation i) (pullback.snd s.X.hom (s.stageToBase i)) k) :
    s.transitionCyclePullback (𝟙 i) k z = z := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro y
  have hpt : (s.stageTransition (𝟙 i)).base y = y := by
    have h := congrArg
      (fun m : (pullback s.X.hom (s.stageToBase i) : Scheme.{u}) ⟶
        (pullback s.X.hom (s.stageToBase i) : Scheme.{u}) ↦ m.base y) (s.stageTransition_id i)
    simpa using h
  have happly := baseChangeCyclePullbackOfIsPullback_apply' (s.transitionBaseChange (𝟙 i)) rfl
    (pullback.snd s.X.hom (s.stageToBase i)) (s.isPullback_stageTransition (𝟙 i)) k z y
  show (baseChangeCyclePullbackOfIsPullback (s.transitionBaseChange (𝟙 i)) rfl
    (pullback.snd s.X.hom (s.stageToBase i)) (s.isPullback_stageTransition (𝟙 i)) k z).1 y =
      z.1 y
  rw [happly, hpt]
  by_cases hz : z.1 y = 0
  · rw [hz, zero_mul]
  · have hdim : relativeDimension (s.transitionBaseChange (𝟙 i)).baseChange.dimensionFunction
        (pullback.snd s.X.hom (s.stageToBase i)) y = k :=
      (mem_cyclesOfDimension_iff_forall_point (s.stageSituation i)
        (pullback.snd s.X.hom (s.stageToBase i)) k z.1).1 z.2 y hz
    have hwt : flatPullbackWeight (s.transitionBaseChange (𝟙 i)).baseChange
        (pullback.snd s.X.hom (s.stageToBase i)) (s.stageTransition (𝟙 i)) k y = 1 := by
      rw [s.stageTransition_id i]
      exact flatPullbackWeight_id (s.transitionBaseChange (𝟙 i)).baseChange
        (pullback.snd s.X.hom (s.stageToBase i)) k y hdim
    rw [hwt, mul_one]

/-- The comparison homomorphism on Chow groups along an identity transition is the identity. -/
theorem transitionChowPullback_id (i : I) (k : ℤ)
    (α : chowGroup (s.stageSituation i) (pullback.snd s.X.hom (s.stageToBase i)) k) :
    s.transitionChowPullback (𝟙 i) k α = α := by
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective _ α
  rw [s.transitionChowPullback_mk (𝟙 i) k z, s.transitionCyclePullback_id i k z]

/-- The comparison homomorphisms on Chow groups along the transitions compose. -/
theorem transitionChowPullback_comp {i j l : I} (f : i ⟶ j) (g : j ⟶ l) (k : ℤ)
    (α : chowGroup (s.stageSituation l) (pullback.snd s.X.hom (s.stageToBase l)) k) :
    s.transitionChowPullback f k (s.transitionChowPullback g k α) =
      s.transitionChowPullback (f ≫ g) k α := by
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective _ α
  rw [s.transitionChowPullback_mk g k z, s.transitionChowPullback_mk f k _,
    s.transitionChowPullback_mk (f ≫ g) k z, s.transitionCyclePullback_comp f g k z]

/-- The comparison homomorphism on Chow groups to the limit absorbs the comparison homomorphism
along a transition. -/
theorem stageChowPullback_transitionChowPullback {i j : I} (f : i ⟶ j) (k : ℤ)
    (α : chowGroup (s.stageSituation j) (pullback.snd s.X.hom (s.stageToBase j)) k) :
    s.stageChowPullback i k (s.transitionChowPullback f k α) = s.stageChowPullback j k α := by
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective _ α
  rw [s.transitionChowPullback_mk f k z, s.stageChowPullback_mk i k _,
    s.stageChowPullback_mk j k z, s.stageCyclePullback_transitionCyclePullback f k z]

/-! ### Injectivity of the comparison homomorphisms on cycle groups -/

/-- The comparison homomorphism `Z_k(X_i) ⟶ Z_k(X')` is injective as soon as the projection from
the limit base to the stage is surjective on points. -/
theorem injective_stageCyclePullback (i : I) [Surjective (s.limitProjection i)] (k : ℤ) :
    Function.Injective (s.stageCyclePullback i k) :=
  injective_baseChangeCyclePullbackOfIsPullback (s.stageToLimitBaseChange i) rfl
    (pullback.snd s.X.hom (s.stageToBase i)) (s.isPullback_stageProjection i) k

/-- The comparison homomorphism `Z_k(X_j) ⟶ Z_k(X_i)` is injective as soon as the transition
morphism of the inverse system of bases is surjective on points. -/
theorem injective_transitionCyclePullback {i j : I} (f : i ⟶ j)
    [Surjective (s.diagram.map f)] (k : ℤ) :
    Function.Injective (s.transitionCyclePullback f k) :=
  injective_baseChangeCyclePullbackOfIsPullback (s.transitionBaseChange f) rfl
    (pullback.snd s.X.hom (s.stageToBase j)) (s.isPullback_stageTransition f) k

/-! ### The filtered system of Chow groups and its colimit -/

/-- The filtered system `i ↦ CH_k(X_i)` of the Chow groups of the stages, indexed by the
opposite of the index category of the inverse system of bases. -/
def chowDiagram (k : ℤ) : Iᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj a := AddCommGrpCat.of
    (chowGroup (s.stageSituation a.unop) (pullback.snd s.X.hom (s.stageToBase a.unop)) k)
  map {_ _} h := AddCommGrpCat.ofHom (s.transitionChowPullback h.unop k)
  map_id a := by
    ext α
    exact s.transitionChowPullback_id a.unop k α
  map_comp {_ _ _} h h' := by
    ext α
    exact (s.transitionChowPullback_comp h'.unop h.unop k α).symm

/-- The value of the system of Chow groups at a stage `i` is `CH_k(X_i)`. -/
@[simp]
theorem chowDiagram_obj (k : ℤ) (a : Iᵒᵖ) :
    (s.chowDiagram k).obj a = AddCommGrpCat.of
      (chowGroup (s.stageSituation a.unop) (pullback.snd s.X.hom (s.stageToBase a.unop)) k) :=
  rfl

/-- The cocone on the system of Chow groups of the stages with vertex `CH_k(X')`, whose legs are
the comparison homomorphisms of Stacks 0FVQ. -/
def chowCocone (k : ℤ) : Cocone (s.chowDiagram k) where
  pt := AddCommGrpCat.of (chowGroup s.limitBaseChange.baseChange
    (pullback.snd s.X.hom s.limitBaseChange.g) k)
  ι :=
    { app a := AddCommGrpCat.ofHom (s.stageChowPullback a.unop k)
      naturality := by
        intro a b h
        ext α
        exact s.stageChowPullback_transitionChowPullback h.unop k α }

/-- The vertex of the cocone on the system of Chow groups of the stages is `CH_k(X')`. -/
@[simp]
theorem chowCocone_pt (k : ℤ) :
    (s.chowCocone k).pt = AddCommGrpCat.of (chowGroup s.limitBaseChange.baseChange
      (pullback.snd s.X.hom s.limitBaseChange.g) k) :=
  rfl

variable [HasColimitsOfShape Iᵒᵖ AddCommGrpCat.{u}]

/-- The homomorphism `colim_i CH_k(X_i) ⟶ CH_k(X')` induced by the comparison homomorphisms of
Stacks 0FVQ. Stacks 0FH6 asserts that it is an isomorphism when the system is the one of the
finite subextensions of an algebraic field extension. -/
def chowColimitComparison (k : ℤ) : colimit (s.chowDiagram k) ⟶ (s.chowCocone k).pt :=
  colimit.desc (s.chowDiagram k) (s.chowCocone k)

/-- On the image of a stage the homomorphism out of the colimit is the comparison homomorphism of
that stage. -/
theorem chowColimitComparison_ι (k : ℤ) (i : I)
    (β : chowGroup (s.stageSituation i) (pullback.snd s.X.hom (s.stageToBase i)) k) :
    s.chowColimitComparison k (colimit.ι (s.chowDiagram k) (op i) β) =
      s.stageChowPullback i k β :=
  congrArg (fun m : (s.chowDiagram k).obj (op i) ⟶ (s.chowCocone k).pt =>
      ConcreteCategory.hom m β)
    (colimit.ι_desc (s.chowCocone k) (op i))

/-- **Stacks Project, Tag 0FVQ, surjectivity through the colimit.** The homomorphism
`colim_i CH_k(X_i) ⟶ CH_k(X')` is surjective: every `k`-cycle class on `X'` is already the
image of a `k`-cycle class on some stage. -/
theorem surjective_chowColimitComparison (k : ℤ) :
    Function.Surjective (s.chowColimitComparison k) := by
  intro α
  obtain ⟨i, β, hβ⟩ := s.exists_stageChowPullback_eq k α
  exact ⟨colimit.ι (s.chowDiagram k) (op i) β,
    (s.chowColimitComparison_ι k i β).trans hβ⟩

/-- **Stacks Project, Tag 0FVQ, injectivity through the colimit.** The homomorphism
`colim_i CH_k(X_i) ⟶ CH_k(X')` is injective.

The index category being filtered, an element of the colimit is the image of a `k`-cycle class
on some stage, and that class is killed by base change to `X'`. By
`Stacks.Chow.FilteredBaseChangeSystem.exists_transitionChowPullback_eq_zero` some transition
kills it, so it already vanishes in the colimit. -/
theorem injective_chowColimitComparison
    [PreservesColimitsOfShape Iᵒᵖ (forget AddCommGrpCat.{u})] (k : ℤ) :
    Function.Injective (s.chowColimitComparison k) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨a, β, rfl⟩ := Concrete.colimit_exists_rep (s.chowDiagram k) x
  rw [s.chowColimitComparison_ι k a.unop β] at hx
  obtain ⟨b, f, hf⟩ := s.exists_transitionChowPullback_eq_zero a.unop k β hx
  have hmap : (s.chowDiagram k).map f.op β = 0 := hf
  rw [← colimit.w_apply (s.chowDiagram k) f.op β, hmap, map_zero]

end FilteredBaseChangeSystem

/-! ### The finite subextensions of a field extension -/

/-- The finite subextensions of a field extension, ordered by inclusion. -/
abbrev FiniteSubextension (k K : Type u) [Field k] [Field K] [Algebra k K] : Type u :=
  {E : IntermediateField k K // FiniteDimensional k E}

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- The trivial subextension is finite, so there is at least one finite subextension. -/
instance : Nonempty (FiniteSubextension k K) := ⟨⟨⊥, inferInstance⟩⟩

/-- The finite subextensions are directed: the compositum of two of them is one. -/
instance : IsDirectedOrder (FiniteSubextension k K) where
  directed E F := ⟨⟨E.1 ⊔ F.1, have := E.2; have := F.2; inferInstance⟩,
    Subtype.coe_le_coe.mp le_sup_left, Subtype.coe_le_coe.mp le_sup_right⟩

/-- The directed system of the finite subextensions of `K/k` as commutative rings, with the
inclusions as transition homomorphisms. -/
def finiteSubextensionRingDiagram : FiniteSubextension k K ⥤ CommRingCat.{u} where
  obj E := CommRingCat.of E.1
  map {_ _} h := CommRingCat.ofHom (IntermediateField.inclusion (leOfHom h)).toRingHom
  map_id _ := by ext x; rfl
  map_comp _ _ := by ext x; rfl

/-- The cocone on the system of finite subextensions with vertex `K`, whose legs are the
inclusions of the subextensions into `K`. -/
def finiteSubextensionRingCocone : Cocone (finiteSubextensionRingDiagram k K) where
  pt := CommRingCat.of K
  ι :=
    { app E := CommRingCat.ofHom (E.1.val).toRingHom
      naturality := by intro E F h; ext x; rfl }

/-- **An algebraic extension is the filtered colimit of its finite subextensions.** Every element
of `K` is algebraic over `k`, hence lies in the finite subextension it generates, and the
inclusion of a subextension into `K` is injective. -/
@[ega "IV 9.1.3" "special case"]
def isColimit_finiteSubextensionRingCocone [Algebra.IsAlgebraic k K] :
    IsColimit (finiteSubextensionRingCocone k K) := by
  letI := reflectsColimit_of_reflectsIsomorphisms (finiteSubextensionRingDiagram k K)
    (forget CommRingCat)
  apply isColimitOfReflects (forget CommRingCat)
  refine Types.FilteredColimit.isColimitOf'
    (F := finiteSubextensionRingDiagram k K ⋙ forget CommRingCat)
    ((forget CommRingCat).mapCocone (finiteSubextensionRingCocone k K))
    (fun x => ?_) (fun E x y h => ?_)
  · let y : K := x
    exact ⟨⟨IntermediateField.adjoin k {y},
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral y)⟩,
      ⟨y, IntermediateField.mem_adjoin_simple_self k y⟩, rfl⟩
  · exact ⟨E, 𝟙 E, Subtype.ext h⟩

/-- **The cofiltered inverse system `k' ↦ Spec k'` of base schemes** attached to a field
extension `K/k`, indexed by the opposite of the finite subextensions. -/
def finiteSubextensionDiagram : (FiniteSubextension k K)ᵒᵖ ⥤ Scheme.{u} :=
  (finiteSubextensionRingDiagram k K).op ⋙ Scheme.Spec

/-- The cone on the inverse system of the spectra of the finite subextensions with vertex
`Spec K`. -/
def finiteSubextensionCone : Cone (finiteSubextensionDiagram k K) :=
  Scheme.Spec.mapCone (finiteSubextensionRingCocone k K).op

/-- **`Spec K` is the limit of the spectra of the finite subextensions of an algebraic extension
`K/k`.** The extension is the filtered colimit of its finite subextensions and `Spec` is a right
adjoint, so it carries that colimit of rings to a limit of schemes. -/
@[ega "IV 9.1.3" "special case"]
def isLimit_finiteSubextensionCone [Algebra.IsAlgebraic k K] :
    IsLimit (finiteSubextensionCone k K) :=
  isLimitOfPreserves Scheme.Spec (isColimit_finiteSubextensionRingCocone k K).op

/-- The structure morphism `Spec k' ⟶ Spec k` of a stage of the inverse system. -/
def finiteSubextensionToBase (i : (FiniteSubextension k K)ᵒᵖ) :
    (finiteSubextensionDiagram k K).obj i ⟶ (fieldChowSituation k).S :=
  Spec.map (CommRingCat.ofHom (algebraMap k i.unop.1))

/-! ### The situation of Stacks 0FVQ attached to an algebraic field extension -/

/-- **The situation of Stacks 0FVQ attached to an algebraic field extension `K/k` and a
quasi-compact scheme `X` of finite type over `k`.** The base is `Spec k`, the stages are the
spectra of the finite subextensions with their vanishing dimension functions, and the limit base
is `Spec K`. -/
def algebraicExtensionSystem [Algebra.IsAlgebraic k K]
    (X : Over (fieldChowSituation k).S) [CompactSpace X.left] [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    FilteredBaseChangeSystem.{u, u, u} (FiniteSubextension k K)ᵒᵖ where
  limitBaseChange := fieldExtensionBaseChangeSituation k K
  shift_eq_zero := rfl
  diagram := finiteSubextensionDiagram k K
  cone := finiteSubextensionCone k K
  isLimit := isLimit_finiteSubextensionCone k K
  limitIdentification := Iso.refl _
  stageToBase := finiteSubextensionToBase k K
  stageToBase_naturality := by
    intro i j h
    change Spec.map (CommRingCat.ofHom
          (IntermediateField.inclusion (leOfHom h.unop)).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k j.unop.1)) =
      Spec.map (CommRingCat.ofHom (algebraMap k i.unop.1))
    rw [← Spec.map_comp]
    congr 1
  limitToBase_comm := by
    intro i
    change Spec.map (CommRingCat.ofHom (i.unop.1).val.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k i.unop.1)) =
      (Iso.refl _).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k K))
    rw [← Spec.map_comp, Iso.refl_hom, Category.id_comp]
    congr 1
  stageAffine i := by
    have : IsAffine ((finiteSubextensionDiagram k K).obj i) :=
      inferInstanceAs (IsAffine (AlgebraicGeometry.Spec (CommRingCat.of i.unop.1)))
    have : IsAffine (fieldChowSituation k).S :=
      inferInstanceAs (IsAffine (AlgebraicGeometry.Spec (CommRingCat.of k)))
    exact isAffineHom_of_isAffine (finiteSubextensionToBase k K i)
  stageLocallyNoetherian i := by
    dsimp [finiteSubextensionDiagram, finiteSubextensionRingDiagram]
    infer_instance
  stageUniversallyCatenary i := Scheme.isUniversallyCatenary_spec_of_field i.unop.1
  stageDimension i := fieldDimensionFunction i.unop.1
  stageDimension_eq := fun _ _ => rfl
  transitionFlat := by
    intro i j h
    dsimp [finiteSubextensionDiagram, finiteSubextensionRingDiagram]
    exact Flat.SpecMap_iff.mpr (RingHom.Flat.of_isField (Field.toIsField _)
      (IntermediateField.inclusion (leOfHom h.unop)).toRingHom)
  X := X

/-- The limit base change of the system of finite subextensions of `K / k` is the flat base change
of Chow situations along `Spec K ⟶ Spec k`. -/
@[simp]
theorem algebraicExtensionSystem_limitBaseChange [Algebra.IsAlgebraic k K]
    (X : Over (fieldChowSituation k).S) [CompactSpace X.left] [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    (algebraicExtensionSystem k K X).limitBaseChange = fieldExtensionBaseChangeSituation k K :=
  rfl

/-- The scheme over `Spec k` underlying the system of finite subextensions of `K / k` is `X`. -/
@[simp]
theorem algebraicExtensionSystem_X [Algebra.IsAlgebraic k K]
    (X : Over (fieldChowSituation k).S) [CompactSpace X.left] [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    (algebraicExtensionSystem k K X).X = X :=
  rfl

/-- Any morphism between spectra of fields is surjective on points. -/
private theorem surjective_spec_map_of_field {F L : Type u} [Field F] [Field L]
    (f : AlgebraicGeometry.Spec (CommRingCat.of F) ⟶ AlgebraicGeometry.Spec (CommRingCat.of L)) :
    Surjective f :=
  surjective_of_subsingleton f

/-- The projection `Spec K ⟶ Spec k'` from the limit base to a stage is surjective on points:
the spectrum of a field is a single point. -/
theorem surjective_limitProjection_algebraicExtensionSystem [Algebra.IsAlgebraic k K]
    (X : Over (fieldChowSituation k).S) [CompactSpace X.left] [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] (i : (FiniteSubextension k K)ᵒᵖ) :
    Surjective ((algebraicExtensionSystem k K X).limitProjection i) := by
  exact surjective_spec_map_of_field (F := K) (L := i.unop.1)
    ((algebraicExtensionSystem k K X).limitProjection i)

/-- A transition morphism `Spec k'' ⟶ Spec k'` of the inverse system of bases is surjective on
points: the spectrum of a field is a single point. -/
theorem surjective_diagram_map_algebraicExtensionSystem [Algebra.IsAlgebraic k K]
    (X : Over (fieldChowSituation k).S) [CompactSpace X.left] [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] {i j : (FiniteSubextension k K)ᵒᵖ} (h : i ⟶ j) :
    Surjective ((algebraicExtensionSystem k K X).diagram.map h) := by
  exact surjective_spec_map_of_field (F := i.unop.1) (L := j.unop.1)
    ((algebraicExtensionSystem k K X).diagram.map h)

/-- **Injectivity on cycle groups for an algebraic field extension.** The comparison homomorphism
`Z_i(X_{k'}) ⟶ Z_i(X_K)` is injective, not merely injective after passing to a later stage: the
projection `Spec K ⟶ Spec k'` is surjective because both are single points. -/
theorem injective_stageCyclePullback_algebraicExtensionSystem [Algebra.IsAlgebraic k K]
    (X : Over (fieldChowSituation k).S) [CompactSpace X.left] [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] (i : (FiniteSubextension k K)ᵒᵖ) (r : ℤ) :
    Function.Injective ((algebraicExtensionSystem k K X).stageCyclePullback i r) :=
  have := surjective_limitProjection_algebraicExtensionSystem k K X i
  (algebraicExtensionSystem k K X).injective_stageCyclePullback i r

/-- **Injectivity on cycle groups along a transition for an algebraic field extension.** The
comparison homomorphism `Z_i(X_{k''}) ⟶ Z_i(X_{k'})` of two finite subextensions is injective. -/
theorem injective_transitionCyclePullback_algebraicExtensionSystem [Algebra.IsAlgebraic k K]
    (X : Over (fieldChowSituation k).S) [CompactSpace X.left] [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] {i j : (FiniteSubextension k K)ᵒᵖ} (h : i ⟶ j) (r : ℤ) :
    Function.Injective ((algebraicExtensionSystem k K X).transitionCyclePullback h r) :=
  have := surjective_diagram_map_algebraicExtensionSystem k K X h
  (algebraicExtensionSystem k K X).injective_transitionCyclePullback h r

/-- **Surjectivity of the colimit comparison for an algebraic field extension.** The
homomorphism `colim_{k'} CH_k(X_{k'}) ⟶ CH_k(X_K)`, the colimit being over the finite
subextensions of `K/k`, is surjective. It is the surjectivity half of
`Stacks.Chow.chowColimitAddEquiv_algebraicExtensionSystem`, which is Stacks 0FH6. -/
theorem surjective_chowColimitComparison_algebraicExtensionSystem [Algebra.IsAlgebraic k K]
    (X : Over (fieldChowSituation k).S) [CompactSpace X.left] [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] (i : ℤ) :
    Function.Surjective ((algebraicExtensionSystem k K X).chowColimitComparison i) :=
  (algebraicExtensionSystem k K X).surjective_chowColimitComparison i

/-! ### Chow groups over an algebraic field extension -/

/-- **Stacks Project, Tag 0FH6, bijectivity of the colimit comparison.** The homomorphism
`colim_{k'} CH_i(X_{k'}) ⟶ CH_i(X_K)`, the colimit being over the finite subextensions of
`K/k`, is bijective. -/
theorem bijective_chowColimitComparison_algebraicExtensionSystem [Algebra.IsAlgebraic k K]
    (X : Over (fieldChowSituation k).S) [CompactSpace X.left] [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] (i : ℤ) :
    Function.Bijective ((algebraicExtensionSystem k K X).chowColimitComparison i) :=
  ⟨(algebraicExtensionSystem k K X).injective_chowColimitComparison i,
    surjective_chowColimitComparison_algebraicExtensionSystem k K X i⟩

/-- **Stacks Project, Tag 0FH6.** For an algebraic field extension `K/k` and a quasi-compact
scheme `X` of finite type over `k`, the Chow group `CH_i(X_K)` is the colimit of the Chow groups
`CH_i(X_{k'})` over the finite subextensions `K/k'/k`, along the base-change homomorphisms. -/
@[stacks 0FH6 "CH_i(X_K) is the colimit of the CH_i(X_{k'}) over the finite subextensions
K/k'/k of an algebraic extension"]
def chowColimitAddEquiv_algebraicExtensionSystem [Algebra.IsAlgebraic k K]
    (X : Over (fieldChowSituation k).S) [CompactSpace X.left] [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] (i : ℤ) :
    ↥(colimit ((algebraicExtensionSystem k K X).chowDiagram i)) ≃+
      chowGroup (fieldChowSituation K)
        (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))) i :=
  AddEquiv.ofBijective ((algebraicExtensionSystem k K X).chowColimitComparison i).hom
    (bijective_chowColimitComparison_algebraicExtensionSystem k K X i)

end Stacks.Chow

end
