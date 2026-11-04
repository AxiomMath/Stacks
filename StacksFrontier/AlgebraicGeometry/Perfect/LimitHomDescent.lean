module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Perfect.LimitPerfectObjects
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SectionsColimitDescent
public import StacksFrontier.Homology.HomotopyCategory.FilteredColimitHom
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.Defs
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.OnARingedSpace
public import StacksFrontier.AlgebraicGeometry.Perfect.LimitHomDescent.Assembly
public import StacksCore.Tactic.StacksAttribute

/-!
# Homomorphisms in the derived category along a limit of schemes

In Situation 09RD — a directed inverse system `i ↦ S_i` of quasi-compact and quasi-separated
schemes with affine transition morphisms, a chosen limit `S` and a chosen index `0` — let `E₀`
and `K₀` be objects of `D(𝒪_{S₀})`.  Put `E_i = Lf_{i0}^*E₀` and `K_i = Lf_{i0}^*K₀` for `i ≥ 0`,
and `E = Lf_0^*E₀`, `K = Lf_0^*K₀`.  Stacks 09RE asserts that

`colim_{i ≥ 0} Hom_{D(𝒪_{S_i})}(E_i, K_i) ⟶ Hom_{D(𝒪_S)}(E, K)`

is an isomorphism if either `E₀` is perfect and `K₀` lies in `D_QCoh(𝒪_{S₀})`, or `E₀` is
pseudo-coherent and `K₀` lies in `D_QCoh(𝒪_{S₀})` and has finite Tor dimension.

Bijectivity of a map out of a filtered colimit of sets is `Stacks.IsStagesColimit`, the
elementwise form: the maps to the vertex form a cocone, they are jointly surjective, and two
elements of one stage with the same image agree at a later stage.  For a directed index those
three clauses are exactly the assertion that the comparison out of the colimit is a bijection.

## Main definitions

* `AlgebraicGeometry.DescentSituation.Stages`: the stages `i ≥ 0` of Situation 09RD.
* `AlgebraicGeometry.DescentSituation.stageObj` and `limitObj`: the objects `E_i = Lf_{i0}^*E₀`
  and `E = Lf_0^*E₀` of the tag.
* `AlgebraicGeometry.DescentSituation.homTransition` and `homProjection`: the maps
  `Hom(E_i, K_i) → Hom(E_j, K_j)` and `Hom(E_i, K_i) → Hom(E, K)` of the tag's directed system.
* `AlgebraicGeometry.DescentSituation.IsHomColimit`: the conclusion of Stacks 09RE,
  `Hom_{D(𝒪_S)}(E, K)` is the filtered colimit of the `Hom_{D(𝒪_{S_i})}(E_i, K_i)`.
* `AlgebraicGeometry.DescentSituation.toSchemeSystem`: the stages `i ≥ 0` as a system of
  schemes over `S₀`.

## Main results

* `AlgebraicGeometry.DescentSituation.homTransition_homTransition` and
  `homProjection_homTransition`: the maps of the directed system compose, and the maps to the
  limit form a cocone on it.
* `AlgebraicGeometry.DescentSituation.isHomColimit`: **Stacks 09RE.**

## Implementation notes

The proof is the source's.  By the induction principle of Stacks 08DR over the quasi-compact
opens of `S₀`, with the distinguished triangle of Stacks 08BU at the union step, the statement
reduces to the restrictions of the system to the affine opens `U ⊆ S₀`
(`Stacks.LimitHomDescent.SchemeSystem.isColim_of_isAffineOpen`).  Over `U = Spec(A₀)` the
restricted stages are the spectra of rings `A_i` with colimit `A`, and by Stacks 06Z0, 08EB,
08E7 and 08E9 the objects are the derived sheafifications of a bounded complex of finite
projective, respectively a bounded above complex of finite free, `A₀`-modules and of a K-flat
complex; the homomorphism groups are then those of the homotopy category of `A_i`-modules, which
form a filtered colimit (`Stacks.LimitHomDescent.Affine.RingSystem.isColim_of_isPerfect` and
`isColim_of_isPseudoCoherent`).

The index set of Situation 09RD is taken in the universe of the schemes.  Over an index set one
universe up the statement is false:
`AlgebraicGeometry.DescentSituation.exists_not_isHomColimit` exhibits such a situation with an
empty limit.

The two unconditional results are the cocycle identities of the comparison isomorphisms,
`AlgebraicGeometry.DescentSituation.pullbackTransitionIso_assoc` and
`pullbackProjectionIso_assoc` of
`StacksFrontier/AlgebraicGeometry/Perfect/LimitPerfectObjects.lean`, themselves
`Stacks.DerivedPullback.factorIso_assoc`.  Both are deduced from one lemma,
`Stacks.LimitHomDescent.conjugate_eq`, stated with every category, functor and object a
variable: on the concrete goal neither `Functor.map_comp` nor `Category.assoc` fires, because
`AlgebraicGeometry.Scheme.Modules` is `implicit_reducible` and unfolds to
`SheafOfModules (RingedSpaceModuleAdjunction.ringSheaf _)` carrying a different category
instance.

A stage of the tag's system is an element of the subtype `{i // 0 ≤ i}`, and the comparison
isomorphisms are indexed by the ambient proofs `i.2 : 0 ≤ i`; a composite stage therefore carries
the proof `i.2.trans h` where the subtype carries `j.2`.  The two are interchangeable by
definitional proof irrelevance, so no transport appears.

## References

* [Stacks Project, Lemma 36.29.2 (Tag 09RE)](https://stacks.math.columbia.edu/tag/09RE)
* [Stacks Project, Situation 36.29.1 (Tag 09RD)](https://stacks.math.columbia.edu/tag/09RD)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
* [Stacks Project, Tag 08BU](https://stacks.math.columbia.edu/tag/08BU)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08EB](https://stacks.math.columbia.edu/tag/08EB)
* [Stacks Project, Tag 08E7](https://stacks.math.columbia.edu/tag/08E7)
* [Stacks Project, Tag 08E9](https://stacks.math.columbia.edu/tag/08E9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

attribute [local instance 10000] HasDerivedCategory.standard

universe v u

namespace Stacks.LimitHomDescent

/-- **Conjugating a morphism by two coherent comparison isomorphisms does not depend on the
route.** Let `T`, `U`, `V` be functors out of `C`, let `Q`, `P`, `R` be functors with
`sc : T ⋙ Q ≅ U`, `pcj : U ⋙ P ≅ V`, `pci : T ⋙ R ≅ V` and `A : Q ⋙ P ≅ R`, and suppose the
four comparisons cohere. Then transporting a morphism `T.obj E ⟶ T.obj K` to `V.obj E ⟶ V.obj K`
through `Q` and then `P` gives the same result as transporting it through `R`.

At `T = Lf_{i0}^*`, `U = Lf_{j0}^*`, `V = Lf_0^*`, `Q = Lf_{ji}^*`, `P = Lf_j^*` and
`R = Lf_i^*` this is the cocone clause of Stacks 09RE. It is stated with every object and
functor a variable, so that the rewrites inside it meet no concrete spelling. -/
theorem conjugate_eq {C : Type*} [Category C] {A : Type*} [Category A] {B : Type*} [Category B]
    {Z : Type*} [Category Z] {T : C ⥤ A} {U : C ⥤ B} {V : C ⥤ Z} {Q : A ⥤ B} {P : B ⥤ Z}
    {R : A ⥤ Z} (sc : T ⋙ Q ≅ U) (pcj : U ⋙ P ≅ V) (pci : T ⋙ R ≅ V) (cmp : Q ⋙ P ≅ R)
    (coh : ∀ M : C, P.map ((sc.app M).hom) ≫ (pcj.app M).hom =
      (cmp.app (T.obj M)).hom ≫ (pci.app M).hom)
    (E K : C) (g : T.obj E ⟶ T.obj K) :
    (pcj.app E).inv ≫ P.map ((sc.app E).inv ≫ Q.map g ≫ (sc.app K).hom) ≫ (pcj.app K).hom =
      (pci.app E).inv ≫ R.map g ≫ (pci.app K).hom := by
  have hiso : ∀ M : C, P.mapIso (sc.app M) ≪≫ pcj.app M = cmp.app (T.obj M) ≪≫ pci.app M :=
    fun M => Iso.ext (coh M)
  have hinv : ∀ M : C, (pcj.app M).inv ≫ P.map ((sc.app M).inv) =
      (pci.app M).inv ≫ (cmp.app (T.obj M)).inv := fun M => congrArg Iso.inv (hiso M)
  have hnat : P.map (Q.map g) ≫ (cmp.app (T.obj K)).hom =
      (cmp.app (T.obj E)).hom ≫ R.map g := cmp.hom.naturality g
  rw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [coh K, reassoc_of% hnat, reassoc_of% (hinv E), Iso.inv_hom_id_assoc]

end Stacks.LimitHomDescent

namespace AlgebraicGeometry.DescentSituation

variable {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] {D : DescentSituation.{v, u} I}

/-! ### The stages `i ≥ 0` -/

/-- The stages of Situation 09RD at or beyond its chosen index — the source's `i ≥ 0` — as a
preorder. -/
abbrev Stages (D : DescentSituation.{v, u} I) := {i : I // D.base ≤ i}

/-- The stages at or beyond the chosen index are directed, the ambient index being directed. -/
instance isDirectedStages : IsDirected D.Stages (· ≤ ·) where
  directed i j := by
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i.1 j.1
    exact ⟨⟨k, i.2.trans hik⟩, hik, hjk⟩

/-! ### The objects and the comparison maps of Stacks 09RE -/

/-- **The object `E_i = Lf_{i0}^*E₀` of Stacks 09RE.** -/
def stageObj (E₀ : DerivedCategory (D.stage D.base).Modules) (i : D.Stages) :
    DerivedCategory (D.stage i.1).Modules :=
  (derivedPullback (D.transition i.2).toLRSHom.toShHom).obj E₀

/-- **The object `E = Lf_0^*E₀` of Stacks 09RE.** -/
def limitObj (E₀ : DerivedCategory (D.stage D.base).Modules) :
    DerivedCategory D.limitScheme.Modules :=
  (derivedPullback (D.projection D.base).toLRSHom.toShHom).obj E₀

/-- The comparison `Lf_{i0}^* ⋙ Lf_{ji}^* ≅ Lf_{j0}^*` of the factorisation
`f_{ji} ≫ f_{i0} = f_{j0}`, which identifies `Lf_{ji}^*E_i` with `E_j`. -/
def stageComp {i j : D.Stages} (h : i ≤ j) :
    derivedPullback (D.transition i.2).toLRSHom.toShHom ⋙
        derivedPullback (D.transition (show i.1 ≤ j.1 from h)).toLRSHom.toShHom ≅
      derivedPullback (D.transition j.2).toLRSHom.toShHom :=
  D.pullbackTransitionIso i.2 (show i.1 ≤ j.1 from h)

/-- The comparison `Lf_{i0}^* ⋙ Lf_i^* ≅ Lf_0^*` of the factorisation `f_i ≫ f_{i0} = f_0`,
which identifies `Lf_i^*E_i` with `E`. -/
def projComp (i : D.Stages) :
    derivedPullback (D.transition i.2).toLRSHom.toShHom ⋙
        derivedPullback (D.projection i.1).toLRSHom.toShHom ≅
      derivedPullback (D.projection D.base).toLRSHom.toShHom :=
  D.pullbackProjectionIso i.2

variable (E₀ K₀ : DerivedCategory (D.stage D.base).Modules)

/-- **The transition map `Hom_{D(𝒪_{S_i})}(E_i, K_i) → Hom_{D(𝒪_{S_j})}(E_j, K_j)` of
Stacks 09RE**: apply `Lf_{ji}^*` and read the result through the comparison
`Lf_{ji}^*Lf_{i0}^* ≅ Lf_{j0}^*` at `E₀` and at `K₀`. -/
def homTransition (i j : D.Stages) (h : i ≤ j) :
    (stageObj E₀ i ⟶ stageObj K₀ i) → (stageObj E₀ j ⟶ stageObj K₀ j) := fun g =>
  ((stageComp h).app E₀).inv ≫
    (derivedPullback (D.transition (show i.1 ≤ j.1 from h)).toLRSHom.toShHom).map g ≫
      ((stageComp h).app K₀).hom

/-- **The map `Hom_{D(𝒪_{S_i})}(E_i, K_i) → Hom_{D(𝒪_S)}(E, K)` of Stacks 09RE**: apply `Lf_i^*`
and read the result through the comparison `Lf_i^*Lf_{i0}^* ≅ Lf_0^*` at `E₀` and at `K₀`. -/
def homProjection (i : D.Stages) :
    (stageObj E₀ i ⟶ stageObj K₀ i) → (limitObj E₀ ⟶ limitObj K₀) := fun g =>
  ((projComp i).app E₀).inv ≫
    (derivedPullback (D.projection i.1).toLRSHom.toShHom).map g ≫ ((projComp i).app K₀).hom

/-- **The cocone clause of the conclusion of Stacks 09RE.** Pushing a homomorphism from the
stage `i` to the stage `j` and then to the limit gives the same homomorphism `E ⟶ K` as pushing
it to the limit directly.

This holds for all `E₀` and `K₀`: it is the coherence of the two comparison
isomorphisms of derived pullback along the factorisations `f_{ji} ≫ f_{i0} = f_{j0}` and
`f_j ≫ f_{ji} = f_i`, together with the naturality of the second. -/
@[stacks 09RE "the maps to Hom(E, K) are compatible with the transition maps of the directed \
system, for all E_0 and K_0"]
theorem homProjection_homTransition (i j : D.Stages) (h : i ≤ j)
    (g : stageObj E₀ i ⟶ stageObj K₀ i) :
    homProjection E₀ K₀ j (homTransition E₀ K₀ i j h g) = homProjection E₀ K₀ i g :=
  Stacks.LimitHomDescent.conjugate_eq (stageComp h) (projComp j) (projComp i)
    (D.pullbackProjectionIso (show i.1 ≤ j.1 from h))
    (fun M => (D.pullbackProjectionIso_assoc i.2 (show i.1 ≤ j.1 from h) M).symm) E₀ K₀ g

/-- **The maps of the directed system of Stacks 09RE compose.** For `i ≤ j ≤ k` among the
stages, pushing a homomorphism from the stage `i` to the stage `j` and then to the stage `k`
gives the same homomorphism `E_k ⟶ K_k` as pushing it to the stage `k` directly. Together with
`AlgebraicGeometry.DescentSituation.homProjection_homTransition` this says that
`i ↦ Hom_{D(𝒪_{S_i})}(E_i, K_i)` is a system over the stages and that the maps to
`Hom_{D(𝒪_S)}(E, K)` form a cocone on it, which is what makes the colimit the tag speaks of
well-posed.

Like the cocone clause, this holds for all `E₀` and `K₀`; it is the cocycle
identity of the comparisons `Lf_{i0}^* ⋙ Lf_{ji}^* ≅ Lf_{j0}^*`. -/
@[stacks 09RE "the directed system whose colimit the tag takes: its transition maps compose, \
for all E_0 and K_0"]
theorem homTransition_homTransition (i j k : D.Stages) (h : i ≤ j) (h' : j ≤ k)
    (g : stageObj E₀ i ⟶ stageObj K₀ i) :
    homTransition E₀ K₀ j k h' (homTransition E₀ K₀ i j h g) =
      homTransition E₀ K₀ i k (h.trans h') g :=
  Stacks.LimitHomDescent.conjugate_eq (stageComp h) (stageComp h') (stageComp (h.trans h'))
    (D.pullbackTransitionIso (show i.1 ≤ j.1 from h) (show j.1 ≤ k.1 from h'))
    (fun M => (D.pullbackTransitionIso_assoc i.2 (show i.1 ≤ j.1 from h)
      (show j.1 ≤ k.1 from h') M).symm) E₀ K₀ g

/-- **The conclusion of Stacks 09RE**: the map

`colim_{i ≥ 0} Hom_{D(𝒪_{S_i})}(E_i, K_i) ⟶ Hom_{D(𝒪_S)}(E, K)`

is an isomorphism, in the elementwise form `Stacks.IsStagesColimit` — the maps
`AlgebraicGeometry.DescentSituation.homProjection` form a cocone on the system given by
`AlgebraicGeometry.DescentSituation.homTransition`, they are jointly surjective, and two
homomorphisms at one stage with the same image at the limit already agree at a later stage.  The
index is directed, so these three clauses are precisely bijectivity of the comparison out of the
colimit. -/
def IsHomColimit : Prop :=
  Stacks.IsStagesColimit (homTransition E₀ K₀) (homProjection E₀ K₀)

/-! ### Stacks 09RE -/

/-- **The system of schemes of Situation 09RD over `S₀`**: the stages `S_i` for `i ≥ 0` with
their morphisms `f_{i0}` to `S₀`, the transition morphisms `f_{ji}`, and the limit `S` with its
projections. -/
def toSchemeSystem (D : DescentSituation.{v, u} I) :
    Stacks.LimitHomDescent.SchemeSystem.{v, u} (D.stage D.base) D.Stages where
  stage j := D.stage j.1
  toBase j := D.transition j.2
  transition h := D.transition (show _ ≤ _ from h)
  transition_toBase {i _} h := D.transition_comp_transition i.2 h
  transition_comp h h' := D.transition_comp_transition h h'
  transition_refl i := D.transition_refl i.1
  limit := D.limitScheme
  limitToBase := D.projection D.base
  proj j := D.projection j.1
  proj_toBase j := D.projection_comp_transition j.2
  proj_transition h := D.projection_comp_transition h

/-- `Hom(E, K)` is the filtered colimit of the `Hom(E_i, K_i)` exactly when it is so for the
system of schemes of the situation. -/
theorem isHomColimit_iff : IsHomColimit E₀ K₀ ↔ D.toSchemeSystem.IsColim E₀ K₀ := Iff.rfl

/-- The inclusion of the stages `i ≥ 0` into the index is final. -/
theorem final_stages : (Subtype.mono_coe (fun i : I => D.base ≤ i)).functor.Final :=
  (Monotone.final_functor_iff _).2 fun i => by
    obtain ⟨k, hik, hk⟩ := directed_of (· ≤ ·) i D.base
    exact ⟨⟨k, hk⟩, hik⟩

/-- The limit of the stages `i ≥ 0` is the limit of the system. -/
def isLimitToSchemeSystem : IsLimit D.toSchemeSystem.cone :=
  have := D.final_stages
  (Functor.Initial.isLimitWhiskerEquiv (Subtype.mono_coe (fun i : I => D.base ≤ i)).functor.op
    D.limitCone).symm D.isLimit

end AlgebraicGeometry.DescentSituation

namespace AlgebraicGeometry.DescentSituation

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] {D : DescentSituation.{u, u} I}
  (E₀ K₀ : DerivedCategory (D.stage D.base).Modules)

/-- **Stacks 09RE.** In Situation 09RD, let `E₀` and `K₀` be objects of `D(𝒪_{S₀})`, put
`E_i = Lf_{i0}^*E₀`, `K_i = Lf_{i0}^*K₀` for `i ≥ 0` and `E = Lf_0^*E₀`, `K = Lf_0^*K₀`.  If
either `E₀` is perfect and `K₀` lies in `D_QCoh(𝒪_{S₀})`, or `E₀` is pseudo-coherent and `K₀`
lies in `D_QCoh(𝒪_{S₀})` and has finite Tor dimension, then

`colim_{i ≥ 0} Hom_{D(𝒪_{S_i})}(E_i, K_i) ⟶ Hom_{D(𝒪_S)}(E, K)`

is an isomorphism.

The index set lies in the universe of the schemes; over a larger index set the statement fails,
see `AlgebraicGeometry.DescentSituation.exists_not_isHomColimit`. -/
@[stacks 09RE]
theorem isHomColimit
    (hcase :
      (Stacks.Cohomology.PerfectComplexes.IsPerfect
            (X := (D.stage D.base).toRingedSpace) E₀ ∧
          ∀ n : ℤ, SheafOfModules.isQuasicoherent (D.stage D.base).ringCatSheaf
            ((DerivedCategory.homologyFunctor (D.stage D.base).Modules n).obj K₀)) ∨
        (AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent
            (X := (D.stage D.base).toRingedSpace) E₀ ∧
          (∀ n : ℤ, SheafOfModules.isQuasicoherent (D.stage D.base).ringCatSheaf
            ((DerivedCategory.homologyFunctor (D.stage D.base).Modules n).obj K₀)) ∧
          Stacks.Cohomology.TorAmplitude.HasFiniteTorDimension
            (D.stage D.base).toRingedSpace K₀)) :
    IsHomColimit E₀ K₀ := by
  have := D.quasiCompact D.base
  have := D.quasiSeparated D.base
  have : Nonempty D.Stages := ⟨⟨D.base, le_rfl⟩⟩
  have : ∀ j : D.Stages, IsAffineHom (D.toSchemeSystem.toBase j) := fun j =>
    D.transition_affine _
  refine (isHomColimit_iff E₀ K₀).2 ?_
  rcases hcase with ⟨hE, hK⟩ | ⟨hE, hK, hKt⟩
  · exact D.toSchemeSystem.isColim_of_isPerfect D.isLimitToSchemeSystem E₀ K₀ hE hK
  · exact D.toSchemeSystem.isColim_of_isPseudoCoherent D.isLimitToSchemeSystem E₀ K₀ hE hK hKt

end AlgebraicGeometry.DescentSituation

end
