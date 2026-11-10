module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.RestrictionOfComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.ConeOfAMorphism
public import StacksCore.Algebra.Homology.ShortComplex.HomologicalComplex
import StacksCore.Tactic.StacksAttribute

/-!
# Local null-homotopy of maps out of strictly perfect complexes

Let `(C, O)` be a ringed site, `U` an object of `C`, and `α : E ⟶ F` a morphism of complexes of
`O|_U`-modules with `E` strictly perfect. If `F` is acyclic, or more generally if `F` has no
cohomology in the degrees where `E` lives, then `α` becomes null-homotopic after restriction
along every arrow of some covering sieve of `U`. This is Stacks 08FP, both parts.

## Main results

* `AlgebraicGeometry.RingedSite.exists_coveringSieve_homotopy_zero_of_acyclic`: part (1), an
  acyclic target.
* `AlgebraicGeometry.RingedSite.exists_coveringSieve_homotopy_zero_of_isZero_homology`:
  part (2), vanishing cohomology in the degrees at or above the source's lower bound.

## Implementation notes

A covering family is represented by the covering sieve it generates, and the conclusion gives
a null-homotopy after restriction along every arrow of that sieve; the cohomology hypothesis
refers to `F` over `U`, before restriction. The two parts are separate statements, part (1)
reducing to part (2) by taking the source's lower bound as `a`.

The proof is an induction on the number of degrees in which `α` may be nonzero. Each step kills
the top degree: there `α` is a cycle, so it factors through the kernel of the differential of
`F`, and that factorisation lifts along `F^{n-1} → Ker(F^n → F^{n+1})` locally on `U` because
the source is a direct summand of a finite free module and the vanishing of `H^n(F)` makes the
lifting map an epimorphism. Subtracting the resulting null-homotopic map leaves a map with one
fewer nonzero degree, to which the induction hypothesis applies — but over a slice of the
site rather than over the site itself, so the statement being inducted on quantifies over the
site, and `doubleOverHomotopy` identifies a slice of a slice with a single slice at the end.

Two things about that induction decide the shape of this file.

The lifting step is Stacks 08FN, but
`AlgebraicGeometry.RingedSite.exists_coveringSieve_lift` cannot be applied: its modules live on
a slice `C/U` of a ringed site, whereas the induction needs the statement for an arbitrary
sheaf of rings on an arbitrary site, which is not the structure sheaf of any `RingedSite` (that
one is a sheaf of *commutative* rings), and it concludes from `Epi p`, which the induction does
not have — it has a restriction of an epimorphism, whose epimorphy is not available. So the
lifting step is restated here as `exists_coveringSieve_lift_of_locallySurjective`, in the form
the induction consumes, by the same one-coordinate-at-a-time argument.

The finite-free hypothesis is carried as `IsFiniteFreeRetract` rather than as
`IsDirectSummandOfFiniteFree`. They say the same thing, and
`isFiniteFreeRetract_of_isDirectSummandOfFiniteFree` converts; but
`IsDirectSummandOfFiniteFree` is phrased with `SheafOfModules.free`, which requires
`HasWeakSheafify` and `WEqualsLocallyBijective` for the topology it is formed over, and nothing
propagates those two instances from a site to a slice of it. Since the induction descends
through arbitrarily deep iterated slices, the hypothesis it carries has to name no
sheafification functor at all: `IsFiniteFreeRetract` asks for a retract off an explicitly given
finite colimit cofan, and `IsFiniteFreeRetract.over` propagates it, restriction preserving
finite coproducts because it preserves finite limits.

**Universe narrowing.** The ring and module universes are both `0` here, and that narrowing is
this file's own. The imported `IsDirectSummandOfFiniteFree` of Stacks Tag 08FM keeps the
module universe `m` independent of the ring universe `w`: Mathlib's
`SheafOfModules.free (I : Type u)` lands in `SheafOfModules.{u} R` for `R : Sheaf J RingCat.{u}`,
so a finite free module does not exist at independent universes at all, and the comparison of `E`
with `O^{⊕n}` is therefore made in `SheafOfModules.{max m w} R` after raising the sections of both
with `Stacks.SheafOfModules.moduleULift`. At `m = w` that lift is fully faithful and the predicate
is the plain retract condition, which is the content of `isDirectSummandOfFiniteFree_iff_free` and
the form `isFiniteFreeRetract_of_isDirectSummandOfFiniteFree` below consumes. The site universes
are *not* narrowed here: `C : Type u` with `Category.{v} C` stay independent, where the library's
08FN additionally collapses `v = u`. The two statements of Stacks 08FP come in a `_general`
form at `RingedSite.{u, v, w}` and in the instance at `RingedSite.{u, v, 0}` named without the
suffix; the reindexing of the finite free cofan along `Equiv.ulift` in
`isFiniteFreeRetract_of_isDirectSummandOfFiniteFree` is what the general ring universe costs.

## References

* [Stacks Project, Tag 08FP](https://stacks.math.columbia.edu/tag/08FP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry.RingedSite

/-- A property of arrows into `U` that holds locally on a covering sieve of `U` holds on a
covering sieve of `U`: the sieve generated by the local witnesses is covering by transitivity
of the topology. -/
private theorem exists_coveringSieve_refinement
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {U : C}
    (S : Sieve U) (hS : S ∈ J U)
    (P : ∀ {V : C}, (V ⟶ U) → Prop)
    (hlocal : ∀ {V : C} (f : V ⟶ U), S f →
      ∃ R : Sieve V, R ∈ J V ∧
        ∀ {W : C} (g : W ⟶ V), R g → P (g ≫ f)) :
    ∃ T : Sieve U, T ∈ J U ∧
      ∀ {V : C} (f : V ⟶ U), T f → P f := by
  choose R hR hP using fun V (f : V ⟶ U) (hf : S f) => hlocal f hf
  refine ⟨Sieve.bind S.arrows fun V f hf => R V f hf,
    J.bind_covering hS fun V f hf => hR V f hf, ?_⟩
  rintro V _ ⟨W, g, f, hf, hg, rfl⟩
  exact hP W f hf g hg

/-- `E` is a retract of a finite coproduct of copies of the structure sheaf, witnessed by an
explicit colimit cofan.

This says exactly what `IsDirectSummandOfFiniteFree` says — see
`isFiniteFreeRetract_of_isDirectSummandOfFiniteFree` — but it names no sheafification functor,
whereas `SheafOfModules.free` requires `HasWeakSheafify` and `WEqualsLocallyBijective` for the
topology it is formed over. The induction below passes from a site to a slice of it at every
step, and nothing propagates those two instances along such a passage, so the hypothesis the
induction carries has to be this one. `IsFiniteFreeRetract.over` is the propagation. -/
private def IsFiniteFreeRetract {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{w}) (E : SheafOfModules.{w} R) : Prop :=
  ∃ (n : ℕ) (cf : Cofan fun _ : Fin n => SheafOfModules.unit R) (_ : IsColimit cf)
    (j : E ⟶ cf.pt) (r : cf.pt ⟶ E), j ≫ r = 𝟙 E

/-- A direct summand of a finite free module is a retract of a finite coproduct of copies of
the structure sheaf: take the tautological cofan with point `O^{⊕n}`.

`IsDirectSummandOfFiniteFree` compares `E` with `O^{⊕n}` in `SheafOfModules.{max m w} R`, after
raising the sections of both with `Stacks.SheafOfModules.moduleULift`, so that the module universe
`m` is independent of the ring universe `w`. Here `m = w = 0`, which is the case
`isDirectSummandOfFiniteFree_iff_free` evaluates: the lift is then a fully faithful endofunctor
and the predicate is the plain retract condition downstairs. One universe lift of the index type
remains, since the predicate indexes the finite free module by `ULift.{w} (Fin n)` (the index type
must lie in the ring universe) while the cofan of `IsFiniteFreeRetract` is indexed by `Fin n`
itself; `SheafOfModules.freeFunctor` carries `Equiv.ulift` to an isomorphism between the two. -/
private theorem isFiniteFreeRetract_of_isDirectSummandOfFiniteFree
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} [HasWeakSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] {E : SheafOfModules.{w} R}
    (hE : IsDirectSummandOfFiniteFree R E) : IsFiniteFreeRetract R E := by
  obtain ⟨n, j, r, hjr⟩ := (isDirectSummandOfFiniteFree_iff_free R E).mp hE
  -- The index type of `SheafOfModules.free` must lie in the ring universe `w`, whereas the
  -- cofan of `IsFiniteFreeRetract` is indexed by `Fin n` itself, so the tautological cofan
  -- on `ULift.{w} (Fin n)` is reindexed along `Equiv.ulift`.
  let c0 := SheafOfModules.freeCofan (R := R) (ULift.{w} (Fin n))
  have hc0 : IsColimit c0 := SheafOfModules.isColimitFreeCofan (R := R) (ULift.{w} (Fin n))
  let cf : Cofan fun _ : Fin n => SheafOfModules.unit R :=
    Cofan.mk c0.pt fun i => c0.inj (ULift.up i)
  have hcf : IsColimit cf :=
    Cofan.IsColimit.mk cf (fun t => Cofan.IsColimit.desc hc0 fun i => t.inj i.down)
      (fun t i => by simp [cf])
      (fun t m hm => Cofan.IsColimit.hom_ext hc0 _ _ fun i => by simpa [cf] using hm i.down)
  exact ⟨n, cf, hcf, j, r, hjr⟩

/-- Restriction to a slice preserves finite coproducts of copies of the structure sheaf: it
preserves finite limits, hence finite biproducts. -/
private theorem preservesColimit_overFunctor_unit
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{w}) (V : C) (n : ℕ) :
    PreservesColimit (Discrete.functor fun _ : Fin n => SheafOfModules.unit R)
      (SheafOfModules.overFunctor.{w} R V) := by
  have : PreservesFiniteLimits (SheafOfModules.overFunctor.{w} R V) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits V
  have : PreservesBiproduct (fun _ : Fin n => SheafOfModules.unit R)
      (SheafOfModules.overFunctor.{w} R V) := preservesBiproduct_of_preservesProduct _
  exact preservesCoproduct_of_preservesBiproduct _

/-- Restriction to a slice carries a finite-free retract to a finite-free retract: it
preserves finite limits, hence finite biproducts, hence finite coproducts, and it takes the
structure sheaf to the structure sheaf of the slice on the nose. -/
private theorem IsFiniteFreeRetract.over {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}} {E : SheafOfModules.{w} R}
    (hE : IsFiniteFreeRetract R E) (V : C) : IsFiniteFreeRetract (R.over V) (E.over V) := by
  obtain ⟨n, cf, hcf, j, r, hjr⟩ := hE
  let H := SheafOfModules.overFunctor R V
  have hHcoprod := preservesColimit_overFunctor_unit R V n
  refine ⟨n, H.mapCocone cf, isColimitOfPreserves H hcf, H.map j, H.map r, ?_⟩
  rw [← H.map_comp, hjr, H.map_id]

/-- **Stacks 08FN**, in the form the induction of Stacks 08FP consumes: the modules live on
`C` itself rather than on a slice, the finite-free hypothesis is `IsFiniteFreeRetract`, and
local surjectivity of `p` is a hypothesis rather than a consequence of `Epi p`, because in the
induction `p` is a restriction of an epimorphism and its epimorphy is not available.

The lift is produced one coordinate at a time, as in
`AlgebraicGeometry.RingedSite.exists_coveringSieve_lift`: the composite `q = r ≫ e` out of the
coproduct is `n` sections of `F` over `U`, each lifts through `p` on a covering sieve because
`p` is locally surjective, the intersection of those `n` sieves is covering, and over it the
chosen lifts assemble by the universal property of the coproduct. -/
private theorem exists_coveringSieve_lift_of_locallySurjective
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{w}) (U : C)
    (E F G : SheafOfModules.{w} R) (e : E ⟶ F) (p : G ⟶ F)
    (hE : IsFiniteFreeRetract R E)
    (hLS : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map p.val)) :
    ∃ S : Sieve U, S ∈ J U ∧
      ∀ {V : C} (f : V ⟶ U), S f →
        ∃ l : E.over V ⟶ G.over V, l ≫ p.over V = e.over V := by
  classical
  obtain ⟨n, cf, hcf, j, r, hjr⟩ := hE
  let q : cf.pt ⟶ F := r ≫ e
  let s : Fin n → F.sections := fun k => F.unitHomEquiv (cf.inj k ≫ q)
  let image : Fin n → Sieve U := fun k =>
    Presheaf.imageSieve ((PresheafOfModules.toPresheaf R.obj).map p.val)
      ((s k).val (Opposite.op U))
  have himage : ∀ k : Fin n, image k ∈ J U :=
    fun k => hLS.imageSieve_mem ((s k).val (Opposite.op U))
  let Scov : Sieve U := ⨅ k : Fin n, image k
  have hScov : Scov ∈ J U :=
    Stacks.SheafOfModules.FiniteTypeKernel.iInf_mem J image himage
  refine ⟨Scov, hScov, ?_⟩
  intro V f hf
  have hle : ∀ k : Fin n, Scov ≤ image k := fun k => iInf_le image k
  let a : Fin n → (G.val).obj (Opposite.op V) := fun k =>
    Classical.choose (show image k f from hle k f hf)
  have ha : ∀ k : Fin n,
      p.val.app (Opposite.op V) (a k) =
        F.val.map f.op ((s k).val (Opposite.op U)) :=
    fun k => Classical.choose_spec (show image k f from hle k f hf)
  let Gf := G.over V
  let pF : Gf ⟶ F.over V := p.over V
  let t : Fin n → Gf.sections := fun k =>
    PresheafOfModules.sectionsMk
      (fun Y => G.val.map Y.unop.hom.op (a k)) (by
        intro Y Z g
        change G.val.map (g.unop.left.op) (G.val.map (Y.unop.hom.op) (a k)) =
          G.val.map (Z.unop.hom.op) (a k)
        rw [← G.val.map_comp_apply]
        have hcomp' : Y.unop.hom.op ≫ g.unop.left.op = Z.unop.hom.op := by
          rw [← op_comp, Over.w g.unop]
        exact congrArg
          (fun h : Opposite.op V ⟶ Opposite.op Z.unop.left =>
            G.val.map h (a k)) hcomp')
  let H := SheafOfModules.overFunctor R V
  have hHcoprod := preservesColimit_overFunctor_unit R V n
  let c := H.mapCocone cf
  have hc : IsColimit c := isColimitOfPreserves H hcf
  let η : SheafOfModules.unit (R.over V) ≅ H.obj (SheafOfModules.unit R) := Iso.refl _
  let d : Cofan (fun _ : Fin n => H.obj (SheafOfModules.unit R)) :=
    Cofan.mk Gf (fun i => η.inv ≫ Gf.unitHomEquiv.symm (t i))
  let k : cf.pt.over V ⟶ Gf := hc.desc d
  have hk : k ≫ p.over V = q.over V := by
    apply hc.hom_ext
    intro i
    change c.ι.app i ≫ k ≫ pF = c.ι.app i ≫ q.over V
    apply (cancel_epi η.hom).1
    have hsections : SheafOfModules.sectionsMap pF (t i.as) =
        (F.over V).unitHomEquiv (η.hom ≫ c.ι.app i ≫ q.over V) := by
      apply PresheafOfModules.sections_ext
      intro Y
      change p.val.app (Opposite.op Y.unop.left)
        (G.val.map Y.unop.hom.op (a i.as)) = _
      rw [PresheafOfModules.naturality_apply, ha i.as]
      change F.val.map Y.unop.hom.op
        (F.val.map f.op ((s i.as).val (Opposite.op U))) = _
      have hsection := (s i.as).property Y.unop.hom.op
      rw [← (s i.as).property f.op] at hsection
      have hsection' :
          (ConcreteCategory.hom (F.val.map Y.unop.hom.op))
              ((ConcreteCategory.hom (F.val.map f.op)) ((s i.as).val (Opposite.op U))) =
            (s i.as).val (Opposite.op Y.unop.left) := by
        change (ConcreteCategory.hom ((F.val.presheaf ⋙ forget Ab).map Y.unop.hom.op))
            ((ConcreteCategory.hom ((F.val.presheaf ⋙ forget Ab).map f.op))
              ((s i.as).val (Opposite.op U))) = _ at hsection
        exact hsection
      have hgen : (s i.as).val (Opposite.op Y.unop.left) =
          (η.hom ≫ c.ι.app i ≫ q.over V).val.app Y
            (1 : (R.over V).obj.obj Y) := by
        simp [s, η, c, H, Cofan.inj, SheafOfModules.overFunctor,
          SheafOfModules.pushforward, Functor.mapCocone_ι_app]
        rfl
      exact hsection'.trans hgen
    calc
      η.hom ≫ c.ι.app i ≫ k ≫ pF =
          (F.over V).unitHomEquiv.symm (SheafOfModules.sectionsMap pF (t i.as)) := by
        calc
          η.hom ≫ c.ι.app i ≫ k ≫ pF = η.hom ≫ d.ι.app i ≫ pF :=
            congrArg (fun m => η.hom ≫ m ≫ pF) (hc.fac d i)
          _ = η.hom ≫ (η.inv ≫ Gf.unitHomEquiv.symm (t i.as)) ≫ pF := by rfl
          _ = (F.over V).unitHomEquiv.symm
                (SheafOfModules.sectionsMap pF (t i.as)) := by
            dsimp only [Gf]
            simp only [Category.assoc, Iso.hom_inv_id_assoc]
            exact SheafOfModules.unitHomEquiv_symm_comp (t i.as) pF
      _ = (F.over V).unitHomEquiv.symm
          ((F.over V).unitHomEquiv (η.hom ≫ c.ι.app i ≫ q.over V)) := congrArg _ hsections
      _ = η.hom ≫ c.ι.app i ≫ q.over V := (F.over V).unitHomEquiv.symm_apply_apply _
  refine ⟨j.over V ≫ k, ?_⟩
  rw [Category.assoc, hk]
  change (SheafOfModules.overFunctor R V).map (j ≫ r ≫ e) =
    (SheafOfModules.overFunctor R V).map e
  rw [← Category.assoc, hjr, Category.id_comp]

/-- Evaluation of sheaves of modules at an object preserves zero morphisms. Mathlib has this
for `PresheafOfModules.evaluation`, as an `Additive` instance; `SheafOfModules.evaluation` is a
`def` composing that with the forgetful functor, so the instance does not fire at this
spelling, while the field itself still holds by `rfl`. -/
private instance evaluation_preservesZeroMorphisms {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w}) (X : Cᵒᵖ) :
    (SheafOfModules.evaluation.{0} R X).PreservesZeroMorphisms where
  map_zero _ _ := rfl

section Restriction

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})

/-- Local surjectivity passes to a slice: the image sieve over `W ⟶ V` is the image sieve
over `W`, transported along `Sieve.overEquiv`. -/
private theorem locallySurjective_over {M N : SheafOfModules.{w} R} (p : M ⟶ N)
    (hp : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map p.val)) (V : C) :
    Presheaf.IsLocallySurjective (J.over V)
      ((PresheafOfModules.toPresheaf (R.over V).obj).map (p.over V).val) := by
  constructor
  intro W y
  exact (J.mem_over_iff _).mpr <| J.superset_covering
    (fun T f hf => (Sieve.overEquiv_iff _ _).mpr hf) (hp.imageSieve_mem y)

/-- Restriction to a slice carries a kernel fork to a kernel fork: it preserves finite limits,
which here is checked sectionwise, since a limit of sheaves of modules is detected by the
evaluation functors. -/
private noncomputable def kernel_over {M N : SheafOfModules.{w} R} {d : M ⟶ N}
    (c : KernelFork d) (hc : IsLimit c) (V : C) :
    IsLimit (c.map (SheafOfModules.overFunctor R V)) := by
  apply isLimitOfReflects (SheafOfModules.forget (R.over V))
  apply PresheafOfModules.evaluationJointlyReflectsLimits
  intro W
  change IsLimit ((SheafOfModules.evaluation (R.over V) W).mapCone
    (c.map (SheafOfModules.overFunctor R V)))
  refine (KernelFork.isLimitMapConeEquiv
    (c.map (SheafOfModules.overFunctor R V))
    (SheafOfModules.evaluation (R.over V) W)).symm ?_
  exact c.mapIsLimit hc (SheafOfModules.evaluation R (Opposite.op W.unop.left))

/-- A morphism of the twice-restricted modules `(M|_V)|_W ⟶ (N|_V)|_W` is a morphism of the
once-restricted modules `M|_{W.left} ⟶ N|_{W.left}`: an object of `(C/V)/W` over `T` is an
object of `C/W.left` over `T`, and the two restrictions have the same sections there. -/
private noncomputable def doubleOverHom {M N : SheafOfModules.{w} R}
    (V : C) (W : Over V) (f : (M.over V).over W ⟶ (N.over V).over W) :
    M.over W.left ⟶ N.over W.left where
  val := {
    app := fun T => f.val.app (Opposite.op
      (Over.mk (Over.homMk T.unop.hom (by rfl) :
        Over.mk (T.unop.hom ≫ W.hom) ⟶ W)))
    naturality := by
      intro T T' g
      let A : Over W := Over.mk (Over.homMk T.unop.hom (by rfl) :
        Over.mk (T.unop.hom ≫ W.hom) ⟶ W)
      let B : Over W := Over.mk (Over.homMk T'.unop.hom (by rfl) :
        Over.mk (T'.unop.hom ≫ W.hom) ⟶ W)
      let q : B.left ⟶ A.left := Over.homMk g.unop.left (by
        change g.unop.left ≫ (T.unop.hom ≫ W.hom) = T'.unop.hom ≫ W.hom
        rw [← Category.assoc, Over.w g.unop])
      let q' : B ⟶ A := Over.homMk q (Over.OverMorphism.ext (Over.w g.unop))
      exact f.val.naturality q'.op }

/-- The same reindexing on homotopies: a null-homotopy of the twice-restricted map is a
null-homotopy of the once-restricted map. -/
private noncomputable def doubleOverHomotopy
    {E F : CochainComplex (SheafOfModules.{w} R) ℤ} (α : E ⟶ F)
    (V : C) (W : Over V)
    (h : Homotopy
      (((SheafOfModules.overFunctor (R.over V) W).mapHomologicalComplex _).map
        (((SheafOfModules.overFunctor R V).mapHomologicalComplex _).map α)) 0) :
    Homotopy (((SheafOfModules.overFunctor R W.left).mapHomologicalComplex _).map α) 0 where
  hom i j := doubleOverHom R V W (h.hom i j)
  zero i j hij := by
    rw [h.zero i j hij]
    rfl
  comm i := congrArg (doubleOverHom R V W) (h.comm i)

end Restriction

/-- One step of the induction of Stacks 08FP: if `α` vanishes above degree `n` and `F` has no
cohomology in degree `n`, then on a covering sieve of `U` the restriction of `α` is homotopic
to a map vanishing in degrees `≥ n`.

In degree `n` the map `α` is a cycle, so it factors through the kernel `c` of `F.d n (n+1)`;
the factorisation lifts along `p : F.X (n-1) ⟶ c.pt` locally on `U`, because `E.X n` is a
finite-free retract and `p` is locally surjective. Subtracting the null-homotopic map built
from that lift kills degree `n` and leaves the higher degrees zero. -/
private theorem exists_coveringSieve_kill_top_component
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{w}) (U : C)
    {E F : CochainComplex (SheafOfModules.{w} R) ℤ} (α : E ⟶ F)
    (n : ℤ) (hα : ∀ i : ℤ, n < i → α.f i = 0)
    (hEn : IsFiniteFreeRetract R (E.X n))
    (c : KernelFork (F.d n (n + 1))) (hc : IsLimit c)
    (p : F.X (n - 1) ⟶ c.pt) (hp : p ≫ c.ι = F.d (n - 1) n)
    (hLS : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map p.val)) :
    ∃ S : Sieve U, S ∈ J U ∧
      ∀ {V : C} (f : V ⟶ U), S f →
        ∃ β : (((SheafOfModules.overFunctor R V).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj E ⟶
          ((SheafOfModules.overFunctor R V).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj F),
          Nonempty (Homotopy
            (((SheafOfModules.overFunctor R V).mapHomologicalComplex
              (ComplexShape.up ℤ)).map α) β) ∧ β.f n = 0 ∧
          ∀ i : ℤ, n < i → β.f i = 0 := by
  classical
  have hcycle : α.f n ≫ F.d n (n + 1) = 0 := by
    rw [α.comm n, hα (n + 1) (by omega), comp_zero]
  obtain ⟨e, he⟩ := KernelFork.IsLimit.lift' hc (α.f n) hcycle
  obtain ⟨S, hS, hLift⟩ :=
    exists_coveringSieve_lift_of_locallySurjective R U (E.X n) c.pt (F.X (n - 1))
      e p hEn hLS
  refine ⟨S, hS, ?_⟩
  intro V f hf
  obtain ⟨l, hl⟩ := hLift f hf
  let G := SheafOfModules.overFunctor R V
  let K := G.mapHomologicalComplex (ComplexShape.up ℤ)
  let E' := K.obj E
  let F' := K.obj F
  let α' := K.map α
  let h : ∀ i j, E'.X i ⟶ F'.X j := fun i j => by
    by_cases hi : i = n
    · subst i
      by_cases hj : j = n - 1
      · subst j
        exact l
      · exact 0
    · exact 0
  have hzero : ∀ i j, ¬ (ComplexShape.up ℤ).Rel j i → h i j = 0 := by
    intro i j hij
    by_cases hi : i = n
    · subst i
      by_cases hj : j = n - 1
      · subst j
        exact False.elim (hij (ComplexShape.up_mk (n - 1) n (by omega)))
      · simp [h, hj]
    · simp [h, hi]
  let δ := Homotopy.nullHomotopicMap h
  let β : E' ⟶ F' := α' - δ
  have hcomm : α'.f n = l ≫ G.map (F.d (n - 1) n) := by
    change G.map (α.f n) = _
    calc
      G.map (α.f n) = G.map (e ≫ c.ι) := by rw [he]
      _ = G.map e ≫ G.map (c.ι) := by rw [Functor.map_comp]
      _ = (l ≫ G.map p) ≫ G.map (c.ι) := by rw [show l ≫ G.map p = G.map e from hl]
      _ = l ≫ G.map (F.d (n - 1) n) := by
        simp only [Category.assoc, ← G.map_comp, hp]
  have hβn : β.f n = 0 := by
    change α'.f n - δ.f n = 0
    rw [Homotopy.nullHomotopicMap_f (ComplexShape.up_mk (n - 1) n (by omega))
      (ComplexShape.up_mk n (n + 1) (by omega)) h]
    simp only [add_eq_left, one_ne_zero, ↓reduceDIte, comp_zero, dite_eq_ite, ↓reduceIte,
      zero_add, h]
    rw [show F'.d (n - 1) n = G.map (F.d (n - 1) n) by rfl, hcomm]
    simp only [sub_self]
  have hαβ : Nonempty (Homotopy α' β) := by
    refine ⟨(Homotopy.equivSubZero (f := α') (g := β)).symm ?_⟩
    rw [show α' - β = δ by dsimp [β]; abel]
    exact Homotopy.nullHomotopy h hzero
  have hβtop : ∀ i : ℤ, n < i → β.f i = 0 := by
    intro i hi
    have hαi : α'.f i = 0 := by
      change G.map (α.f i) = 0
      rw [hα i hi, Functor.map_zero]
    have hδi : δ.f i = 0 := by
      rw [Homotopy.nullHomotopicMap_f
        (ComplexShape.up_mk (i - 1) i (by omega))
        (ComplexShape.up_mk i (i + 1) (by omega)) h]
      simp only [show i + 1 ≠ n from by omega, ↓reduceDIte, comp_zero,
        show i ≠ n from by omega, zero_comp, add_zero, h]
    change α'.f i - δ.f i = 0
    rw [hαi, hδi, sub_self]
  exact ⟨β, hαβ, hβn, hβtop⟩

/-- Induction on the number `k` of degrees in which `α` may be nonzero: if `α` vanishes above
`a + k - 1` and `E` vanishes below `a`, then `α` is locally null-homotopic.

Each step kills the top degree by `exists_coveringSieve_kill_top_component` and applies the
induction hypothesis to the restricted map on the slice over each arrow of the resulting
covering sieve; the slices are then compared with single slices of `C` by
`doubleOverHomotopy`. The site is quantified inside the statement because every step replaces
it by a slice of itself. -/
@[sga "6 I 4.1" "special case"]
private theorem exists_coveringSieve_homotopy_zero_bounded (k : ℕ) :
    ∀ {C : Type (max u v)} [Category.{v} C] {J : GrothendieckTopology C}
      (R : Sheaf J RingCat.{w})
      {E F : CochainComplex (SheafOfModules.{w} R) ℤ} (α : E ⟶ F)
      (a : ℤ)
      (_ : ∀ i, IsFiniteFreeRetract R (E.X i))
      (_ : ∀ i, i < a → IsZero (E.X i))
      (_ : ∀ i, a + k - 1 < i → α.f i = 0)
      (c : ∀ i : ℤ, KernelFork (F.d i (i + 1)))
      (_ : ∀ i, IsLimit (c i))
      (p : ∀ i, F.X (i - 1) ⟶ (c i).pt)
      (_ : ∀ i, p i ≫ (c i).ι = F.d (i - 1) i)
      (_ : ∀ i, a ≤ i → Presheaf.IsLocallySurjective J
        ((PresheafOfModules.toPresheaf R.obj).map (p i).val))
      (U : C),
      ∃ S : Sieve U, S ∈ J U ∧
        ∀ {V : C} (f : V ⟶ U), S f → Nonempty (Homotopy
          (((SheafOfModules.overFunctor R V).mapHomologicalComplex _).map α) 0) := by
  induction k with
  | zero =>
    intro C _ J R E F α a _ hE₀ hα c hc p hp hLS U
    have hzero : α = 0 := by
      ext1 i
      by_cases hi : i < a
      · exact (hE₀ i hi).eq_of_src _ _
      · exact hα i (by simp only [Nat.cast_zero]; omega)
    refine ⟨⊤, J.top_mem U, ?_⟩
    intro V f hf
    exact ⟨Homotopy.ofEq (by rw [hzero, Functor.map_zero])⟩
  | succ k ih =>
    intro C _ J R E F α a hE hE₀ hα c hc p hp hLS U
    let n : ℤ := a + k
    obtain ⟨S, hS, hkill⟩ := exists_coveringSieve_kill_top_component R U α n
      (fun i hi => hα i (by dsimp [n] at hi; push_cast; omega)) (hE n)
      (c n) (hc n) (p n) (hp n) (hLS n (by dsimp [n]; omega))
    apply exists_coveringSieve_refinement S hS
    intro V f hf
    obtain ⟨β, ⟨hαβ⟩, hβn, hβtop⟩ := hkill f hf
    let G := SheafOfModules.overFunctor R V
    let F' := (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj F
    have hβ : ∀ i, a + k - 1 < i → β.f i = 0 := by
      intro i hi
      by_cases hin : i = n
      · subst i; exact hβn
      · exact hβtop i (by dsimp [n] at *; omega)
    let c' : ∀ i : ℤ, KernelFork (F'.d i (i + 1)) := fun i => (c i).map G
    have hc' : ∀ i, IsLimit (c' i) := fun i => kernel_over R (c i) (hc i) V
    let p' : ∀ i, F'.X (i - 1) ⟶ (c' i).pt := fun i => G.map (p i)
    have hp' : ∀ i, p' i ≫ (c' i).ι = F'.d (i - 1) i := by
      intro i
      change G.map (p i) ≫ G.map (c i).ι = G.map (F.d (i - 1) i)
      rw [← G.map_comp, hp]
    obtain ⟨T, hT, hnull⟩ := ih (R.over V) β a
      (fun i => (hE i).over V)
      (fun i hi => G.map_isZero (hE₀ i hi)) hβ c' hc' p' hp'
      (fun i hi => locallySurjective_over R (p i) (hLS i hi) V) (Over.mk (𝟙 V))
    refine ⟨(Sieve.overEquiv (Over.mk (𝟙 V))) T, (J.mem_over_iff T).mp hT, ?_⟩
    intro W g hg
    obtain ⟨hβzero⟩ := hnull (V := Over.mk (g ≫ 𝟙 V)) (Over.homMk g (by rfl))
      ((Sieve.overEquiv_iff T g).mp hg)
    exact ⟨doubleOverHomotopy R α V (Over.mk (g ≫ 𝟙 V))
      ((SheafOfModules.overFunctor (R.over V) (Over.mk (g ≫ 𝟙 V))).mapHomotopy hαβ |>.trans
        hβzero)⟩

variable (X : RingedSite.{u, v, w}) (U : X.C)
variable [HasSheafify (X.J.over U) AddCommGrpCat.{w}]
variable [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {E F : CochainComplex
  (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) ℤ}
variable (α : E ⟶ F)

/-- A strictly perfect complex has a degree below which it vanishes. -/
private theorem exists_integer_lower_bound_of_finite_support
    (hE : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) E) :
    ∃ a : ℤ, ∀ i : ℤ, i < a → IsZero (E.X i) := by
  obtain ⟨a, ha⟩ := hE.bounded.bddBelow
  exact ⟨a, fun i hi => by_contra fun hnot => (ha hnot).not_gt hi⟩

/-- A strictly perfect complex has a degree above which it vanishes. -/
private theorem exists_integer_upper_bound_of_finite_support
    (hE : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) E) :
    ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (E.X i) := by
  obtain ⟨b, hb⟩ := hE.bounded.bddAbove
  exact ⟨b, fun i hi => by_contra fun hnot => (hb hnot).not_gt hi⟩

/-- Stacks 08FP (2). The cohomology hypothesis supplies, in each degree `i ≥ a`, an
epimorphism from `F.X (i-1)` onto the cycles in degree `i`; local surjectivity of those
epimorphisms is what the induction consumes. -/
private theorem local_nullhomotopy (a : ℤ)
    (hE : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) E)
    (hE₀ : ∀ i : ℤ, i < a → IsZero (E.X i))
    (hF : ∀ i : ℤ, a ≤ i → IsZero (F.homology i)) :
    ∃ S : Sieve U, S ∈ X.J U ∧
      ∀ {V : X.C} (f : V ⟶ U), S f →
        Nonempty (Homotopy
          (((SheafOfModules.overFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)
            (Over.mk f)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map α) 0) := by
  obtain ⟨b, hb⟩ := exists_integer_upper_bound_of_finite_support X U hE
  let k := (b - a + 1).toNat
  have hα : ∀ i : ℤ, a + k - 1 < i → α.f i = 0 := by
    intro i hi
    exact (hb i (by dsimp [k] at hi; omega)).eq_of_src _ _
  let c : ∀ i : ℤ, KernelFork (F.d i (i + 1)) :=
    fun i => KernelFork.ofι (F.iCycles i) (F.iCycles_d i (i + 1))
  have hc : ∀ i, IsLimit (c i) := fun i => F.cyclesIsKernel i (i + 1) (by simp)
  let p : ∀ i : ℤ, F.X (i - 1) ⟶ (c i).pt := fun i => F.toCycles (i - 1) i
  have hp : ∀ i, p i ≫ (c i).ι = F.d (i - 1) i := fun i => F.toCycles_i _ _
  have hLS : ∀ i, a ≤ i → Presheaf.IsLocallySurjective (X.J.over U)
      ((PresheafOfModules.toPresheaf ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).obj).map
        (p i).val) := by
    intro i hi
    have : Epi (p i) := Preadditive.epi_of_isZero_cokernel' _
      (F.homologyIsCokernel (i := i - 1) (j := i) (by simp)) (hF i hi)
    exact Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi (p i)
  obtain ⟨S, hS, hnull⟩ := exists_coveringSieve_homotopy_zero_bounded k
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) α a
    (fun i => isFiniteFreeRetract_of_isDirectSummandOfFiniteFree (hE.termDirectSummand i))
    hE₀ hα c hc p hp hLS (Over.mk (𝟙 U))
  refine ⟨Sieve.overEquiv _ S, (X.J.mem_over_iff S).mp hS, ?_⟩
  intro V f hf
  have hh := hnull (V := Over.mk (f ≫ 𝟙 U)) (Over.homMk f (by rfl))
    ((Sieve.overEquiv_iff S f).mp hf)
  exact (congrArg Over.mk (Category.comp_id f) : Over.mk (f ≫ 𝟙 U) = Over.mk f) ▸ hh

/-- **Stacks 08FP (1)**, with the site, its morphisms and the sections of the structure
sheaf at independent universes. A map from a strictly perfect complex of `O|_U`-modules to an
acyclic complex is null-homotopic after restriction along every arrow of a covering sieve. -/
@[sga "6 I 4.1" "special case"]
theorem exists_coveringSieve_homotopy_zero_of_acyclic_general
    (hE : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) E)
    (hF : F.Acyclic) :
    ∃ S : Sieve U, S ∈ X.J U ∧
      ∀ {V : X.C} (f : V ⟶ U), S f →
        Nonempty (Homotopy
          (((SheafOfModules.overFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)
            (Over.mk f)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map α) 0) := by
  have hhom (i : ℤ) : F.HasHomology i := (hF i).hasHomology
  obtain ⟨a, hEa⟩ := exists_integer_lower_bound_of_finite_support X U hE
  exact local_nullhomotopy X U α a hE hEa (fun i _ => (hF i).isZero_homology)

/-- **Stacks 08FP (2)**, with the site, its morphisms and the sections of the structure sheaf
at independent universes. A map from a strictly perfect complex of `O|_U`-modules supported in
degrees `≥ a` into a complex with vanishing cohomology there is locally null-homotopic. -/
alias exists_coveringSieve_homotopy_zero_of_isZero_homology_general := local_nullhomotopy

section DiagonalUniverses

variable (X : RingedSite.{u, v, 0}) (U : X.C)
variable [HasSheafify (X.J.over U) AddCommGrpCat.{0}]
variable [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{0}]
variable {E F : CochainComplex
  (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) ℤ}
variable (α : E ⟶ F)

/-- **Stacks 08FP (1).** A map from a strictly perfect complex of `O|_U`-modules to an acyclic
complex is null-homotopic after restriction along every arrow of a covering sieve of `U`. -/
@[stacks 08FP "part (1)", sga "6 I 4.1"]
theorem exists_coveringSieve_homotopy_zero_of_acyclic
    (hE : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) E)
    (hF : F.Acyclic) :
    ∃ S : Sieve U, S ∈ X.J U ∧
      ∀ {V : X.C} (f : V ⟶ U), S f →
        Nonempty (Homotopy
          (((SheafOfModules.overFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)
            (Over.mk f)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map α) 0) := by
  exact exists_coveringSieve_homotopy_zero_of_acyclic_general X U α hE hF

/-- **Stacks 08FP (2).** A map from a strictly perfect complex of `O|_U`-modules supported in
degrees `≥ a` is null-homotopic after restriction along every arrow of a covering sieve of `U`,
provided the target has vanishing cohomology in those degrees. -/
@[stacks 08FP "part (2)", sga "6 I 4.1"]
theorem exists_coveringSieve_homotopy_zero_of_isZero_homology (a : ℤ)
    (hE : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) E)
    (hE₀ : ∀ i : ℤ, i < a → IsZero (E.X i))
    (hF : ∀ i : ℤ, a ≤ i → IsZero (F.homology i)) :
    ∃ S : Sieve U, S ∈ X.J U ∧
      ∀ {V : X.C} (f : V ⟶ U), S f →
        Nonempty (Homotopy
          (((SheafOfModules.overFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)
            (Over.mk f)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map α) 0) := local_nullhomotopy X U α a hE hE₀ hF

end DiagonalUniverses

end AlgebraicGeometry.RingedSite

end
