module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.FiniteFreeSummands
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.LocalLiftingOverASlice
public import StacksCore.Tactic.StacksAttribute

/-!
# Local null-homotopy of a map out of a strictly perfect complex

Let `α : E ⟶ F` be a map of complexes of `O_X`-modules on a ringed space with `E` strictly
perfect. If the cohomology of `F` vanishes in every degree where `E` can be nonzero -- in
particular if `F` is acyclic -- then `α` is null-homotopic after restricting to a small enough
open neighbourhood of any point.

## Main definitions

* `Stacks.Cohomology.LocalNullHomotopy.HasNullHomotopyAbove` is the invariant of the induction:
  over the open set `U`
  there is a null-homotopic map `ψ` agreeing with the restriction of `α` in every degree above
  a given one. Carrying a *map together with a null-homotopy of it*, rather than the degreewise
  homotopy data itself, is what lets the invariant be transported to a smaller open set with
  `SheafOfModules.overFunctorMapHomotopy`; the degreewise data would have to be conjugated by
  hand in each degree.

## Main results

* `Stacks.Cohomology.LocalNullHomotopy.exists_local_homotopy_zero_of_acyclic` treats an acyclic
  target.
* `Stacks.Cohomology.LocalNullHomotopy.exists_local_homotopy_zero_of_isZero_homology` treats
  vanishing cohomology above
  a lower bound for the source.
* `Stacks.Cohomology.LocalNullHomotopy.exists_local_factor_d` is the inductive step: a cocycle out
  of a retract of a
  finite free sheaf of modules, in a degree where the target complex is exact, is a coboundary
  along the arrows of a covering sieve. It is stated over an arbitrary sheaf of rings on an
  arbitrary site, since in the induction it is applied over the *restricted* sheaf of rings.
* `Stacks.Cohomology.LocalNullHomotopy.exactAt_map_overFunctor` and
  `Stacks.Cohomology.LocalNullHomotopy.exists_retract_free_of_isDirectSummand` move the two
    hypotheses of Tag 08C7, which
  are about the unrestricted complexes, to the slice where the inductive step is applied.
* `StrictlyPerfect.finiteFreeIsoFree`: `O_X^{\oplus n}` is the free sheaf of modules on
  `ULift (Fin n)`.

## Implementation notes

The proof is the Stacks induction. Let `b` be a degree above which `E` vanishes and induct on
`k` over the statement that `α` has a null-homotopic comparison map, on some neighbourhood of
the given point, in every degree above `b - k`. The base case `k = 0` takes the zero map. At the
step, in degree `m = b - k`, the obstruction `β = α^m - ψ^m` satisfies `β ≫ d = 0`, so the
vanishing of `H^m(F)` factors it through the epimorphism `F^{m-1} ↠ ker d` and
`Stacks.StrictlyPerfect.LocalLiftingOverSlice.exists_local_lift` lifts the factorisation after
  shrinking the open set. Taking
`k` with `b - k < a` gives agreement in every degree, since `E` vanishes below `a`.

Restriction to the slice over `U` is `SheafOfModules.overFunctor`, extended to complexes by
`Functor.mapHomologicalComplex`; this is additive by `SheafOfModules.overFunctor_additive`, so
no hand-rolled `PreservesZeroMorphisms` instance is needed. Shrinking from `U` to `V` uses
`SheafOfModules.overFunctorMapHomologicalComplex`, the identification of
`overFunctor R U ⋙ overMap R g` with `overFunctor R V`.

The space, ring and module universes all coincide here, which is a restatement relative to the
source: `StrictlyPerfect.LocalLifting.exists_local_lift` and its slice form
  `Stacks.StrictlyPerfect.LocalLiftingOverSlice.exists_local_lift`
are available only when the module universe is the ring universe, because both the free sheaf of
modules and the characterisation of epimorphisms as locally surjective maps are, and the
sheafification hypotheses they need hold automatically only when the site universe matches too.

## References

* [Stacks Project, Tag 08C7](https://stacks.math.columbia.edu/tag/08C7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace StrictlyPerfect

open _root_.SheafOfModules

universe u

/-- **The finite free module of rank `n` is a free sheaf of modules.** `finiteFree X n` is the
biproduct of `n` copies of the structure sheaf and `SheafOfModules.free I` is the coproduct of
`I` copies of the unit; the two agree for `I = ULift (Fin n)`. -/
noncomputable def finiteFreeIsoFree (X : AlgebraicGeometry.RingedSpace.{u, u}) (n : ℕ) :
    finiteFree X n ≅ free (R := structureSheafOfRings X) (ULift.{u} (Fin n)) := by
  change (⨁ fun _ : Fin n => unit (structureSheafOfRings X)) ≅
    ∐ (fun _ : ULift.{u} (Fin n) => unit (structureSheafOfRings X))
  exact (biproduct.whiskerEquiv
    (g := fun _ : ULift.{u} (Fin n) => unit (structureSheafOfRings X))
    Equiv.ulift.symm (fun _ => Iso.refl _)).trans (biproduct.isoCoproduct _)

end StrictlyPerfect

namespace Stacks.Cohomology.LocalNullHomotopy

universe v₁ u₁ u

open _root_.SheafOfModules _root_.StrictlyPerfect

section Site

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [HasPullbacks C] {R : Sheaf J RingCat.{u}}
  [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasPullbacks C] in
/-- **Restriction to a slice preserves exactness in a degree.** Restriction to the slice over
`U` preserves homology (`SheafOfModules.overFunctor_preservesHomology`), and the short complex
in degree `m` of the restricted complex is the restriction of the short complex in degree `m`;
so exactness in degree `m` is preserved. -/
lemma exactAt_map_overFunctor [HasBinaryProducts C] [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] (U : C)
    {G : CochainComplex (SheafOfModules.{u} R) ℤ} (m : ℤ) (hG : G.ExactAt m) :
    (((overFunctor.{u} R U).mapHomologicalComplex (ComplexShape.up ℤ)).obj G).ExactAt m :=
  hG.map (overFunctor.{u} R U)

/-- **The inductive step of Tag 08C7.** Let `A` be a retract of a free sheaf of modules on a
finite type, over the slice sheaf of rings `R.over Y`, and let `G` be a complex which is exact
in degree `m`. Then a morphism `β : A ⟶ G.X m` killed by the differential is, along the arrows
of a covering sieve of `Y`, the image under the differential of a morphism
`A ⟶ G.X (m - 1)`.

The hypothesis of exactness makes `G.X (m - 1) ⟶ ker (G.d m (m + 1))` an epimorphism
(`CategoryTheory.ShortComplex.Exact.epi_toCycles`), `β` factors through that kernel because it
is a cocycle, and `Stacks.StrictlyPerfect.LocalLiftingOverSlice.exists_local_lift` lifts the
  factorisation through the
epimorphism after passing to a covering sieve. -/
@[sga "6 I 1.3" "more general"]
theorem exists_local_factor_d {Y : C} {A : SheafOfModules.{u} (R.over Y)}
    {G : CochainComplex (SheafOfModules.{u} (R.over Y)) ℤ}
    {I : Type u} [Finite I] (ρ : Retract A (free I))
    (m : ℤ) (hG : G.ExactAt m) (β : A ⟶ G.X m) (hβ : β ≫ G.d m (m + 1) = 0) :
    ∃ S : Sieve Y, S ∈ J Y ∧ ∀ ⦃V : C⦄ (g : V ⟶ Y), S g →
      ∃ h : (overMap.{u} R g).obj A ⟶ (overMap.{u} R g).obj (G.X (m - 1)),
        h ≫ (overMap.{u} R g).map (G.d (m - 1) m) = (overMap.{u} R g).map β := by
  rw [G.exactAt_iff' (m - 1) m (m + 1) (by simp) (by simp)] at hG
  have hepi : Epi (G.sc' (m - 1) m (m + 1)).toCycles := hG.epi_toCycles
  obtain ⟨S, hS, hlift⟩ := Stacks.StrictlyPerfect.LocalLiftingOverSlice.exists_local_lift
    ((G.sc' (m - 1) m (m + 1)).liftCycles β hβ)
    (G.sc' (m - 1) m (m + 1)).toCycles ρ
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨l, hl⟩ := hlift g hg
  have hd : G.d (m - 1) m =
      (G.sc' (m - 1) m (m + 1)).toCycles ≫ (G.sc' (m - 1) m (m + 1)).iCycles := by
    simp
  refine ⟨l, ?_⟩
  rw [hd]
  erw [Functor.map_comp, ← Category.assoc, hl, ← Functor.map_comp, ShortComplex.liftCycles_i]

end Site

section RingedSpace

variable {X : AlgebraicGeometry.RingedSpace.{u, u}}

/-- **A direct summand of a finite free module restricts to a retract of a free sheaf of
modules.** The restriction functor carries the retract exhibiting `E` as a summand of
`O_X^{⊕ n}` to a retract of the restriction of `O_X^{⊕ n}`, which is the free sheaf of modules
on `ULift (Fin n)` over the restricted sheaf of rings by `StrictlyPerfect.finiteFreeIsoFree`
and `SheafOfModules.overFunctorFreeIso`. -/
lemma exists_retract_free_of_isDirectSummand (E : OXMod.{u, u} X)
    (hE : IsDirectSummandOfFiniteFree E) (U : Opens X.carrier) :
    ∃ n : ℕ, Nonempty (Retract ((overFunctor.{u} (structureSheafOfRings X) U).obj E)
      (free (R := (structureSheafOfRings X).over U) (ULift.{u} (Fin n)))) := by
  obtain ⟨n, ⟨ρ⟩⟩ := (isDirectSummandOfFiniteFree_iff_retract E).mp hE
  exact ⟨n, ⟨(ρ.map (overFunctor.{u} (structureSheafOfRings X) U)).trans
    (((overFunctor.{u} (structureSheafOfRings X) U).mapIso (finiteFreeIsoFree X n)).trans
      (overFunctorFreeIso (structureSheafOfRings X) U (ULift.{u} (Fin n))).symm).retract⟩⟩

/-- Restriction of complexes of `O_X`-modules to the slice over an open set `U`. -/
noncomputable abbrev restr (X : AlgebraicGeometry.RingedSpace.{u, u}) (U : Opens X.carrier) :
    CochainComplex (OXMod.{u, u} X) ℤ ⥤
      CochainComplex (SheafOfModules.{u} ((structureSheafOfRings X).over U)) ℤ :=
  (overFunctor.{u} (structureSheafOfRings X) U).mapHomologicalComplex (ComplexShape.up ℤ)

/-- **The invariant of the induction proving Tag 08C7.** Over the open set `U` there is a
null-homotopic map `ψ` between the restrictions of `E` and `F` which agrees with the restriction
of `α` in every degree above `n`. -/
def HasNullHomotopyAbove {E F : CochainComplex (OXMod.{u, u} X) ℤ} (α : E ⟶ F)
    (U : Opens X.carrier) (n : ℤ) : Prop :=
  ∃ ψ : (restr X U).obj E ⟶ (restr X U).obj F, Nonempty (Homotopy ψ 0) ∧
    ∀ i : ℤ, n < i → ((restr X U).map α).f i = ψ.f i

variable {E F : CochainComplex (OXMod.{u, u} X) ℤ} (α : E ⟶ F)

/-- Any two maps out of the restriction of a zero module to a slice are equal. -/
private theorem overFunctor_hom_ext_of_isZero {Z : OXMod.{u, u} X} (hZ : IsZero Z)
    (U : Opens X.carrier) {W : SheafOfModules.{u} ((structureSheafOfRings X).over U)}
    (f g : (overFunctor.{u} (structureSheafOfRings X) U).obj Z ⟶ W) : f = g :=
  ((overFunctor.{u} (structureSheafOfRings X) U).map_isZero hZ).eq_of_src _ _

/-- **The shrinking step.** Suppose `α` admits a null-homotopic comparison map over `U` in
every degree above `m`. Then, after shrinking `U` to a smaller neighbourhood `V` of `x`, it
admits one in every degree above `m - 1`.

If `E.X m` vanishes there is nothing to do and `V = U` works. Otherwise `a ≤ m`, so `F` has
vanishing cohomology in degree `m`; the obstruction `β = α^m - ψ^m` is a cocycle because `α` and
`ψ` are both chain maps and they already agree in degree `m + 1`, so
`exists_local_factor_d` writes `β` as `h ≫ d` along a covering sieve of `U`, and `x`
lies in one of the open sets of that sieve. Transporting `ψ` to `V` with
`SheafOfModules.overFunctorMapHomologicalComplex` and adding the null-homotopic map built from
the single morphism `h` gives the new comparison map; the added map vanishes in all degrees
above `m` and contributes exactly `β` in degree `m`. -/
lemma step (a : ℤ) (hE : ∀ i : ℤ, IsDirectSummandOfFiniteFree (E.X i))
    (hE₀ : ∀ i : ℤ, i < a → IsZero (E.X i))
    (hF : ∀ i : ℤ, a ≤ i → IsZero (F.homology i))
    (x : X.carrier) (m : ℤ) {U : Opens X.carrier} (hxU : x ∈ U)
    (hU : HasNullHomotopyAbove α U m) :
    ∃ V : Opens X.carrier, x ∈ V ∧ HasNullHomotopyAbove α V (m - 1) := by
  obtain ⟨ψ, ⟨H⟩, hag⟩ := hU
  by_cases hm : m < a
  · refine ⟨U, hxU, ψ, ⟨H⟩, fun i hi => ?_⟩
    rcases eq_or_lt_of_le (show m ≤ i by omega) with heq | hlt
    · subst heq
      exact overFunctor_hom_ext_of_isZero (hE₀ m hm) U _ _
    · exact hag i hlt
  rw [not_lt] at hm
  obtain ⟨n, ⟨ρ⟩⟩ := exists_retract_free_of_isDirectSummand (E.X m) (hE m) U
  have hGex : ((restr X U).obj F).ExactAt m := by
    refine exactAt_map_overFunctor U m ?_
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact hF m hm
  have hβ : (((restr X U).map α).f m - ψ.f m) ≫ ((restr X U).obj F).d m (m + 1) = 0 := by
    rw [Preadditive.sub_comp, ((restr X U).map α).comm m (m + 1), ψ.comm m (m + 1),
      ← Preadditive.comp_sub, hag (m + 1) (by omega), sub_self, comp_zero]
  obtain ⟨S, hS, hlift⟩ := exists_local_factor_d ρ m hGex _ hβ
  obtain ⟨V, g, hSg, hxV⟩ := hS x hxU
  obtain ⟨h', hh'⟩ := hlift g hSg
  refine ⟨V, hxV, ?_⟩
  let Ψ := (overMap.{u} (structureSheafOfRings X) g).mapHomologicalComplex (ComplexShape.up ℤ)
  let e := overFunctorMapHomologicalComplex.{u} (structureSheafOfRings X) g (ComplexShape.up ℤ)
  have hnat : ∀ (A B : CochainComplex (OXMod.{u, u} X) ℤ) (φ : A ⟶ B),
      (restr X V).map φ = (e.inv.app A ≫ Ψ.map ((restr X U).map φ)) ≫ e.hom.app B := by
    intro A B φ
    have h := e.hom.naturality φ
    dsimp at h
    rw [Category.assoc, h, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  set ψV : (restr X V).obj E ⟶ (restr X V).obj F :=
    (e.inv.app E ≫ Ψ.map ψ) ≫ e.hom.app F with hψV
  have HV : Homotopy ψV 0 := by
    refine ((((overMap.{u} (structureSheafOfRings X) g).mapHomotopy H).compLeft
        (e.inv.app E)).compRight (e.hom.app F)).trans (Homotopy.ofEq ?_)
    simp
  have key : ∀ i : ℤ, ((restr X V).map α).f i - ψV.f i =
      (e.inv.app E).f i ≫ ((Ψ.map ((restr X U).map α)).f i - (Ψ.map ψ).f i) ≫
        (e.hom.app F).f i := by
    intro i
    rw [hnat E F α, hψV]
    simp only [HomologicalComplex.comp_f, Preadditive.comp_sub, Preadditive.sub_comp,
      Category.assoc]
  have hsub : (Ψ.map ((restr X U).map α)).f m - (Ψ.map ψ).f m =
      (overMap.{u} (structureSheafOfRings X) g).map (((restr X U).map α).f m - ψ.f m) :=
    ((overMap.{u} (structureSheafOfRings X) g).map_sub).symm
  have hh'' : ((e.inv.app E).f m ≫ h' ≫ (e.hom.app F).f (m - 1)) ≫
      ((restr X V).obj F).d (m - 1) m = ((restr X V).map α).f m - ψV.f m := by
    rw [key m, hsub, ← hh']
    simp only [Category.assoc]
    rw [(e.hom.app F).comm (m - 1) m]
    rfl
  let single : ∀ i j : ℤ, ((restr X V).obj E).X i ⟶ ((restr X V).obj F).X j := fun i j =>
    if hi : i = m then
      if hj : j = m - 1 then
        (HomologicalComplex.XIsoOfEq _ hi).hom ≫
          ((e.inv.app E).f m ≫ h' ≫ (e.hom.app F).f (m - 1)) ≫
            (HomologicalComplex.XIsoOfEq _ hj).inv
      else 0
    else 0
  have hmid : single m (m - 1) = (e.inv.app E).f m ≫ h' ≫ (e.hom.app F).f (m - 1) := by
    simp [single]
  have hzero : ∀ i j : ℤ, ¬ (ComplexShape.up ℤ).Rel j i → single i j = 0 := by
    intro i j hij
    by_cases hi : i = m
    · by_cases hj : j = m - 1
      · exfalso
        apply hij
        simp only [ComplexShape.up_Rel]
        omega
      · simp [single, hi, hj]
    · simp [single, hi]
  have hnext : ∀ i : ℤ, m - 1 < i → single (i + 1) i = 0 := by
    intro i hi
    have hne : i + 1 ≠ m := by omega
    simp [single, hne]
  have hprev : ∀ i : ℤ, m < i → single i (i - 1) = 0 := by
    intro i hi
    have hne : i ≠ m := by omega
    simp [single, hne]
  have hδ : ∀ i : ℤ, (Homotopy.nullHomotopicMap single).f i =
      ((restr X V).obj E).d i (i + 1) ≫ single (i + 1) i +
        single i (i - 1) ≫ ((restr X V).obj F).d (i - 1) i := by
    intro i
    have hr1 : (ComplexShape.up ℤ).Rel i (i + 1) := by simp only [ComplexShape.up_Rel]
    have hr2 : (ComplexShape.up ℤ).Rel (i - 1) i := by
      simp only [ComplexShape.up_Rel]
      omega
    change dNext i single + prevD i single = _
    rw [dNext_eq single hr1, prevD_eq single hr2]
  refine ⟨ψV + Homotopy.nullHomotopicMap single,
    ⟨(HV.add (Homotopy.nullHomotopy single hzero)).trans (Homotopy.ofEq (add_zero 0))⟩, ?_⟩
  intro i hi
  rcases eq_or_lt_of_le (show m ≤ i by omega) with heq | hlt
  · rw [← heq, HomologicalComplex.add_f_apply, hδ m, hnext m (by omega), hmid, comp_zero,
      zero_add, hh'']
    abel
  · rw [HomologicalComplex.add_f_apply, hδ i, hnext i (by omega), hprev i hlt, zero_comp,
      comp_zero, add_zero, add_zero]
    have hfi : (Ψ.map ((restr X U).map α)).f i = (Ψ.map ψ).f i :=
      congrArg (overMap.{u} (structureSheafOfRings X) g).map (hag i hlt)
    have hk := key i
    rw [hfi, sub_self, zero_comp, comp_zero] at hk
    exact sub_eq_zero.mp hk

/-- **The base of the induction.** Above a degree beyond which `E` vanishes, the zero map is a
null-homotopic comparison map for `α`: both it and `α` are morphisms out of a zero object. -/
lemma base {b : ℤ} (hb : ∀ i : ℤ, b < i → IsZero (E.X i)) (U : Opens X.carrier) :
    HasNullHomotopyAbove α U b :=
  ⟨0, ⟨Homotopy.refl 0⟩, fun i hi => overFunctor_hom_ext_of_isZero (hb i hi) U _ _⟩

/-- **The induction.** Iterating `Stacks.Cohomology.LocalNullHomotopy.step` `k` times produces a
  neighbourhood of `x`
over which `α` has a null-homotopic comparison map in every degree above `b - k`. -/
lemma main (a b : ℤ) (hE : ∀ i : ℤ, IsDirectSummandOfFiniteFree (E.X i))
    (hE₀ : ∀ i : ℤ, i < a → IsZero (E.X i))
    (hb : ∀ i : ℤ, b < i → IsZero (E.X i))
    (hF : ∀ i : ℤ, a ≤ i → IsZero (F.homology i)) (x : X.carrier) (k : ℕ) :
    ∃ U : Opens X.carrier, x ∈ U ∧ HasNullHomotopyAbove α U (b - k) := by
  induction k with
  | zero => exact ⟨⊤, trivial, by simpa using base α hb ⊤⟩
  | succ k ih =>
      obtain ⟨U, hxU, hU⟩ := ih
      obtain ⟨V, hxV, hV⟩ := step α a hE hE₀ hF x (b - k) hxU hU
      refine ⟨V, hxV, ?_⟩
      rw [show b - ((k + 1 : ℕ) : ℤ) = b - (k : ℤ) - 1 by push_cast; ring]
      exact hV

/-- A strictly perfect complex vanishes in all large degrees. -/
lemma exists_upper_bound (hE : IsStrictlyPerfect E) : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (E.X i) := by
  obtain ⟨b, hb⟩ := hE.bounded.bddAbove
  exact ⟨b, fun i hi => not_not.mp fun h => absurd (hb h) (by omega)⟩

/-- A strictly perfect complex vanishes in all small degrees. -/
lemma exists_lower_bound (hE : IsStrictlyPerfect E) : ∃ a : ℤ, ∀ i : ℤ, i < a → IsZero (E.X i) := by
  obtain ⟨a, ha⟩ := hE.bounded.bddBelow
  exact ⟨a, fun i hi => not_not.mp fun h => absurd (ha h) (by omega)⟩

/-- A map from a strictly perfect complex concentrated in degrees at least
`a` is locally null-homotopic if the target's cohomology vanishes in those
degrees.

Choosing `k` with `b - k < a`, where `E` vanishes above `b`, the induction
  `Stacks.Cohomology.LocalNullHomotopy.main`
produces a comparison map agreeing with `α` in every degree above `b - k`; in the remaining
degrees `E` vanishes, so the two agree there too and `α` is itself null-homotopic over that
neighbourhood. -/
@[sga "6 I 4.1" "special case"]
theorem exists_local_homotopy_zero_of_isZero_homology (a : ℤ)
    (hE : IsStrictlyPerfect E) (hE₀ : ∀ i : ℤ, i < a → IsZero (E.X i))
    (hF : ∀ i : ℤ, a ≤ i → IsZero (F.homology i)) :
    ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      Nonempty (Homotopy
        (((SheafOfModules.overFunctor (structureSheafOfRings X) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).map α) 0) := by
  intro x
  obtain ⟨b, hb⟩ := exists_upper_bound hE
  have hkey : b - (((b - a).toNat + 1 : ℕ) : ℤ) < a := by
    have h := Int.self_le_toNat (b - a)
    push_cast
    omega
  obtain ⟨U, hxU, ψ, ⟨H⟩, hag⟩ :=
    main α a b hE.directSummand hE₀ hb hF x ((b - a).toNat + 1)
  refine ⟨U, hxU, ⟨?_⟩⟩
  have heq : (restr X U).map α = ψ := by
    refine HomologicalComplex.hom_ext _ _ fun i => ?_
    by_cases hi : b - (((b - a).toNat + 1 : ℕ) : ℤ) < i
    · exact hag i hi
    · exact overFunctor_hom_ext_of_isZero (hE₀ i (by omega)) U _ _
  exact (Homotopy.ofEq heq).trans H

/-- A map from a strictly perfect complex to an acyclic complex is locally
null-homotopic.

A strictly perfect complex vanishes in all small degrees, which supplies the lower bound `a`
needed by `Stacks.Cohomology.LocalNullHomotopy.exists_local_homotopy_zero_of_isZero_homology`; an
  acyclic complex has
vanishing cohomology in every degree. -/
@[sga "6 I 4.1" "special case"]
theorem exists_local_homotopy_zero_of_acyclic
    (hE : IsStrictlyPerfect E) (hF : F.Acyclic) :
    ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      Nonempty (Homotopy
        (((SheafOfModules.overFunctor (structureSheafOfRings X) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).map α) 0) := by
  obtain ⟨a, ha⟩ := exists_lower_bound hE
  exact exists_local_homotopy_zero_of_isZero_homology α a hE ha
    fun i _ => (hF i).isZero_homology

end RingedSpace

end Stacks.Cohomology.LocalNullHomotopy

end
