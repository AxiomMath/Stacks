module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalSectionSmul
public import StacksFrontier.Topology.Sheaves.Cohomology.InverseSystems.TorsionFreeAndDivisibleSystems

/-!
# The kernel of a projection out of the limit of terminal sections

Let `R` be a sheaf of commutative rings on a small site with a terminal object `T`, let a
scalar `f` act on sheaves of `R`-modules through a ring map `A → R(T)`, and let
`… → 𝓕₂ → 𝓕₁` be an inverse system of `R`-modules satisfying condition (1) of Stacks 0H39
for multiplication by `f`. Write `F` for the induced inverse system of `A`-modules of
sections over `T`. Then an element of `lim F` dies in the term `𝓕ₙ₊₁` exactly when it is
`f^(n+1)` times another element of the limit.

Condition (1) presents multiplication by `f` on `𝓕ₙ₊₁` as `𝓕ₙ₊₁ → 𝓕ₙ → 𝓕ₙ₊₁` with mono
second map, and the sequence `0 → 𝓕ₙ → 𝓕ₙ₊₁ → 𝓕₁ → 0` is short exact. Sections over `T` are
a left exact functor, so an element of `lim F` killed in `𝓕₁` lifts through every `𝓕ₙ → 𝓕ₙ₊₁`,
and the lifts are unique, hence compatible; the lifted family is an element of the limit
whose `f`-multiple is the original. Iterating gives the formula for every `n`.

## Main results

* `Stacks.Modules.range_pow_eq_ker_limitProjection_terminalSections`: the projection kernel
  is the submodule of `f^(n+1)`-multiples.

## Implementation notes

The site is assumed small, which is what makes `SheafOfModules R` abelian and the sections
functor left exact; the site of opens of a topological space, the case consumed by Stacks
0BLB, is small. The coefficient ring `A` acts through a ring map to the sections of `R` over
the terminal object, so its universe is independent of the site's.

This is the degree-zero, terminal-sections half of Stacks 0EHA. The two cohomological
statements of that tag are not proved here, so no tag is recorded.

## References

* [Stacks Project, Tag 0EHA](https://stacks.math.columbia.edu/tag/0EHA)
* [Stacks Project, Tag 0H39](https://stacks.math.columbia.edu/tag/0H39)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped IsMulCommutative

universe u w a m

namespace Stacks.Modules

/-- Transition maps carry the projection from the limit in degree `j` to the one in degree
`i ≤ j`. -/
private lemma limit_π_map_of_le {A : Type a} [CommRing A] (F : ℕᵒᵖ ⥤ ModuleCat.{m} A) {i j : ℕ}
    (h : i ≤ j) (x : (limit F : ModuleCat.{m} A)) :
    (F.map (homOfLE h).op).hom ((limit.π F (op j)).hom x) = (limit.π F (op i)).hom x :=
  congrArg (fun g => g.hom x) (limit.w F (homOfLE h).op)

private lemma exists_smul_eq_of_lifts
    {A : Type a} [CommRing A] (f : A) (F : ℕᵒᵖ ⥤ ModuleCat.{m} A)
    (ι : ∀ n, F.obj (op n) ⟶ F.obj (op (n + 1)))
    (hinj : ∀ n, Function.Injective (ι n).hom)
    (hfac : ∀ n (x : F.obj (op (n + 1))),
      (ι n).hom ((F.map (homOfLE (Nat.le_succ n)).op).hom x) = f • x)
    (x : (limit F : ModuleCat.{m} A))
    (hlift : ∀ n, ∃ y, (ι n).hom y = (limit.π F (op (n + 1))).hom x) :
    ∃ z : (limit F : ModuleCat.{m} A), f • z = x := by
  have hback (k : ℕ) (y : F.obj (op k)) :
      (F.map (homOfLE (Nat.le_succ k)).op).hom ((ι k).hom y) = f • y := by
    apply hinj k
    rw [hfac, map_smul]
  choose y hy using hlift
  have hycompat (k : ℕ) :
      (F.map (homOfLE (Nat.le_succ k)).op).hom (y (k + 1)) = y k := by
    apply hinj k
    rw [hfac, hy, ← hback (k + 1), hy, limit_π_map_of_le]
  let c : Cone (F ⋙ forget (ModuleCat.{m} A)) :=
    { pt := PUnit
      π := NatTrans.ofOpSequence (fun k => ↾fun _ => y k) (by
        intro k
        ext z
        exact (hycompat k).symm) }
  let hc := isLimitOfPreserves (forget (ModuleCat.{m} A)) (limit.isLimit F)
  let z : (limit F : ModuleCat.{m} A) := hc.lift c PUnit.unit
  have hz (k : ℕ) : (limit.π F (op k)).hom z = y k :=
    congrArg (fun g => g PUnit.unit) (hc.fac c (op k))
  refine ⟨z, Concrete.limit_ext F _ _ ?_⟩
  intro k
  show (limit.π F k).hom (f • z) = (limit.π F k).hom x
  rw [map_smul, hz k.unop, ← hback, hy, limit_π_map_of_le]

private lemma range_pow_eq_ker_limitProjection_of_lifts
    {A : Type a} [CommRing A] (f : A) (F : ℕᵒᵖ ⥤ ModuleCat.{m} A)
    (ι : ∀ n, F.obj (op n) ⟶ F.obj (op (n + 1)))
    (hinj : ∀ n, Function.Injective (ι n).hom)
    (hfac : ∀ n (x : F.obj (op (n + 1))),
      (ι n).hom ((F.map (homOfLE (Nat.le_succ n)).op).hom x) = f • x)
    (hzero : ∀ x : F.obj (op 0), f • x = 0)
    (hlift : ∀ (x : (limit F : ModuleCat.{m} A)), (limit.π F (op 0)).hom x = 0 →
      ∀ n, ∃ y, (ι n).hom y = (limit.π F (op (n + 1))).hom x)
    (n : ℕ) :
    (LinearMap.lsmul A (limit F : ModuleCat.{m} A) (f ^ (n + 1))).range =
      (limit.π F (op n)).hom.ker := by
  have hsucc (k : ℕ) (x : (limit F : ModuleCat.{m} A)) :
      (limit.π F (op (k + 1))).hom (f • x) =
        (ι k).hom ((limit.π F (op k)).hom x) := by
    rw [map_smul, ← hfac, limit_π_map_of_le]
  have hbase (x : (limit F : ModuleCat.{m} A)) :
      (limit.π F (op 0)).hom x = 0 ↔ ∃ y : (limit F : ModuleCat.{m} A), f • y = x := by
    refine ⟨fun hx => exists_smul_eq_of_lifts f F ι hinj hfac x (hlift x hx), ?_⟩
    rintro ⟨y, rfl⟩
    rw [map_smul, hzero]
  have hpow : ∀ k (x : (limit F : ModuleCat.{m} A)),
      (limit.π F (op k)).hom x = 0 ↔ ∃ y : (limit F : ModuleCat.{m} A), f ^ (k + 1) • y = x := by
    intro k
    induction k with
    | zero => simpa using hbase
    | succ k ih =>
      intro x
      constructor
      · intro hx
        have hx0 : (limit.π F (op 0)).hom x = 0 := by
          rw [← limit_π_map_of_le F (Nat.zero_le (k + 1)), hx, map_zero]
        obtain ⟨y, rfl⟩ := (hbase x).mp hx0
        rw [hsucc] at hx
        have hy : (limit.π F (op k)).hom y = 0 :=
          hinj k (hx.trans (map_zero (ι k).hom).symm)
        obtain ⟨z, rfl⟩ := (ih y).mp hy
        exact ⟨z, by rw [pow_succ', mul_smul]⟩
      · rintro ⟨y, rfl⟩
        rw [pow_succ', mul_smul, hsucc, (ih _).mpr ⟨y, rfl⟩, map_zero]
  ext x
  exact (hpow n x).symm

/-- Through sections over a terminal object `T`, multiplication by the section `scalarMap f`
acts on sections over `T` as the scalar `f`. -/
private theorem evaluation_restrictScalars_map_terminalSectionToEnd_apply
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{w}) [∀ U, IsMulCommutative (R.obj.obj U)]
    (T : C) (hT : IsTerminal T) {A : Type a} [CommRing A]
    (scalarMap : A →+* R.obj.obj (op T)) (f : A) (M : SheafOfModules.{u} R)
    (x : (SheafOfModules.evaluation R (op T) ⋙ ModuleCat.restrictScalars scalarMap).obj M) :
    ((SheafOfModules.evaluation R (op T) ⋙ ModuleCat.restrictScalars scalarMap).map
      ((Stacks.SheafOfModules.terminalSectionToEnd R T hT (scalarMap f)).asHom.app M)).hom x =
        f • x := by
  change M.val.obj (op T) at x
  show (((Stacks.SheafOfModules.terminalSectionToEnd R T hT (scalarMap f)).asHom.app M).val.app
    (op T)).hom x = scalarMap f • x
  rw [Stacks.SheafOfModules.terminalSectionToEnd_apply, hT.hom_ext (hT.from T) (𝟙 T)]
  simp

/-- On the limit of the inverse system `E(𝓕ₙ)`, the composite transition map `𝓕ₖ → 𝓕₀`
carries the degree-`k` projection to the degree-zero projection. -/
private theorem map_proj_apply_limit_π
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    {A : Type a} [CommRing A] (E : SheafOfModules.{u} R ⥤ ModuleCat.{m} A)
    (obj : ℕ → SheafOfModules.{u} R) (map : ∀ n, obj (n + 1) ⟶ obj n) (k : ℕ)
    (x : (limit (Functor.ofOpSequence (X := fun n => E.obj (obj n))
      (fun n => E.map (map n))) : ModuleCat.{m} A)) :
    (E.map (Stacks.Cohomology.InverseSystems.TorsionFreeDivisible.proj obj map k)).hom
        ((limit.π (Functor.ofOpSequence (X := fun n => E.obj (obj n))
          (fun n => E.map (map n))) (op k)).hom x) =
      (limit.π (Functor.ofOpSequence (X := fun n => E.obj (obj n))
        (fun n => E.map (map n))) (op 0)).hom x := by
  let F : ℕᵒᵖ ⥤ ModuleCat.{m} A :=
    Functor.ofOpSequence (X := fun n => E.obj (obj n)) (fun n => E.map (map n))
  show (E.map (Stacks.Cohomology.InverseSystems.TorsionFreeDivisible.proj obj map k)).hom
    ((limit.π F (op k)).hom x) = (limit.π F (op 0)).hom x
  have hstep (k : ℕ) :
      (E.map (map k)).hom ((limit.π F (op (k + 1))).hom x) = (limit.π F (op k)).hom x := by
    have hw := limit_π_map_of_le F (Nat.le_succ k) x
    rwa [Functor.ofOpSequence_map_homOfLE_succ] at hw
  induction k with
  | zero =>
    rw [Stacks.Cohomology.InverseSystems.TorsionFreeDivisible.proj, E.map_id]
    rfl
  | succ k ih =>
    have hcomp : (E.map (Stacks.Cohomology.InverseSystems.TorsionFreeDivisible.proj obj map
            (k + 1))).hom
          ((limit.π F (op (k + 1))).hom x) =
        (E.map (Stacks.Cohomology.InverseSystems.TorsionFreeDivisible.proj obj map k)).hom
          ((E.map (map k)).hom ((limit.π F (op (k + 1))).hom x)) := by
      rw [Stacks.Cohomology.InverseSystems.TorsionFreeDivisible.proj, E.map_comp]
      exact ModuleCat.comp_apply _ _ _
    rw [hcomp, hstep k, ih]

/-- In degree zero, the kernel of the projection from the inverse limit of terminal sections
to the term `𝓕ₙ₊₁` is the submodule of `f^(n+1)`-multiples. The coefficient ring acts through
a ring homomorphism to the ring of sections over the terminal object. -/
theorem range_pow_eq_ker_limitProjection_terminalSections
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{w}) [∀ U, IsMulCommutative (R.obj.obj U)]
    (T : C) (hT : IsTerminal T) {A : Type a} [CommRing A]
    (scalarMap : A →+* R.obj.obj (op T)) (f : A)
    (obj : ℕ → SheafOfModules.{u} R) (map : ∀ n, obj (n + 1) ⟶ obj n)
    (h : Stacks.Cohomology.InverseSystems.TorsionFreeDivisible.Condition1
      (Stacks.SheafOfModules.terminalSectionToEnd R T hT (scalarMap f)) obj map)
    (F : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hF : F = Functor.ofOpSequence
      (X := fun n => (SheafOfModules.evaluation R (op T) ⋙
        ModuleCat.restrictScalars scalarMap).obj (obj n))
      (fun n => (SheafOfModules.evaluation R (op T) ⋙
        ModuleCat.restrictScalars scalarMap).map (map n)))
    (n : ℕ) :
    (LinearMap.lsmul A (limit F : ModuleCat.{u} A) (f ^ (n + 1))).range =
      (limit.π F (op n)).hom.ker := by
  classical
  subst hF
  let E := SheafOfModules.evaluation R (op T) ⋙ ModuleCat.restrictScalars scalarMap
  let F : ℕᵒᵖ ⥤ ModuleCat.{u} A :=
    Functor.ofOpSequence (X := fun n => E.obj (obj n)) (fun n => E.map (map n))
  have : E.Additive := by
    dsimp [E, SheafOfModules.evaluation]
    infer_instance
  let g := Stacks.SheafOfModules.terminalSectionToEnd R T hT (scalarMap f)
  choose ι w hfac hshort using h
  have hmonoι (k : ℕ) : Mono (ι k) := (hshort k).mono_f
  have hscalar (M : SheafOfModules.{u} R) (x : E.obj M) : (E.map (g.asHom.app M)).hom x = f • x :=
    evaluation_restrictScalars_map_terminalSectionToEnd_apply R T hT scalarMap f M x
  have hback (k : ℕ) : ι k ≫ map k = g.asHom.app (obj k) := by
    have := hmonoι k
    apply (cancel_mono (ι k)).1
    rw [Category.assoc, hfac]
    exact (Stacks.Cohomology.InverseSystems.TorsionFreeDivisible.mulF_naturality g (ι k)).symm
  have hkill : g.asHom.app (obj 0) = 0 := by
    rw [← hback 0]
    simpa [Stacks.Cohomology.InverseSystems.TorsionFreeDivisible.proj] using w 0
  have hproj := map_proj_apply_limit_π E obj map
  apply range_pow_eq_ker_limitProjection_of_lifts f F (fun k => E.map (ι k))
  · intro k
    have := hmonoι k
    have hmono : Mono ((ModuleCat.restrictScalars scalarMap).map
      ((SheafOfModules.evaluation R (op T)).map (ι k))) := inferInstance
    exact (ModuleCat.mono_iff_injective _).mp hmono
  · intro k x
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    show (E.map (ι k)).hom ((E.map (map k)).hom x) = f • x
    have he := congrArg (fun q => (E.map q).hom x) (hfac k)
    rw [E.map_comp] at he
    exact ((ModuleCat.comp_apply _ _ _).symm.trans he).trans (hscalar _ x)
  · intro x
    have hzero : (E.map (g.asHom.app (obj 0))).hom x = 0 := by
      rw [hkill, E.map_zero, ModuleCat.hom_zero]
      exact LinearMap.zero_apply x
    exact (hscalar (obj 0) x).symm.trans hzero
  · intro x hx k
    have hex := ShortComplex.exact_of_f_is_kernel
      ((ShortComplex.mk (ι k)
        (Stacks.Cohomology.InverseSystems.TorsionFreeDivisible.proj obj map (k + 1)) (w k)).map E)
      (KernelFork.mapIsLimit _ (hshort k).fIsKernel E)
    exact (ShortComplex.moduleCat_exact_iff _).mp hex _ ((hproj (k + 1) x).trans hx)

end Stacks.Modules

end
