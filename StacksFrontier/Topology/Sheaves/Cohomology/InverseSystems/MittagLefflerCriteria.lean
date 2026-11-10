module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Images
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Noetherian.Filter
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalSectionSmul
public import StacksFrontier.CategoryTheory.Abelian.InverseSystem
public import StacksFrontier.Topology.Sheaves.Cohomology.InverseSystems.TorsionFreeAndDivisibleSystems
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
import StacksFrontier.CategoryTheory.Abelian.InverseSystemProDominated
import StacksCore.Tactic.StacksAttribute

/-!
# Mittag-Leffler criteria for the cohomology of an inverse system of sheaves

Let `X` be a topological space, `A` a ring and `f ∈ A` acting on the sheaves of modules on `X`
through the structure sheaf. For an inverse system `… → ℱ₃ → ℱ₂ → ℱ₁` of sheaves of modules
satisfying condition (1) of Stacks 0H39 — each `ℱ_{n+1}` sits in a short exact sequence
`0 → ℱ₁ → ℱ_{n+1} → ℱ_n → 0` whose composite the other way is multiplication by `f` — the
inverse system `n ↦ H^p(X, ℱ_n)` satisfies the Mittag-Leffler condition as soon as a
finiteness hypothesis holds one degree up. Two such hypotheses are treated: finiteness of
`H^{p+1}(X, ℱ₁)` itself (Stacks 0BLC), and the weaker finiteness of the image, respectively
the intersection of the images, of `H^{p+1}(X, ℱ_m) → H^{p+1}(X, ℱ₁)` (Stacks 0DXG).

Both proofs run through the same comparison. Cohomology on a site is constructed in
`Stacks.Cohomology.SiteModules` as the right derived functors of global sections valued in
modules over the ring `Γ(X, 𝒪)` of global sections of the structure sheaf; the statements here
are about the right derived functors of evaluation at the top open, over the ring `𝒪(X)`. On
the site of opens of a space the two agree: `topSectionsIso` identifies global sections with
evaluation at `⊤` after restricting scalars along `topSectionRingHom`, and derived functors
commute with the exact restriction of scalars, giving `topEvaluationDerivedIso`. Transporting
the universal `δ`-functor of Stacks 071H across it produces the connecting maps and their
naturality, which is all either argument uses about cohomology.

From there the two arguments diverge. For 0BLC the boundary maps `H^p(X, ℱ_{n+1}) →
H^{p+1}(X, ℱ₁)` have ranges increasing inside a Noetherian module, so they stabilise; the
resulting decomposition of a class as an "upward" image plus a "downward" image turns the
descending filtration by transition images into a recurrence which, together with nilpotence
of multiplication by `f` on `ℱ_n`, forces the filtration to stop
(`antitone_stabilizes_of_nilpotent`). For 0DXG the same boundary maps are used, but the
upward maps are assembled into the long short exact sequences
`0 → ℱ_m → ℱ_{m+n+1} → ℱ_n → 0` of `shortExact_up_down`, and stabilisation is applied inside
the intersection of the images rather than in the whole of `H^{p+1}(X, ℱ₁)`.

## Main results

* `Stacks.Cohomology.InverseSystems.isMittagLefflerCategorical_of_finite_cohomology`:
  Stacks 0BLC.
* `Stacks.Cohomology.InverseSystems.isMittagLefflerCategorical_of_finite_cohomology_image`:
  Stacks 0DXG.

## Implementation notes

The coefficient ring `A` of the source is a ring acting on `𝒪(X)`, not `𝒪(X)` itself, so it
enters as an `Algebra A (𝒪(X))` together with the induced `A`-module structures on cohomology;
the element `f ∈ A` acts through `algebraMap`. Multiplication by a global section as an
endomorphism of the identity functor of sheaves of modules is
`Stacks.SheafOfModules.terminalSectionToEnd`, which is the shape in which the conditions of
Stacks 0H39 are stated.

The inverse system is indexed from zero, matching `StacksDraft.Ch20.Sec36.Tag0H39`: `obj n` is
the source's `ℱ_{n+1}` and `map n : obj (n + 1) ⟶ obj n` is `ℱ_{n+2} → ℱ_{n+1}`. In
particular `obj 0 = ℱ₁`.

Cohomology of sheaves of modules on an arbitrary site carries the instances
`Stacks.Cohomology.SiteModules.moduleSheaves{Abelian, Grothendieck, EnoughInjectives}`, which
are stated for a universe-enlarged module category and would be preferred over the ones the
statements below need; they are therefore removed locally at the two main theorems.

## References

* [Stacks Project, Tag 0BLC](https://stacks.math.columbia.edu/tag/0BLC)
* [Stacks Project, Tag 0DXG](https://stacks.math.columbia.edu/tag/0DXG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped IsMulCommutative

universe u

namespace Stacks.Cohomology.InverseSystems

/-! ### Derived functors and exact postcomposition -/

section DerivedFunctors

/-- Postcomposition with a homology-preserving functor commutes with right derived
functors. -/
private def rightDerivedCompIso {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [HasInjectiveResolutions C] [Abelian D] [Abelian E]
    (F : C ⥤ D) [F.Additive] (G : D ⥤ E) [G.Additive] [G.PreservesHomology] (p : ℕ) :
    F.rightDerived p ⋙ G ≅ (F ⋙ G).rightDerived p := by
  refine NatIso.ofComponents (fun Z => ?_) ?_
  · unfold Functor.rightDerived Functor.rightDerivedToHomotopyCategory
      HomotopyCategory.homologyFunctor
    exact (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      ((injectiveResolutions C).obj Z).as).sc p).mapHomologyIso G |>.symm
  · intro Z W f
    obtain ⟨g, hg⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℕ)).map_surjective
      ((injectiveResolutions C).map f)
    unfold Functor.rightDerived Functor.rightDerivedToHomotopyCategory
    simp only [Functor.comp_map]
    rw [← hg]
    unfold HomotopyCategory.homologyFunctor
    dsimp [Functor.comp_map, Functor.mapHomotopyCategory,
      HomologicalComplex.homologyFunctor]
    exact ShortComplex.mapHomologyIso_inv_naturality
      ((HomologicalComplex.shortComplexFunctor D (ComplexShape.up ℕ) p).map
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map g)) G

/-- A natural isomorphism of additive functors induces one of their right derived
functors. -/
private def rightDerivedIso {C D : Type*} [Category C] [Category D]
    [Abelian C] [HasInjectiveResolutions C] [Abelian D]
    {F G : C ⥤ D} [F.Additive] [G.Additive] (e : F ≅ G) (p : ℕ) :
    F.rightDerived p ≅ G.rightDerived p where
  hom := NatTrans.rightDerived e.hom p
  inv := NatTrans.rightDerived e.inv p
  hom_inv_id := by rw [← NatTrans.rightDerived_comp, e.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by rw [← NatTrans.rightDerived_comp, e.inv_hom_id, NatTrans.rightDerived_id]

end DerivedFunctors

/-! ### Cohomology on a space as the derived functors of evaluation at the top open -/

section TopEvaluation

variable {X : Type u} [TopologicalSpace X]
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- Evaluation of sheaves of modules at the top open is additive. -/
instance evaluation_top_additive :
    (SheafOfModules.evaluation R (op (⊤ : Opens X)) :
      SheafOfModules.{u} R ⥤ ModuleCat.{u} (R.obj.obj (op (⊤ : Opens X)))).Additive := by
  dsimp [SheafOfModules.evaluation]
  infer_instance

/-- A section over the top open, as a scalar in the ring of global sections of the structure
sheaf. -/
private def topSectionRingHom :
    R.obj.obj (op (⊤ : Opens X)) →+* RingCat.sectionsSubring R.obj where
  toFun b := ⟨(Stacks.SheafOfModules.terminalSection R ⊤ isTerminalTop b).val,
    (Stacks.SheafOfModules.terminalSection R ⊤ isTerminalTop b).property⟩
  map_one' := by ext U; exact map_one _
  map_mul' _ _ := by ext U; exact map_mul _ _ _
  map_zero' := by ext U; exact map_zero _
  map_add' _ _ := by ext U; exact map_add _ _ _

/-- Global sections of a sheaf of modules on a space, with scalars restricted along
`topSectionRingHom`, are its sections over the top open. -/
private def topSectionsIso :
    SiteModules.globalSectionsFunctor R ⋙ ModuleCat.restrictScalars (topSectionRingHom R) ≅
      SheafOfModules.evaluation R (op (⊤ : Opens X)) := by
  refine NatIso.ofComponents (fun M => ?_) ?_
  · let e : ((SiteModules.globalSectionsFunctor R ⋙
        ModuleCat.restrictScalars (topSectionRingHom R)).obj M) →ₗ[
        R.obj.obj (op (⊤ : Opens X))] M.val.obj (op ⊤) :=
      { toFun := fun s => s.eval (op ⊤)
        map_add' := fun _ _ => rfl
        map_smul' := by
          intro a s
          change R.obj.map (isTerminalTop.from (⊤ : Opens X)).op a • _ = a • _
          simp }
    exact (LinearEquiv.ofBijective e ⟨by
      intro s t h
      apply Subtype.ext
      funext U
      have hs := M.val.sections_property s (isTerminalTop.from U.unop).op
      have ht := M.val.sections_property t (isTerminalTop.from U.unop).op
      exact hs.symm.trans ((congrArg (M.val.map _) h).trans ht), by
      intro x
      refine ⟨M.val.sectionsMk (fun U => M.val.map (isTerminalTop.from U.unop).op x)
        (by intro U V i
            rw [← M.val.map_comp_apply]
            congr 2), ?_⟩
      change M.val.map (isTerminalTop.from (⊤ : Opens X)).op x = x
      change M.val.map (𝟙 (op (⊤ : Opens X))) x = x
      exact congrArg (fun f => f x) (M.val.map_id _)⟩).toModuleIso
  · intro M N f
    ext s
    rfl

/-- Restriction of scalars along `topSectionRingHom` preserves homology: it is exact. -/
private instance topSectionRestrictScalars_preservesHomology :
    (ModuleCat.restrictScalars (topSectionRingHom R)).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ fun S hS =>
    (ShortComplex.moduleCat_exact_iff (S.map (ModuleCat.restrictScalars (topSectionRingHom R)))).2
      ((ShortComplex.moduleCat_exact_iff S).1 hS)

/-- A universal cohomological `δ`-functor computing the cohomology of sheaves of modules,
chosen once and for all. -/
private def cohomologyDelta :
    DeltaFunctor (SheafOfModules.{u} R) (ModuleCat.{u} (RingCat.sectionsSubring R.obj)) :=
  Classical.choose (SiteModules.exists_universal_cohomologyDeltaFunctor R)

private lemma cohomologyDelta_functor (n : ℕ) :
    (cohomologyDelta R).functor n = SiteModules.cohomologyFunctor R n :=
  (Classical.choose_spec (SiteModules.exists_universal_cohomologyDeltaFunctor R)).1 n

/-- The chosen `δ`-functor computes the right derived functors of evaluation at the top
open. -/
private def topEvaluationDerivedIso (n : ℕ) :
    (cohomologyDelta R).functor n ⋙ ModuleCat.restrictScalars (topSectionRingHom R) ≅
      (SheafOfModules.evaluation R (op (⊤ : Opens X))).rightDerived n :=
  Functor.isoWhiskerRight (eqToIso (cohomologyDelta_functor R n))
      (ModuleCat.restrictScalars (topSectionRingHom R)) ≪≫
    rightDerivedCompIso (SiteModules.globalSectionsFunctor R) _ n ≪≫
      rightDerivedIso (topSectionsIso R) n

/-- **The connecting maps of cohomology on a space**, in the form used for Stacks 0BLC: the
range of the map induced by a surjection is the kernel of the boundary, and the boundaries are
natural in the short exact sequence.

Everything either Mittag-Leffler argument uses about cohomology is here, and none of it is
special to Stacks 0BLC: the boundaries come from the universal `δ`-functor of Stacks 071H
transported along `Stacks.Cohomology.InverseSystems.topEvaluationDerivedIso`. It is public
because the general-ideal Mittag-Leffler criterion
`Stacks.Cohomology.IdealBoundaries.isMittagLefflerCategorical_of_idealBoundaries` asks for the
same data, for an inverse system whose boundaries land in a *varying* family of modules rather
than in a single one. -/
theorem exists_connecting_maps (p : ℕ) :
    let E := SheafOfModules.evaluation R (op (⊤ : Opens X))
    (E.rightDerived p).Additive ∧
    ∃ δ : ∀ {S : ShortComplex (SheafOfModules.{u} R)}, S.ShortExact →
        ((E.rightDerived p).obj S.X₃ ⟶ (E.rightDerived (p + 1)).obj S.X₁),
      (∀ {S : ShortComplex (SheafOfModules.{u} R)} (hS : S.ShortExact),
        LinearMap.range ((E.rightDerived p).map S.g).hom = LinearMap.ker (δ hS).hom) ∧
      (∀ {S T : ShortComplex (SheafOfModules.{u} R)}
        (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T),
        (E.rightDerived p).map φ.τ₃ ≫ δ hT =
          δ hS ≫ (E.rightDerived (p + 1)).map φ.τ₁) := by
  let E := SheafOfModules.evaluation R (op (⊤ : Opens X))
  let K := ModuleCat.restrictScalars (topSectionRingHom R)
  let H := cohomologyDelta R
  let e (n : ℕ) : H.functor n ⋙ K ≅ E.rightDerived n := topEvaluationDerivedIso R n
  let δ {S : ShortComplex (SheafOfModules.{u} R)} (hS : S.ShortExact) :=
    (e p).inv.app S.X₃ ≫ K.map (H.δ hS p) ≫ (e (p + 1)).hom.app S.X₁
  refine ⟨Functor.additive_of_iso (e p), δ, ?_, ?_⟩
  · intro S hS
    have hz : (E.rightDerived p).map S.g ≫ δ hS = 0 := by
      dsimp [δ]
      rw [(e p).inv.naturality_assoc, Functor.comp_map, ← K.map_comp_assoc, H.map_g_δ,
        K.map_zero, zero_comp, comp_zero]
    have hex := (H.exact_δ₁ hS p).map K
    have hi : (H.scδ₁ hS p).map K ≅
        ShortComplex.mk ((E.rightDerived p).map S.g) (δ hS) hz :=
      ShortComplex.isoMk ((e p).app S.X₂) ((e p).app S.X₃) ((e (p + 1)).app S.X₁)
        (((e p).hom.naturality S.g).symm) (by dsimp [δ]; simp)
    exact (ShortComplex.exact_of_iso hi hex).moduleCat_range_eq_ker
  · intro S T hS hT φ
    dsimp [δ]
    rw [(e p).inv.naturality_assoc, Functor.comp_map, ← K.map_comp_assoc,
      H.δ_naturality hS hT φ p, K.map_comp]
    have hn := (e (p + 1)).hom.naturality φ.τ₁
    dsimp only [Functor.comp_map] at hn
    simp only [Category.assoc]
    rw [hn]

/-- The connecting maps of cohomology on a space, in the form used for Stacks 0DXG: the
boundary fits into an exact sequence with the map induced by a surjection. -/
private lemma exists_cohomology_boundary (p : ℕ) :
    let P := (SheafOfModules.evaluation R (op (⊤ : Opens X))).rightDerived p
    let Q := (SheafOfModules.evaluation R (op (⊤ : Opens X))).rightDerived (p + 1)
    P.Additive ∧ ∃ δ : ∀ {S : ShortComplex (SheafOfModules.{u} R)}, S.ShortExact →
        (P.obj S.X₃ ⟶ Q.obj S.X₁),
      (∀ {S : ShortComplex (SheafOfModules.{u} R)} (hS : S.ShortExact),
        ∃ hz : P.map S.g ≫ δ hS = 0, (ShortComplex.mk _ _ hz).Exact) ∧
      (∀ {S T : ShortComplex (SheafOfModules.{u} R)}
        (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T),
        P.map φ.τ₃ ≫ δ hT = δ hS ≫ Q.map φ.τ₁) := by
  obtain ⟨hadd, δ, hδ, hnat⟩ := exists_connecting_maps R p
  exact ⟨hadd, δ, fun hS => ⟨ModuleCat.hom_ext (LinearMap.range_le_ker_iff.mp (hδ hS).le),
    (ShortComplex.moduleCat_exact_iff_range_eq_ker _).2 (hδ hS)⟩, hnat⟩

end TopEvaluation

/-! ### Stacks 0BLC -/

section Blc

/-- A descending filtration whose successive quotients are generated by a nilpotent
endomorphism eventually stabilizes. -/
private theorem antitone_stabilizes_of_nilpotent
    {B M : Type*} [Ring B] [AddCommGroup M] [Module B M]
    (a : Module.End B M) (I : ℕ → Submodule B M) (hI : Antitone I)
    (ha : ∀ n, (I n).map a ≤ I (n + 1))
    (N k : ℕ) (hk : a ^ k = 0)
    (hrec : ∀ n, N ≤ n → I (n + 1) ≤ (I n).map a ⊔ I (n + 2)) :
    ∀ n, N + k ≤ n → I n = I (N + k) := by
  have hbound (b : ℕ) (hb : N ≤ b) :
      ∀ j, I (b + j) ≤ LinearMap.range (a ^ j) ⊔ I (b + j + 1) := by
    intro j
    induction j with
    | zero =>
      simpa only [pow_zero, Module.End.one_eq_id, LinearMap.range_id, top_sup_eq] using le_top
    | succ j ih =>
      calc
        I (b + (j + 1)) ≤ (I (b + j)).map a ⊔ I (b + j + 2) := by
          simpa only [Nat.add_assoc] using hrec (b + j) (by omega)
        _ ≤ (LinearMap.range (a ^ j) ⊔ I (b + j + 1)).map a ⊔ I (b + j + 2) :=
          sup_le_sup_right (Submodule.map_mono ih) _
        _ ≤ LinearMap.range (a ^ (j + 1)) ⊔ I (b + (j + 1) + 1) := by
          rw [Submodule.map_sup, ← LinearMap.range_comp, ← Module.End.mul_eq_comp,
            ← pow_succ']
          exact sup_le (sup_le le_sup_left ((ha (b + j + 1)).trans le_sup_right))
            le_sup_right
  have hstep (n : ℕ) (hn : N + k ≤ n) : I n = I (n + 1) := by
    apply le_antisymm ?_ (hI (Nat.le_succ n))
    have h := hbound (n - k) (by omega) k
    simpa [Nat.sub_add_cancel (show k ≤ n by omega), hk] using h
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih => exact (hstep n hn).symm.trans ih

/-- If an upward map does not change the range of the boundary, every class splits as an
upward image plus a downward image. -/
private lemma exists_eq_map_add_map_of_range_eq
    {B : Type*} [Ring B] {C : Type*} [Category C] (P : C ⥤ ModuleCat.{u} B)
    {M : ModuleCat.{u} B} {X Y Z : C} (up : X ⟶ Y) (down : Z ⟶ Y)
    (dX : P.obj X ⟶ M) (dY : P.obj Y ⟶ M)
    (hd : LinearMap.range (P.map down).hom = LinearMap.ker dY.hom)
    (hdu : P.map up ≫ dY = dX) (heq : LinearMap.range dY.hom = LinearMap.range dX.hom)
    (x : P.obj Y) : ∃ y z, x = P.map up y + P.map down z := by
  obtain ⟨y, hy⟩ : dY x ∈ LinearMap.range dX.hom := heq ▸ LinearMap.mem_range_self _ x
  obtain ⟨z, hz⟩ : x - P.map up y ∈ LinearMap.range (P.map down).hom := by
    rw [hd]
    change dY (x - P.map up y) = 0
    rw [map_sub, ← ModuleCat.comp_apply, hdu, hy, sub_self]
  exact ⟨y, z, by rw [hz]; abel⟩

/-- A functor to modules sends a power of a natural endomorphism to the power of its image. -/
private lemma map_pow_app_hom {B : Type*} [Ring B] {C : Type*} [Category C]
    (P : C ⥤ ModuleCat.{u} B) (ρ : End (𝟭 C)) (X : C) (n : ℕ) :
    (P.map ((ρ ^ n).asHom.app X)).hom = (P.map (ρ.asHom.app X)).hom ^ n := by
  induction n with
  | zero =>
    change (P.map (𝟙 X)).hom = 1
    rw [P.map_id]
    rfl
  | succ n ih =>
    rw [pow_succ, End.mul_asHom, NatTrans.comp_app,
      P.map_comp, ModuleCat.hom_comp, ih]
    rfl

/-- Two morphisms of modules with the same range have the same image subobject. -/
private lemma imageSubobject_eq_of_range_eq
    {S : Type*} [Ring S] {M N P : ModuleCat S} (a : M ⟶ P) (b : N ⟶ P)
    (h : a.hom.range = b.hom.range) :
    Subobject.mk (image.ι a) = Subobject.mk (image.ι b) := by
  have ha := Subobject.mk_eq_mk_of_comm (image.ι a)
    (ModuleCat.ofHom a.hom.range.subtype) (ModuleCat.imageIsoRange a)
    (ModuleCat.imageIsoRange_hom_subtype a)
  have hb := Subobject.mk_eq_mk_of_comm (image.ι b)
    (ModuleCat.ofHom b.hom.range.subtype) (ModuleCat.imageIsoRange b)
    (ModuleCat.imageIsoRange_hom_subtype b)
  rw [ha, hb]
  exact congrArg (fun L : Submodule S P => Subobject.mk (ModuleCat.ofHom L.subtype)) h

/-- If `ι` is monic and `m ≫ ι` is multiplication by `g`, then `ι ≫ m` is multiplication
by `g` as well. -/
private lemma comp_eq_app_of_mono {C : Type*} [Category C] (g : End (𝟭 C)) {X Y : C}
    (ι : X ⟶ Y) (m : Y ⟶ X) [Mono ι] (hf : m ≫ ι = g.asHom.app Y) : ι ≫ m = g.asHom.app X := by
  apply (cancel_mono ι).1
  rw [Category.assoc, hf]
  exact g.asHom.naturality ι

/-- Noetherian boundary images give Mittag-Leffler stabilization for a tower with compatible
upward maps and a termwise nilpotent natural endomorphism. -/
private theorem isMittagLeffler_of_boundaries
    {B : Type*} [Ring B] {C : Type*} [Category C] [Preadditive C]
    (P : C ⥤ ModuleCat.{u} B) [P.Additive]
    (ρ : End (𝟭 C)) (obj : ℕ → C) (map : ∀ n, obj (n + 1) ⟶ obj n)
    (up : ∀ n, obj n ⟶ obj (n + 1))
    (hup : ∀ n, up n ≫ map n = ρ.asHom.app (obj n))
    (hnil : ∀ n, (ρ ^ (n + 1)).asHom.app (obj n) = 0)
    (M : ModuleCat.{u} B) [IsNoetherian B M]
    (d : ∀ n, P.obj (obj n) ⟶ M)
    (hd : ∀ n, LinearMap.range (P.map (map n)).hom = LinearMap.ker (d n).hom)
    (hdu : ∀ n, P.map (up n) ≫ d (n + 1) = d n) :
    IsMittagLefflerCategorical (Functor.ofOpSequence map ⋙ P) := by
  let D : ℕ →o Submodule B M :=
    { toFun := fun n => LinearMap.range (d n).hom
      monotone' := monotone_nat_of_le_succ fun n _ ⟨y, hy⟩ =>
        ⟨P.map (up n) y, (congrArg (fun f => f y) (hdu n)).trans hy⟩ }
  obtain ⟨N, hN⟩ := monotone_stabilizes_iff_noetherian.mpr ‹IsNoetherian B M› D
  -- Stable boundary images express each class as an upward image plus a downward image.
  have hdecomp (n : ℕ) (hn : N ≤ n) (x : P.obj (obj (n + 1))) :
      ∃ y z, x = P.map (up n) y + P.map (map (n + 1)) z :=
    exists_eq_map_add_map_of_range_eq P (up n) (map (n + 1)) (d n) (d (n + 1)) (hd (n + 1))
      (hdu n) ((hN (n + 1) (by omega)).symm.trans (hN n hn)) x
  intro i
  let T := Functor.ofOpSequence map ⋙ P
  let t (n : ℕ) : P.obj (obj (i + n)) ⟶ P.obj (obj i) :=
    T.map (homOfLE (Nat.le_add_right i n)).op
  let I (n : ℕ) := LinearMap.range (t n).hom
  let a : Module.End B (P.obj (obj i)) := (P.map (ρ.asHom.app (obj i))).hom
  have ht (n : ℕ) : P.map (map (i + n)) ≫ t n = t (n + 1) := by
    rw [← Functor.ofOpSequence_map_homOfLE_succ map (i + n)]
    change T.map (homOfLE (Nat.le_succ (i + n))).op ≫
      T.map (homOfLE (Nat.le_add_right i n)).op = _
    rw [← T.map_comp]
    rfl
  have hnat (n : ℕ) :
      P.map (ρ.asHom.app (obj (i + n))) ≫ t n = t n ≫ P.map (ρ.asHom.app (obj i)) := by
    have h := congrArg P.map
      (ρ.asHom.naturality ((Functor.ofOpSequence map).map (homOfLE (Nat.le_add_right i n)).op))
    rw [P.map_comp, P.map_comp] at h
    exact h.symm
  have hta (n : ℕ) : (P.map (up (i + n)) ≫ t (n + 1)).hom = a.comp (t n).hom := by
    rw [← ht, ← Category.assoc, ← P.map_comp, hup, hnat]
    rfl
  have ha (n : ℕ) : (I n).map a ≤ I (n + 1) := by
    rintro _ ⟨x, ⟨y, rfl⟩, rfl⟩
    exact ⟨P.map (up (i + n)) y, congrArg (fun f => f y) (hta n)⟩
  have hI : Antitone I := antitone_nat_of_succ_le fun n _ ⟨y, hy⟩ =>
    ⟨P.map (map (i + n)) y, (congrArg (fun f => f y) (ht n)).trans hy⟩
  -- On transition images, this decomposition is the filtration recurrence.
  have hrec (n : ℕ) (hn : N ≤ n) : I (n + 1) ≤ (I n).map a ⊔ I (n + 2) := by
    rintro x ⟨y, rfl⟩
    obtain ⟨z, w, hw⟩ := hdecomp (i + n) (by omega) y
    rw [hw, map_add]
    exact Submodule.add_mem_sup ⟨t n z, ⟨z, rfl⟩, (congrArg (fun f => f z) (hta n)).symm⟩
      ⟨w, (congrArg (fun f => f w) (ht (n + 1))).symm⟩
  have hpow : a ^ (i + 1) = 0 := (map_pow_app_hom P ρ (obj i) (i + 1)).symm.trans
    (by rw [hnil, P.map_zero, ModuleCat.hom_zero])
  have hstable := antitone_stabilizes_of_nilpotent a I hI ha N (i + 1) hpow hrec
  refine ⟨i + (N + (i + 1)), Nat.le_add_right _ _, fun m hm => ?_⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le ((Nat.le_add_right i (N + (i + 1))).trans hm)
  have heq := hstable n (by omega)
  exact imageSubobject_eq_of_range_eq (t n) (t (N + (i + 1))) heq

/-- Finiteness over the coefficient ring makes a module Noetherian over any larger commutative
ring whose action extends the coefficient action. -/
private theorem noetherian_of_finiteLength_or_finite
    {A B M : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    (h : IsFiniteLength A M ∨ (IsNoetherianRing A ∧ Module.Finite A M)) :
    IsNoetherian B M := by
  rcases h with hlen | ⟨hNoeth, hFinite⟩
  · exact isNoetherian_of_tower A (isFiniteLength_iff_isNoetherian_isArtinian.mp hlen).1
  · exact isNoetherian_of_tower A
      (@isNoetherian_of_isNoetherianRing_of_finite A M inferInstance inferInstance
        inferInstance hNoeth hFinite)

attribute [-instance] SiteModules.moduleSheavesEnoughInjectives in
attribute [-instance] SiteModules.moduleSheavesGrothendieck in
attribute [-instance] SiteModules.moduleSheavesAbelian in
/-- **Stacks 0BLC.** Let `A` be a ring, `f ∈ A`, `X` a topological space and `… → ℱ₂ → ℱ₁` an
inverse system of sheaves of `A`-modules satisfying condition (1) of Stacks 0H39. If
`H^{p+1}(X, ℱ₁)` has finite length over `A`, or `A` is Noetherian and `H^{p+1}(X, ℱ₁)` is a
finite `A`-module, then the inverse system `n ↦ H^p(X, ℱ_n)` satisfies the Mittag-Leffler
condition. -/
@[stacks 0BLC]
theorem isMittagLefflerCategorical_of_finite_cohomology
    {X : Type u} [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [∀ U, IsMulCommutative (R.obj.obj U)]
    (A : Type u) [CommRing A]
    [Algebra A (R.obj.obj (op (⊤ : Opens X)))] (f : A)
    (obj : ℕ → SheafOfModules.{u} R)
    (map : ∀ n, obj (n + 1) ⟶ obj n) (p : ℕ) :
    let E := SheafOfModules.evaluation R (op (⊤ : Opens X))
    let G := E.rightDerived (p + 1)
    letI : Module A (G.obj (obj 0)) :=
      Module.compHom (G.obj (obj 0)) (algebraMap A (R.obj.obj (op (⊤ : Opens X))))
    ((IsFiniteLength A (G.obj (obj 0))) ∨
      (IsNoetherianRing A ∧ Module.Finite A (G.obj (obj 0)))) →
    Stacks.Cohomology.InverseSystems.TorsionFreeDivisible.Condition1
      (Stacks.SheafOfModules.terminalSectionToEnd R (⊤ : Opens X) isTerminalTop
        (algebraMap A (R.obj.obj (op (⊤ : Opens X))) f)) obj map →
    IsMittagLefflerCategorical
      (Functor.ofOpSequence map ⋙ E.rightDerived p) := by
  dsimp only
  intro hfinite hgood
  let E := SheafOfModules.evaluation R (op (⊤ : Opens X))
  let G := E.rightDerived (p + 1)
  let : Module A (G.obj (obj 0)) :=
    Module.compHom (G.obj (obj 0)) (algebraMap A (R.obj.obj (op (⊤ : Opens X))))
  let B := R.obj.obj (op (⊤ : Opens X))
  let : IsScalarTower A B (G.obj (obj 0)) :=
    IsScalarTower.of_compHom A B (G.obj (obj 0))
  let b : B := algebraMap A B f
  let ρ := Stacks.SheafOfModules.terminalSectionToEnd R (⊤ : Opens X) isTerminalTop b
  have hgood₂ : TorsionFreeDivisible.Condition2 ρ obj map :=
    (TorsionFreeDivisible.stacks0H39_one_iff_two ρ obj map).mp hgood
  have : IsNoetherian B (G.obj (obj 0)) := noetherian_of_finiteLength_or_finite hfinite
  obtain ⟨hadd, δ, hδ, hnat⟩ := exists_connecting_maps R p
  choose up wup hf hsu using hgood
  choose j wj hj hsj using hgood₂
  let (n : ℕ) : Mono (up n) := (hsu n).mono_f
  let (n : ℕ) : Epi (map n) := (hsj n).epi_g
  have hepi : ∀ n, Epi (TorsionFreeDivisible.proj obj map n) := by
    intro n
    induction n with
    | zero =>
      change Epi (𝟙 _)
      infer_instance
    | succ n ih =>
      let := ih
      change Epi (map n ≫ TorsionFreeDivisible.proj obj map n)
      infer_instance
  have hup (n : ℕ) : up n ≫ map n = ρ.asHom.app (obj n) :=
    comp_eq_app_of_mono ρ (up n) (map n) (hf n)
  have hnil (n : ℕ) : (ρ ^ (n + 1)).asHom.app (obj n) = 0 := by
    apply (cancel_epi (map n)).1
    rw [← TorsionFreeDivisible.mulF_naturality (ρ ^ (n + 1)) (map n), ← hj, Category.assoc, wj,
      comp_zero, comp_zero]
  -- The kernels in condition (2) are compatible with the upward maps of condition (1).
  have hju (n : ℕ) : j n ≫ up (n + 1) = j (n + 1) := by
    let := hepi (n + 2)
    apply (cancel_epi (TorsionFreeDivisible.proj obj map (n + 2))).1
    calc
      TorsionFreeDivisible.proj obj map (n + 2) ≫ (j n ≫ up (n + 1)) =
          map (n + 1) ≫ (ρ ^ (n + 1)).asHom.app (obj (n + 1)) ≫ up (n + 1) := by
        change (map (n + 1) ≫ TorsionFreeDivisible.proj obj map (n + 1)) ≫
          (j n ≫ up (n + 1)) = _
        rw [Category.assoc, ← Category.assoc
          (TorsionFreeDivisible.proj obj map (n + 1)), hj]
      _ = (map (n + 1) ≫ up (n + 1)) ≫ (ρ ^ (n + 1)).asHom.app (obj (n + 2)) := by
        rw [TorsionFreeDivisible.mulF_naturality, Category.assoc]
      _ = (ρ ^ (n + 2)).asHom.app (obj (n + 2)) := by
        rw [hf, TorsionFreeDivisible.mulF_pow_succ]
      _ = TorsionFreeDivisible.proj obj map (n + 2) ≫ j (n + 1) :=
        (hj (n + 1)).symm
  apply isMittagLeffler_of_boundaries (E.rightDerived p) ρ obj map up hup hnil
    (G.obj (obj 0)) (fun n => δ (hsj n)) (fun n => hδ (hsj n))
  intro n
  let φ : ShortComplex.mk (j n) (map n) (wj n) ⟶
      ShortComplex.mk (j (n + 1)) (map (n + 1)) (wj (n + 1)) :=
    { τ₁ := 𝟙 _
      τ₂ := up (n + 1)
      τ₃ := up n
      comm₁₂ := by simpa using (hju n).symm
      comm₂₃ := (hup (n + 1)).trans (hf n).symm }
  simpa [φ] using hnat (hsj n) (hsj (n + 1)) φ

end Blc

/-! ### Stacks 0DXG -/

section Dxg

private lemma isNoetherian_iInf_of_finiteLength
    {A M : Type*} [Ring A] [AddCommGroup M] [Module A M]
    (L : ℕ → Submodule A M) (h : ∃ n, IsFiniteLength A (L n)) :
    IsNoetherian A ↥(⨅ n, L n) := by
  obtain ⟨n, hn⟩ := h
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp hn).1
  exact isNoetherian_of_injective
    (Submodule.inclusion (iInf_le L n)) (Submodule.inclusion_injective _)

private lemma exists_stable_of_monotone_le
    {A M : Type*} [Semiring A] [AddCommMonoid M] [Module A M]
    (N : Submodule A M) [IsNoetherian A N]
    (L : ℕ → Submodule A M) (hL : Monotone L) (hN : ∀ n, L n ≤ N) :
    ∃ c, ∀ n, c ≤ n → L c = L n := by
  let K : ℕ →o Submodule A N :=
    ⟨fun n => (L n).comap N.subtype, fun i j h => Submodule.comap_mono (hL h)⟩
  obtain ⟨c, hc⟩ := monotone_stabilizes_iff_noetherian.mpr ‹IsNoetherian A N› K
  refine ⟨c, fun n hn => le_antisymm (hL hn) fun x hx => ?_⟩
  have hxK : (⟨x, hN n hx⟩ : N) ∈ K n := hx
  rwa [← hc n hn] at hxK

private alias transition_comp := inverseSystem_transition_comp

/-- Stabilising boundary ranges, together with a supply of long exact sequences, give the
Mittag-Leffler condition. -/
private lemma isMittagLeffler_of_stable_boundary_ranges
    {S : Type*} [Ring S] (F : ℕᵒᵖ ⥤ ModuleCat S) (T : ModuleCat S)
    (δ : ∀ n, F.obj (op n) →ₗ[S] T)
    (U : ∀ c n, (_ : c ≤ n) → (F.obj (op c) ⟶ F.obj (op n)))
    (hex : ∀ n x, δ n x = 0 → ∃ y, (F.map (homOfLE (Nat.le_succ n)).op).hom y = x)
    (hδU : ∀ c n (h : c ≤ n) x, δ n ((U c n h).hom x) = δ c x)
    (hzero : ∀ c i n (hc : c ≤ n) (hi : i ≤ n), i + c + 1 ≤ n →
      U c n hc ≫ F.map (homOfLE hi).op = 0)
    (hstable : ∃ c, ∀ n, c ≤ n → (δ c).range = (δ n).range) :
    IsMittagLefflerCategorical F := by
  obtain ⟨c, hc⟩ := hstable
  have hstep (i n : ℕ) (hin : i ≤ n) (hn : i + c + 1 ≤ n) :
      (F.map (homOfLE (hin.trans (Nat.le_succ n))).op).hom.range =
        (F.map (homOfLE hin).op).hom.range := by
    rw [transition_comp F hin (Nat.le_succ n), ModuleCat.hom_comp]
    apply le_antisymm (LinearMap.range_comp_le_range _ _)
    rintro _ ⟨x, rfl⟩
    have hcn : c ≤ n := by omega
    have hx : δ n x ∈ (δ c).range := by
      rw [hc n hcn]
      exact LinearMap.mem_range_self _ _
    obtain ⟨y, hy⟩ := hx
    obtain ⟨z, hz⟩ := hex n (x - (U c n hcn).hom y) (by
      rw [map_sub, hδU, hy, sub_self])
    refine ⟨z, ?_⟩
    rw [LinearMap.comp_apply, hz, map_sub]
    have hzy := congrArg (fun g => g.hom y) (hzero c i n hcn hin hn)
    change (F.map (homOfLE hin).op).hom ((U c n hcn).hom y) = 0 at hzy
    rw [hzy, sub_zero]
  intro i
  refine ⟨i + c + 1, by omega, fun k hk => ?_⟩
  apply imageSubobject_eq_of_range_eq
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    exact (hstep i k (by omega) hk).trans ih

section Tower

variable {X : Type u} [TopologicalSpace X]
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
  {obj : ℕ → SheafOfModules.{u} R}

/-- The iterated transition map `ℱ_{j+1} ⟶ ℱ_{i+1}` of the inverse system, for `i ≤ j`. -/
private def transDown (map : ∀ n, obj (n + 1) ⟶ obj n) {i j : ℕ} (h : i ≤ j) :
    obj j ⟶ obj i :=
  (Functor.ofOpSequence map).map (homOfLE h).op

/-- The iterated upward map `ℱ_{i+1} ⟶ ℱ_{j+1}` assembled from the maps supplied by
condition (1) of Stacks 0H39, for `i ≤ j`. -/
private def transUp (ι : ∀ n, obj n ⟶ obj (n + 1)) {i j : ℕ} (h : i ≤ j) :
    obj i ⟶ obj j :=
  (Functor.ofSequence ι).map (homOfLE h)

variable (map : ∀ n, obj (n + 1) ⟶ obj n) (ι : ∀ n, obj n ⟶ obj (n + 1))

private lemma transDown_refl (i : ℕ) : transDown map (le_refl i) = 𝟙 (obj i) :=
  (Functor.ofOpSequence map).map_id (op i)

private lemma transDown_succ (n : ℕ) : transDown map (Nat.le_succ n) = map n :=
  Functor.ofOpSequence_map_homOfLE_succ map n

private lemma transDown_comp {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    transDown map hjk ≫ transDown map hij = transDown map (hij.trans hjk) :=
  ((Functor.ofOpSequence map).map_comp (homOfLE hjk).op (homOfLE hij).op).symm

private lemma transUp_refl (i : ℕ) : transUp ι (le_refl i) = 𝟙 (obj i) :=
  (Functor.ofSequence ι).map_id i

private lemma transUp_succ (n : ℕ) : transUp ι (Nat.le_succ n) = ι n :=
  Functor.ofSequence_map_homOfLE_succ ι n

private lemma transUp_comp {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    transUp ι hij ≫ transUp ι hjk = transUp ι (hij.trans hjk) :=
  ((Functor.ofSequence ι).map_comp (homOfLE hij) (homOfLE hjk)).symm

private lemma proj_eq_transDown (n : ℕ) :
    Stacks.Cohomology.InverseSystems.TorsionFreeDivisible.proj obj map n = transDown map
      (Nat.zero_le n) := by
  induction n with
  | zero => exact (transDown_refl map 0).symm
  | succ n ih =>
    rw [TorsionFreeDivisible.proj, ih, ← transDown_succ map n, transDown_comp]

private lemma iterUp_eq_transUp (i k : ℕ) :
    Stacks.Cohomology.InverseSystems.TorsionFreeDivisible.DivColim.iterUp ι i k = transUp ι
      (Nat.le_add_right i k) := by
  induction k with
  | zero => exact (transUp_refl ι i).symm
  | succ k ih =>
    rw [TorsionFreeDivisible.DivColim.iterUp, ih, ← transUp_succ ι (i + k), transUp_comp]

private lemma transUp_mono (hmono : ∀ n, Mono (ι n)) {i j : ℕ} (h : i ≤ j) :
    Mono (transUp ι h) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [← iterUp_eq_transUp ι i k]
  exact TorsionFreeDivisible.DivColim.iterUp_mono ι hmono i k

private lemma transDown_epi (hepi : ∀ n, Epi (map n)) {i j : ℕ} (h : i ≤ j) :
    Epi (transDown map h) := by
  induction j, h using Nat.le_induction with
  | base => simpa only [transDown_refl] using (inferInstance : Epi (𝟙 (obj i)))
  | succ j hij ih =>
    have hsplit : transDown map (hij.trans (Nat.le_succ j)) =
        map j ≫ transDown map hij := by
      rw [← transDown_succ map j, transDown_comp]
    rw [hsplit]
    have := hepi j
    have := ih
    exact epi_comp _ _

variable (g : End (𝟭 (SheafOfModules.{u} R)))

/-- Going down and back up the tower is multiplication by a power of `f`. -/
private lemma transDown_comp_transUp (hf : ∀ n, map n ≫ ι n = g.asHom.app (obj (n + 1)))
    (i k : ℕ) :
    transDown map (Nat.le_add_right i k) ≫ transUp ι (Nat.le_add_right i k) =
      (g ^ k).asHom.app (obj (i + k)) := by
  induction k with
  | zero => simp [transDown_refl, transUp_refl]
  | succ k ih =>
    have hd : transDown map (Nat.le_add_right i (k + 1)) =
        map (i + k) ≫ transDown map (Nat.le_add_right i k) := by
      rw [← transDown_succ map (i + k), transDown_comp]
    have hu : transUp ι (Nat.le_add_right i (k + 1)) =
        transUp ι (Nat.le_add_right i k) ≫ ι (i + k) := by
      rw [← transUp_succ ι (i + k), transUp_comp]
    rw [hd, hu, Category.assoc, ← Category.assoc _ _ (ι (i + k)), ih,
      TorsionFreeDivisible.mulF_naturality, ← Category.assoc, hf,
      TorsionFreeDivisible.mulF_pow_succ]
    rfl

private lemma transDown_comp_transUp_of_le
    (hf : ∀ n, map n ≫ ι n = g.asHom.app (obj (n + 1))) {i j : ℕ} (h : i ≤ j) :
    transDown map h ≫ transUp ι h = (g ^ (j - i)).asHom.app (obj j) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  simpa using transDown_comp_transUp map ι g hf i k

/-- Going up by `c` and then down by `i` vanishes once the tower is long enough, because
multiplication by `f^{c+1}` already kills `ℱ_{c+1}`. -/
private lemma transUp_comp_transDown_eq_zero
    (hf : ∀ n, map n ≫ ι n = g.asHom.app (obj (n + 1)))
    (hmono : ∀ n, Mono (ι n))
    (hkill : ∀ n, (g ^ (n + 1)).asHom.app (obj n) = 0)
    (c i n : ℕ) (hc : c ≤ n) (hi : i ≤ n) (hn : i + c + 1 ≤ n) :
    transUp ι hc ≫ transDown map hi = 0 := by
  have := transUp_mono ι hmono hi
  apply (cancel_mono (transUp ι hi)).1
  rw [Category.assoc, transDown_comp_transUp_of_le map ι g hf hi, zero_comp,
    ← TorsionFreeDivisible.mulF_naturality (g ^ (n - i)) (transUp ι hc)]
  have hz : (g ^ (n - i)).asHom.app (obj c) = 0 := by
    rw [show n - i = (c + 1) + (n - i - (c + 1)) by omega, pow_add]
    change (g ^ (n - i - (c + 1))).asHom.app (obj c) ≫ (g ^ (c + 1)).asHom.app (obj c) = 0
    rw [hkill, comp_zero]
  rw [hz, zero_comp]

/-- Up and down maps commute when they move the index by the same amount. -/
private lemma transUp_comp_transDown_comm
    (hf : ∀ n, map n ≫ ι n = g.asHom.app (obj (n + 1)))
    (hm : ∀ n, Mono (ι n))
    (i j k l : ℕ) (hij : i ≤ j) (hkl : k ≤ l) (hki : k ≤ i) (hlj : l ≤ j)
    (heq : j - l = i - k) :
    transUp ι hij ≫ transDown map hlj = transDown map hki ≫ transUp ι hkl := by
  have := transUp_mono ι hm hlj
  apply (cancel_mono (transUp ι hlj)).1
  rw [Category.assoc, transDown_comp_transUp_of_le map ι g hf hlj, heq,
    ← TorsionFreeDivisible.mulF_naturality (g ^ (i - k)) (transUp ι hij),
    ← transDown_comp_transUp_of_le map ι g hf hki, Category.assoc,
    Category.assoc, transUp_comp, transUp_comp]

/-- The long short exact sequences `0 → ℱ_{m+1} → ℱ_{m+n+2} → ℱ_{n+1} → 0` produced by
condition (1) of Stacks 0H39. -/
private lemma shortExact_transUp_transDown
    (hf : ∀ n, map n ≫ ι n = g.asHom.app (obj (n + 1)))
    (w : ∀ n, ι n ≫ Stacks.Cohomology.InverseSystems.TorsionFreeDivisible.proj obj map (n + 1) = 0)
    (hs : ∀ n, (ShortComplex.mk (ι n) (Stacks.Cohomology.InverseSystems.TorsionFreeDivisible.proj
      obj map (n + 1)) (w n)).ShortExact)
    (hkill : ∀ n, (g ^ (n + 1)).asHom.app (obj n) = 0)
    (hepi : ∀ n, Epi (map n)) (m n t : ℕ) (ht : t = m + n + 1)
    (hmt : m ≤ t) (hnt : n ≤ t) :
    ∃ hz : transUp ι hmt ≫ transDown map hnt = 0,
      (ShortComplex.mk _ _ hz).ShortExact := by
  subst t
  have hm : ∀ k, Mono (ι k) := fun k => (hs k).mono_f
  have hu : Mono (transUp ι hmt) := transUp_mono ι hm _
  have hd : Epi (transDown map hnt) := transDown_epi map hepi _
  have hz : transUp ι hmt ≫ transDown map hnt = 0 :=
    transUp_comp_transDown_eq_zero map ι g hf hm hkill m n _ _ _ (by omega)
  refine ⟨hz, ShortComplex.ShortExact.mk' ?_ hu hd⟩
  apply Abelian.Pseudoelement.exact_of_pseudo_exact
  intro x hx
  have hpow := transDown_comp_transUp_of_le map ι g hf hnt
  rw [show m + n + 1 - n = m + 1 by omega] at hpow
  have hxpow : Abelian.Pseudoelement.pseudoApply
      ((g ^ (m + 1)).asHom.app (obj (m + n + 1))) x = 0 := by
    rw [← hpow, Abelian.Pseudoelement.comp_apply, hx, Abelian.Pseudoelement.apply_zero]
  obtain ⟨y, hy⟩ :=
    TorsionFreeDivisible.DivColim.stabilization g map ι hf w hs m (n + 1) x hxpow
  exact ⟨y, by rwa [iterUp_eq_transUp ι m (n + 1)] at hy⟩

end Tower

attribute [-instance] SiteModules.moduleSheavesEnoughInjectives in
attribute [-instance] SiteModules.moduleSheavesGrothendieck in
attribute [-instance] SiteModules.moduleSheavesAbelian in
/-- **Stacks 0DXG.** Let `A` be a ring, `f ∈ A`, `X` a topological space and `… → ℱ₂ → ℱ₁` an
inverse system of sheaves of `A`-modules satisfying condition (1) of Stacks 0H39. If for some
`m` the image of `H^{p+1}(X, ℱ_m) → H^{p+1}(X, ℱ₁)` has finite length over `A`, or `A` is
Noetherian and the intersection of all those images is a finite `A`-module, then the inverse
system `n ↦ H^p(X, ℱ_n)` satisfies the Mittag-Leffler condition. -/
@[stacks 0DXG]
theorem isMittagLefflerCategorical_of_finite_cohomology_image
    {X : Type u} [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [∀ U, IsMulCommutative (R.obj.obj U)]
    (A : Type u) [CommRing A]
    [Algebra A (R.obj.obj (op (⊤ : Opens X)))] (f : A)
    (obj : ℕ → SheafOfModules.{u} R)
    (map : ∀ n, obj (n + 1) ⟶ obj n) (p : ℕ) :
    let E := SheafOfModules.evaluation R (op (⊤ : Opens X))
    let G := E.rightDerived (p + 1)
    letI : Module A (G.obj (obj 0)) :=
      Module.compHom (G.obj (obj 0)) (algebraMap A (R.obj.obj (op (⊤ : Opens X))))
    letI : IsScalarTower A (R.obj.obj (op (⊤ : Opens X))) (G.obj (obj 0)) :=
      ⟨fun a b x => by
        rw [Algebra.smul_def]
        change (algebraMap A (R.obj.obj (op (⊤ : Opens X))) a * b) • x =
          (algebraMap A (R.obj.obj (op (⊤ : Opens X))) a) • (b • x)
        exact mul_smul _ _ _⟩
    ((∃ n : ℕ, IsFiniteLength A
        (↥((LinearMap.range (G.map (Stacks.Cohomology.InverseSystems.TorsionFreeDivisible.proj obj
          map n)).hom).restrictScalars A))) ∨
      (IsNoetherianRing A ∧ Module.Finite A
        (↥(⨅ n : ℕ,
          (LinearMap.range (G.map (Stacks.Cohomology.InverseSystems.TorsionFreeDivisible.proj obj
            map n)).hom).restrictScalars A)))) →
      Stacks.Cohomology.InverseSystems.TorsionFreeDivisible.Condition1
        (Stacks.SheafOfModules.terminalSectionToEnd R (⊤ : Opens X) isTerminalTop
          (algebraMap A (R.obj.obj (op (⊤ : Opens X))) f)) obj map →
      IsMittagLefflerCategorical
        (Functor.ofOpSequence map ⋙ E.rightDerived p) := by
  dsimp only
  intro hfinite hcondition
  classical
  let E := SheafOfModules.evaluation R (op (⊤ : Opens X))
  let P := E.rightDerived p
  let Q := E.rightDerived (p + 1)
  let : Module A (Q.obj (obj 0)) :=
    Module.compHom _ (algebraMap A (R.obj.obj (op (⊤ : Opens X))))
  let : IsScalarTower A (R.obj.obj (op (⊤ : Opens X))) (Q.obj (obj 0)) :=
    ⟨fun a b x => by
      rw [Algebra.smul_def]
      exact mul_smul _ _ _⟩
  let g := Stacks.SheafOfModules.terminalSectionToEnd R ⊤ isTerminalTop
    (algebraMap A (R.obj.obj (op (⊤ : Opens X))) f)
  let N : Submodule A (Q.obj (obj 0)) :=
    ⨅ n, ((Q.map (TorsionFreeDivisible.proj obj map n)).hom.range).restrictScalars A
  have hNnoeth : IsNoetherian A N := by
    rcases hfinite with hfinite | ⟨hA, hfinite⟩
    · exact isNoetherian_iInf_of_finiteLength _ hfinite
    · have := hA
      have := hfinite
      exact inferInstance
  have := hNnoeth
  choose ι w hf hs using hcondition
  have hm (n : ℕ) : Mono (ι n) := (hs n).mono_f
  have hback (n : ℕ) : ι n ≫ map n = g.asHom.app (obj n) :=
    have := hm n
    comp_eq_app_of_mono g (ι n) (map n) (hf n)
  have hg0 : g.asHom.app (obj 0) = 0 := by
    rw [← hback 0]
    simpa [TorsionFreeDivisible.proj] using w 0
  have hkill := TorsionFreeDivisible.DivColim.vanishing g map ι hf hback hg0
  have hepi (n : ℕ) : Epi (map n) := by
    obtain ⟨j, hj, _, hs⟩ :=
      (TorsionFreeDivisible.stacks0H39_one_iff_two g obj map).mp (fun k => ⟨ι k, w k, hf k, hs k⟩) n
    exact hs.epi_g
  have hlong (m n : ℕ) :
      ∃ hz : transUp ι (show m ≤ n + m + 1 by omega) ≫
          transDown map (show n ≤ n + m + 1 by omega) = 0,
        (ShortComplex.mk _ _ hz).ShortExact :=
    shortExact_transUp_transDown map ι g hf w hs hkill hepi m n (n + m + 1) (by omega) _ _
  choose z hz using hlong
  let S (m n : ℕ) : ShortComplex (SheafOfModules.{u} R) :=
    ShortComplex.mk _ _ (z m n)
  have hS (m n : ℕ) : (S m n).ShortExact := hz m n
  obtain ⟨hP, δ, hex, hnat⟩ := exists_cohomology_boundary R p
  have : P.Additive := hP
  let d (n : ℕ) : P.obj (obj n) →ₗ[R.obj.obj (op (⊤ : Opens X))] Q.obj (obj 0) :=
    (δ (hS 0 n)).hom
  have hdU (c n : ℕ) (hcn : c ≤ n) (x : P.obj (obj c)) :
      d n ((P.map (transUp ι hcn)).hom x) = d c x := by
    let φ : S 0 c ⟶ S 0 n :=
      { τ₁ := 𝟙 _
        τ₂ := transUp ι (show c + 0 + 1 ≤ n + 0 + 1 by omega)
        τ₃ := transUp ι hcn
        comm₁₂ := by
          dsimp [S]
          rw [Category.id_comp, transUp_comp]
        comm₂₃ := transUp_comp_transDown_comm map ι g hf hm (c + 1) (n + 1) c n
          (by omega) hcn (by omega) (by omega) (by omega) }
    have hh := hnat (hS 0 c) (hS 0 n) φ
    change P.map (transUp ι hcn) ≫ δ (hS 0 n) =
      δ (hS 0 c) ≫ Q.map (𝟙 (obj 0)) at hh
    rw [Q.map_id, Category.comp_id] at hh
    exact congrArg (fun a => a.hom x) hh
  let L (n : ℕ) : Submodule A (Q.obj (obj 0)) := (d n).range.restrictScalars A
  have hL : Monotone L := by
    intro c n hcn x hx
    obtain ⟨y, hy⟩ := hx
    exact ⟨(P.map (transUp ι hcn)).hom y, (hdU c n hcn y).trans hy⟩
  have hLN (n : ℕ) : L n ≤ N := by
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    apply (Submodule.mem_iInf _).mpr
    intro m
    let φ : S m n ⟶ S 0 n :=
      { τ₁ := transDown map (Nat.zero_le m)
        τ₂ := transDown map (show n + 0 + 1 ≤ n + m + 1 by omega)
        τ₃ := 𝟙 _
        comm₁₂ := (transUp_comp_transDown_comm map ι g hf hm m (n + m + 1) 0 (n + 1)
          (by omega) (by omega) (by omega) (by omega) (by omega)).symm
        comm₂₃ := by
          dsimp [S]
          rw [Category.comp_id, transDown_comp] }
    have hh := hnat (hS m n) (hS 0 n) φ
    refine ⟨(δ (hS m n)).hom y, ?_⟩
    change P.map (𝟙 (obj n)) ≫ δ (hS 0 n) = δ (hS m n) ≫
      Q.map (transDown map (Nat.zero_le m)) at hh
    rw [P.map_id, Category.id_comp] at hh
    rw [proj_eq_transDown map m]
    exact congrArg (fun a => a.hom y) hh.symm
  obtain ⟨c, hc⟩ := exists_stable_of_monotone_le N L hL hLN
  refine isMittagLeffler_of_stable_boundary_ranges (Functor.ofOpSequence map ⋙ P)
    (Q.obj (obj 0)) d (fun c n h => P.map (transUp ι h))
    (fun n x hx => (ShortComplex.moduleCat_exact_iff _).mp (hex (hS 0 n)).2 x hx) hdU
    (fun c i n hc hi hn => ?_) ⟨c, fun n hn => ?_⟩
  · change P.map (transUp ι hc) ≫ P.map (transDown map hi) = 0
    rw [← P.map_comp, transUp_comp_transDown_eq_zero map ι g hf hm hkill c i n hc hi hn,
      P.map_zero]
  · ext x
    exact SetLike.ext_iff.mp (hc n hn) x

end Dxg

end Stacks.Cohomology.InverseSystems
