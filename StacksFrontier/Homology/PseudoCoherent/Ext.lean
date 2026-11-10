module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Finiteness.Projective
public import StacksFrontier.Algebra.Homology.PseudoCoherent
public import StacksFrontier.Homology.HomologyColimit
public import StacksFrontier.Homology.PseudoCoherent.Basic

@[expose] public section

/-!
# Ext out of a pseudo-coherent complex

Let `R` be a ring and let `K` be an object of the derived category `D(R)`. Two consequences of
pseudo-coherence of `K` are recorded here, and the first of them is shown to characterise it.

First, `Ext` out of `K` commutes with filtered colimits in the second variable, in the range
controlled by the pseudo-coherence bound: if `K` is `m`-pseudo-coherent and `M : ι ⥤ ModuleCat R`
is a filtered diagram of modules, then the canonical map
`colim Extⁿ(K, Mᵢ) → Extⁿ(K, colim Mᵢ)` is an isomorphism for `n < -m` and is injective for
`n = -m`. Here `Extⁿ(K, N)` is realised as the abelian group `Hom_{D(R)}(K, N[0]⟦n⟧)`, so being
an isomorphism (resp. a monomorphism) of `AddCommGrpCat` says exactly that the canonical map is
bijective (resp. injective).

Conversely, if `K` is cohomologically bounded above, this colimit property characterises
`m`-pseudo-coherence: if for every filtered diagram of modules the comparison map is bijective
for `n < -m` and injective for `n = -m`, then `K` is `m`-pseudo-coherent. Being bounded above is
expressed as the existence of an integer `b` with `K` at most `b` for the canonical t-structure.

Second, the cohomology of a pseudo-coherent complex is detected by maps to finitely presented
modules: for every `i` there is a finitely presented `R`-module `M` and a morphism
`K ⟶ M[-i]` in `D(R)` whose effect on degree-`i` cohomology is injective. The object `M[-i]` is
realised as the single complex with `M` placed in degree `i`, and the canonical identification of
its degree-`i` cohomology with `M` is folded into the asserted monomorphism.

## Main definitions

No new definitions are introduced.

## Main results

* `StacksDraft.PseudoCoherence.colimit_ext_comparison_isIso_of_lt_and_mono`: the canonical
  filtered-colimit comparison for `Ext` out of an `m`-pseudo-coherent object is an isomorphism
  below `-m` and a monomorphism at `-m`.
* `StacksDraft.PseudoCoherence.isPseudoCoherentFrom_iff_colimit_ext_comparison`: for a
  cohomologically bounded-above object, that filtered-colimit comparison property is equivalent
  to `m`-pseudo-coherence.
* `StacksDraft.PseudoCoherence.exists_finitelyPresented_module_mono_homology`: degree-`i`
  cohomology of a pseudo-coherent complex injects into a finitely presented module via a
  morphism of `D(R)`.

## References

* [Stacks Project, Tag 0G8W](https://stacks.math.columbia.edu/tag/0G8W)
* [Stacks Project, Tag 0G8X](https://stacks.math.columbia.edu/tag/0G8X)
* [Stacks Project, Tag 0G8Y](https://stacks.math.columbia.edu/tag/0G8Y)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Localization Opposite

-- We use the standard construction of the derived category of an abelian category, which
-- supplies the triangulated structure and the cohomology functors `Hⁱ`.
attribute [local instance] HasDerivedCategory.standard

open Stacks.HomologyColimit

namespace StacksDraft.PseudoCoherence

universe u v

section FilteredColimits

/-- The t-structure vanishing used for the error term of a pseudo-coherent
approximation. -/
lemma hom_eq_zero_of_isLE_of_single_shift
    {C : Type u} [Category.{v} C] [Abelian C]
    (L : DerivedCategory C) (m : ℤ) [L.IsLE (m - 1)]
    (N : C) (n : ℤ) (hn : n ≤ -m)
    (f : L ⟶ ((DerivedCategory.singleFunctor C 0).obj N)⟦n⟧) : f = 0 := by
  let : (DerivedCategory.singleFunctor C 0).obj N |>.IsGE 0 := inferInstance
  have hGE : ((DerivedCategory.singleFunctor C 0).obj N⟦n⟧).IsGE (-n) :=
    (DerivedCategory.TStructure.t).isGE_shift _ 0 n (-n) (by omega)
  exact (DerivedCategory.TStructure.t).zero_of_isLE_of_isGE f (m - 1) (-n)
    (by omega) inferInstance hGE

/-- An approximation that is an isomorphism above `m` and surjective at `m`
has a cone with homology below `m`. -/
lemma cone_isLE_of_homology_iso_and_epi
    {C : Type u} [Category.{v} C] [Abelian C]
    (T : Pretriangulated.Triangle (DerivedCategory C))
    (hT : T ∈ Pretriangulated.distinguishedTriangles) (m : ℤ)
    (hiso : ∀ i : ℤ, m < i →
      IsIso ((DerivedCategory.homologyFunctor C i).map T.mor₁))
    (hepi : Epi ((DerivedCategory.homologyFunctor C m).map T.mor₁)) :
    T.obj₃.IsLE (m - 1) := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  have hmi : m ≤ i := by omega
  have hiEpi : Epi ((DerivedCategory.homologyFunctor C i).map T.mor₁) := by
    rcases eq_or_lt_of_le hmi with rfl | hlt
    · exact hepi
    · let : IsIso ((DerivedCategory.homologyFunctor C i).map T.mor₁) := hiso i hlt
      infer_instance
  have hiMono : Mono ((DerivedCategory.homologyFunctor C (i + 1)).map T.mor₁) := by
    let : IsIso ((DerivedCategory.homologyFunctor C (i + 1)).map T.mor₁) :=
      hiso (i + 1) (by omega)
    infer_instance
  have hf : (DerivedCategory.homologyFunctor C i).map T.mor₂ = 0 :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i).mp hiEpi
  have hg : DerivedCategory.HomologySequence.δ T i (i + 1) = 0 :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT i (i + 1)).mp
      hiMono
  exact (DerivedCategory.HomologySequence.exact₃ T hT i (i + 1)).isZero_X₂ hf hg

/-- The functor `Hom(P, -)` on `R`-modules, valued in abelian groups. -/
noncomputable abbrev homF {R : Type u} [Ring R] (P : ModuleCat.{v} R) :
    ModuleCat.{v} R ⥤ AddCommGrpCat.{v} :=
  preadditiveCoyoneda.obj (op P)

/-- The canonical map `colim Hom(P, Mᵢ) → Hom(P, colim Mᵢ)` for a filtered diagram `M`. -/
noncomputable abbrev comparison {R : Type u} [Ring R]
    {ι : Type v} [Category.{v} ι] [IsFiltered ι] (P : ModuleCat.{v} R)
    (M : ι ⥤ ModuleCat.{v} R) :
    colimit (M ⋙ homF P) ⟶ (homF P).obj (colimit M) :=
  colimit.post M (homF P)

/-- The forgetful functor from `R`-modules to types preserves filtered colimits. -/
private theorem preservesColimit_forget_moduleCat {R : Type u} [Ring R]
    {ι : Type v} [Category.{v} ι] [IsFiltered ι] (M : ι ⥤ ModuleCat.{v} R) :
    PreservesColimit M (forget (ModuleCat.{v} R)) :=
  inferInstanceAs (PreservesColimit M
    ((forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}) ⋙ forget AddCommGrpCat.{v}))

/-- Finiteness of `P` lets a map out of `P` be factored through one stage of a filtered
colimit, so the comparison map is surjective. -/
lemma comparison_surjective {R : Type u} [Ring R]
    {ι : Type v} [Category.{v} ι] [IsFiltered ι] (P : ModuleCat.{v} R)
    [Module.Finite R P] [Module.Free R P] (M : ι ⥤ ModuleCat.{v} R) :
    Function.Surjective (ConcreteCategory.hom (comparison P M)) := by
  classical
  have := preservesColimit_forget_moduleCat M
  let B := Module.Free.chooseBasis R P
  let J := Module.Free.ChooseBasisIndex R P
  let : Fintype J := inferInstance
  intro f
  change (P ⟶ colimit M) at f
  have hrep : ∀ j : J, ∃ i : ι, ∃ x : M.obj i,
      (colimit.ι M i) x = f (B j) :=
    fun j => Concrete.colimit_exists_rep M (f (B j))
  choose i x hx using hrep
  let D : Discrete J ⥤ ι := Discrete.functor i
  let c := IsFiltered.cocone D
  let g : P ⟶ M.obj c.pt := ModuleCat.ofHom (B.constr ℕ fun j => (M.map (c.ι.app ⟨j⟩)) (x j))
  have hg : g ≫ colimit.ι M c.pt = f := by
    apply ModuleCat.hom_ext
    apply B.ext
    intro j
    simp only [ModuleCat.hom_comp, g, ModuleCat.hom_ofHom, LinearMap.comp_apply,
      Module.Basis.constr_basis]
    have hw := colimit.w M (c.ι.app ⟨j⟩)
    have hw' := congrArg (fun h : M.obj (i j) ⟶ colimit M =>
      (ConcreteCategory.hom h) (x j)) hw
    simpa [ModuleCat.hom_comp] using hw'.trans (hx j)
  let z : (M ⋙ homF P).obj c.pt := g
  refine ⟨(colimit.ι (M ⋙ homF P) c.pt) z, ?_⟩
  have hfac := colimit.ι_post M (homF P) c.pt
  have hz : (ConcreteCategory.hom (comparison P M))
      ((ConcreteCategory.hom (colimit.ι (M ⋙ homF P) c.pt)) z) =
      ((homF P).map (colimit.ι M c.pt)) z :=
    ConcreteCategory.congr_hom hfac z
  rw [hz]
  exact hg

/-- Finitely many elements of a stage of a filtered colimit that all die in the colimit are
killed simultaneously by a single transition map. -/
lemma dominate_finset {R : Type u} [Ring R]
    {ι : Type v} [Category.{v} ι] [IsFiltered ι]
    (M : ι ⥤ ModuleCat.{v} R) (i : ι)
    {T : Type v} (y : T → M.obj i) (s : Finset T)
    (h : ∀ x ∈ s, (colimit.ι M i) (y x) = 0) :
    ∃ (k : ι) (g : i ⟶ k), ∀ x ∈ s, (M.map g) (y x) = 0 := by
  have := preservesColimit_forget_moduleCat M
  classical
  induction s using Finset.induction with
  | empty => exact ⟨i, 𝟙 i, by simp⟩
  | insert a s ha ih =>
      obtain ⟨k, g, hk⟩ := ih (fun x hx => h x (Finset.mem_insert_of_mem hx))
      have haz : (colimit.ι M i) (y a) = 0 := h a (Finset.mem_insert_self a s)
      have h0 : (colimit.ι M i) (y a) = (colimit.ι M i) (0 : M.obj i) := by
        rw [haz, map_zero]
      rw [Concrete.colimit_rep_eq_iff_exists M (y a) (0 : M.obj i)] at h0
      obtain ⟨ka, ga, ga', hga⟩ := h0
      rw [map_zero] at hga
      let m := IsFiltered.max k ka
      let lk : k ⟶ m := IsFiltered.leftToMax k ka
      let la : ka ⟶ m := IsFiltered.rightToMax k ka
      let g1 : i ⟶ m := g ≫ lk
      let g2 : i ⟶ m := ga ≫ la
      let m' := IsFiltered.coeq g1 g2
      let e : m ⟶ m' := IsFiltered.coeqHom g1 g2
      refine ⟨m', g ≫ lk ≫ e, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxs
      · have hcond : g1 ≫ e = g2 ≫ e := IsFiltered.coeq_condition g1 g2
        have he : g ≫ lk ≫ e = ga ≫ la ≫ e := by
          simpa only [g1, g2, Category.assoc] using hcond
        rw [he]
        rw [show (M.map (ga ≫ la ≫ e)) (y x)
            = (M.map (la ≫ e)) ((M.map ga) (y x)) by
          rw [M.map_comp]; rfl]
        rw [hga, map_zero]
      · rw [show (M.map (g ≫ lk ≫ e)) (y x)
            = (M.map (lk ≫ e)) ((M.map g) (y x)) by
          rw [M.map_comp]; rfl]
        rw [hk x hxs, map_zero]

/-- A map out of a finite free `P` that dies in `Hom(P, colim Mᵢ)` already dies at some stage,
so the comparison map is injective. -/
lemma comparison_injective {R : Type u} [Ring R]
    {ι : Type v} [Category.{v} ι] [IsFiltered ι] (P : ModuleCat.{v} R)
    [Module.Finite R P] [Module.Free R P] (M : ι ⥤ ModuleCat.{v} R) :
    Function.Injective (ConcreteCategory.hom (comparison P M)) := by
  classical
  let : PreservesColimit (M ⋙ homF P) (forget AddCommGrpCat.{v}) := inferInstance
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨i, f, rfl⟩ := Concrete.colimit_exists_rep (M ⋙ homF P) z
  change (P ⟶ M.obj i) at f
  have hfac := colimit.ι_post M (homF P) i
  have hzf : (homF P).map (colimit.ι M i) f = 0 := by
    have heq := congrArg (fun (h : (M ⋙ homF P).obj i ⟶ _) =>
      (ConcreteCategory.hom h) f) hfac
    exact heq.symm.trans hz
  have hpost : (homF P).map (colimit.ι M i) f = f ≫ colimit.ι M i := rfl
  rw [hpost] at hzf
  let B := Module.Free.chooseBasis R P
  let J := Module.Free.ChooseBasisIndex R P
  let : Fintype J := inferInstance
  have hgen : ∀ j : J, (colimit.ι M i) (f (B j)) = 0 := by
    intro j
    have hh := congrArg (fun (h : P ⟶ colimit M) =>
      (ConcreteCategory.hom h) (B j)) hzf
    change (colimit.ι M i) (f (B j)) = 0 at hh
    exact hh
  obtain ⟨k, g, hg⟩ := dominate_finset M i (fun j : J => f (B j)) Finset.univ
    (fun j _ => hgen j)
  have hfg0 : f ≫ M.map g = 0 := by
    apply ModuleCat.hom_ext
    apply B.ext
    intro j
    simpa [ModuleCat.hom_comp] using hg j (Finset.mem_univ j)
  have hgoal :
      (ConcreteCategory.hom (colimit.ι (M ⋙ homF P) i)) f =
      (ConcreteCategory.hom (colimit.ι (M ⋙ homF P) i))
        (0 : (M ⋙ homF P).obj i) := by
    rw [Concrete.colimit_rep_eq_iff_exists (M ⋙ homF P) f
      (0 : (M ⋙ homF P).obj i)]
    refine ⟨k, g, g, ?_⟩
    rw [map_zero]
    change (homF P).map (M.map g) f = 0
    exact hfg0
  rw [hgoal, map_zero]

/-- `Hom(P, -)` out of a finite free module commutes with filtered colimits. -/
lemma comparison_isIso {R : Type u} [Ring R]
    {ι : Type v} [Category.{v} ι] [IsFiltered ι] (P : ModuleCat.{v} R)
    [Module.Finite R P] [Module.Free R P] (M : ι ⥤ ModuleCat.{v} R) :
    IsIso (comparison P M) :=
  (ConcreteCategory.isIso_iff_bijective (comparison P M)).2
    ⟨comparison_injective P M, comparison_surjective P M⟩

/-- For a K-projective `E`, cohomology classes of the `Hom`-complex into `M[0]` are the same
thing as morphisms `Q(E) ⟶ M[0]⟦n⟧` in `D(R)`. -/
noncomputable def cohomologyClassExtEquiv {R : Type u} [Ring R]
    (E : CochainComplex (ModuleCat.{v} R) ℤ) [E.IsKProjective]
    (M : ModuleCat.{v} R) (n : ℤ) :
    CochainComplex.HomComplex.CohomologyClass E
        ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj M) n ≃
      (DerivedCategory.Q.obj E ⟶
        ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M)⟦n⟧) := by
  let L := (CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj M
  let a := CochainComplex.HomComplex.CohomologyClass.homAddEquiv (K := E) (L := L) (n := n)
  let b := Equiv.ofBijective DerivedCategory.Qh.map
    (CochainComplex.IsKProjective.Qh_map_bijective E
      ((HomotopyCategory.quotient _ _).obj (L⟦n⟧)))
  let c := Iso.homCongr
    ((DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).symm.app E)
    ((DerivedCategory.Q.commShiftIso n).symm.app L ≪≫
      (DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).symm.app (L⟦n⟧))
  let d := Iso.homCongr (Iso.refl (DerivedCategory.Q.obj E))
    ((shiftFunctor (DerivedCategory (ModuleCat.{v} R)) n).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{v} R) 0).symm.app M))
  exact a.toEquiv.trans (b.trans (c.symm.trans d))

/-- `cohomologyClassExtEquiv` is additive. -/
noncomputable def cohomologyClassExtAddEquiv {R : Type u} [Ring R]
    (E : CochainComplex (ModuleCat.{v} R) ℤ) [E.IsKProjective]
    (M : ModuleCat.{v} R) (n : ℤ) :
    CochainComplex.HomComplex.CohomologyClass E
        ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj M) n ≃+
      (DerivedCategory.Q.obj E ⟶
        ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M)⟦n⟧) := by
  let e := cohomologyClassExtEquiv E M n
  refine { e with map_add' := ?_ }
  intro x y
  dsimp [e, cohomologyClassExtEquiv]
  simp

/-- Degree-`n` cohomology of the `Hom`-complex `Hom(E, M[0])` computes `Extⁿ(Q(E), M[0])`. -/
noncomputable def homologyExtAddEquiv {R : Type u} [Ring R]
    (E : CochainComplex (ModuleCat.{v} R) ℤ) [E.IsKProjective]
    (M : ModuleCat.{v} R) (n : ℤ) :
    (E.HomComplex ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj M)).homology n ≃+
      (DerivedCategory.Q.obj E ⟶
        ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M)⟦n⟧) :=
  (CochainComplex.HomComplex.homologyAddEquiv E _ n).trans
    (cohomologyClassExtAddEquiv E M n)

/-- `cohomologyClassExtEquiv` is natural in the target module. -/
lemma cohomologyClassExtEquiv_mk_postcomp {R : Type u} [Ring R]
    (E : CochainComplex (ModuleCat.{v} R) ℤ) [E.IsKProjective]
    {M N : ModuleCat.{v} R} (f : M ⟶ N) (n : ℤ)
    (z : CochainComplex.HomComplex.Cocycle E
      ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj M) n) :
    cohomologyClassExtEquiv E N n (CochainComplex.HomComplex.CohomologyClass.mk
      (z.postcomp ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).map f))) =
    cohomologyClassExtEquiv E M n (CochainComplex.HomComplex.CohomologyClass.mk z) ≫
      ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).map f)⟦n⟧' := by
  dsimp [cohomologyClassExtEquiv]
  simp only [CochainComplex.HomComplex.CohomologyClass.homAddEquiv_apply,
    CochainComplex.HomComplex.CohomologyClass.toHom_mk]
  simp only [Iso.homCongr_apply, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, Category.assoc]
  -- `hshift` is the naturality of `singleFunctorIsoCompQ` shifted by `n`; it is supplied to
  -- `simp` rather than used by a later `rw`, so that no rigid tactic follows the `simp`.
  have hnat := ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{v} R) 0).inv.naturality f)
  have hshift :=
    congrArg (fun h => (shiftFunctor (DerivedCategory (ModuleCat.{v} R)) n).map h) hnat
  simp only [Functor.map_comp] at hshift
  dsimp only [Functor.comp_map] at hshift
  simp [CochainComplex.HomComplex.Cocycle.equivHomShift_symm_postcomp, hshift,
    -Functor.commShiftIso_hom_naturality, -NatTrans.naturality]

/-- Postcomposition on `Hom`-complexes induced by a map of modules. -/
noncomputable def homComplexMap {R : Type u} [Ring R]
    (E : CochainComplex (ModuleCat.{v} R) ℤ) {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    E.HomComplex ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj M) ⟶
      E.HomComplex ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj N) where
  f i := AddCommGrpCat.ofHom {
    toFun z := z.comp (CochainComplex.HomComplex.Cochain.ofHom
      ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).map f)) (add_zero i)
    map_zero' := by simp [CochainComplex.HomComplex.Cochain.zero_comp]
    map_add' x y := by simp [CochainComplex.HomComplex.Cochain.add_comp]
  }
  comm' i j hij := by
    ext z
    change CochainComplex.HomComplex.δ i j
        (z.comp (CochainComplex.HomComplex.Cochain.ofHom
          ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).map f)) (add_zero i)) =
      (CochainComplex.HomComplex.δ i j z).comp
        (CochainComplex.HomComplex.Cochain.ofHom
          ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).map f)) (add_zero j)
    exact CochainComplex.HomComplex.δ_comp_ofHom z _ j

/-- The functor `M ↦ Hom(E, M[0])` from `R`-modules to cochain complexes of abelian groups. -/
noncomputable def homComplexFunctor {R : Type u} [Ring R]
    (E : CochainComplex (ModuleCat.{v} R) ℤ) :
    ModuleCat.{v} R ⥤ CochainComplex AddCommGrpCat.{v} ℤ where
  obj M := E.HomComplex ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj M)
  map f := homComplexMap E f
  map_id M := by
    apply HomologicalComplex.hom_ext
    intro i
    ext z
    change CochainComplex.HomComplex.Cochain E
      ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj M) i at z
    change z.comp (CochainComplex.HomComplex.Cochain.ofHom
      ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).map (𝟙 M)))
      (add_zero i) = z
    apply CochainComplex.HomComplex.Cochain.ext
    intro p q hpq
    rw [CochainComplex.HomComplex.Cochain.comp_zero_cochain_v]
    simp
  map_comp {M N P} f g := by
    apply HomologicalComplex.hom_ext
    intro i
    ext z
    change CochainComplex.HomComplex.Cochain E
      ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj M) i at z
    change z.comp (CochainComplex.HomComplex.Cochain.ofHom
      ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).map (f ≫ g)))
      (add_zero i) =
      (z.comp (CochainComplex.HomComplex.Cochain.ofHom
        ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).map f))
        (add_zero i)).comp
          (CochainComplex.HomComplex.Cochain.ofHom
            ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).map g))
          (add_zero i)
    apply CochainComplex.HomComplex.Cochain.ext
    intro p q hpq
    rw [CochainComplex.HomComplex.Cochain.comp_zero_cochain_v]
    simp [CochainComplex.HomComplex.Cochain.ofHom_comp]

/-- In degree `n`, the `Hom`-complex into `M[0]` is `Hom(E⁻ⁿ, M)`. -/
noncomputable def homComplexEvalIso {R : Type u} [Ring R]
    (E : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℤ) :
    homComplexFunctor E ⋙ HomologicalComplex.eval AddCommGrpCat.{v} (ComplexShape.up ℤ) n ≅
      homF (E.X (-n)) := by
  let h : -n + n = (0 : ℤ) := by omega
  refine NatIso.ofComponents (fun M =>
    (CochainComplex.HomComplex.Cochain.toSingleEquiv (K := E) (X := M) h).toAddCommGrpIso) ?_
  intro M N f
  ext z
  change CochainComplex.HomComplex.Cochain E
    ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj M) n at z
  obtain ⟨g, rfl⟩ :=
    CochainComplex.HomComplex.Cochain.toSingleMk_surjective z (-n) h
  change (CochainComplex.HomComplex.Cochain.toSingleEquiv h)
      ((CochainComplex.HomComplex.Cochain.toSingleMk g h).comp
        (CochainComplex.HomComplex.Cochain.ofHom
          ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).map f)) (add_zero n)) =
    (CochainComplex.HomComplex.Cochain.toSingleEquiv h)
      (CochainComplex.HomComplex.Cochain.toSingleMk g h) ≫ f
  rw [← CochainComplex.HomComplex.Cochain.toSingleMk_postcomp]
  simp

/-- Hom complexes out of a degreewise finite free complex commute with a filtered
colimit degree by degree. -/
private lemma preservesColimit_homComplexFunctor {R : Type u} [Ring R]
    {ι : Type v} [Category.{v} ι] [IsFiltered ι]
    (E : CochainComplex (ModuleCat.{v} R) ℤ)
    (hE : ∀ i : ℤ, Module.Finite R (E.X i) ∧ Module.Free R (E.X i))
    (M : ι ⥤ ModuleCat.{v} R) :
    PreservesColimit M (homComplexFunctor E) := by
  refine preservesColimit_of_preserves_colimit_cocone (colimit.isColimit M) ?_
  apply HomologicalComplex.isColimitOfEval
  intro n
  have : Module.Finite R (E.X (-n)) := (hE (-n)).1
  have : Module.Free R (E.X (-n)) := (hE (-n)).2
  have : PreservesColimit M (homF (E.X (-n))) :=
    let : IsIso (colimit.post M (homF (E.X (-n)))) :=
      comparison_isIso (E.X (-n)) M
    preservesColimit_of_isIso_post _ _
  have : PreservesColimit M
      (homComplexFunctor E ⋙
        HomologicalComplex.eval AddCommGrpCat.{v} (ComplexShape.up ℤ) n) :=
    preservesColimit_of_natIso M (homComplexEvalIso E n).symm
  change IsColimit
    ((homComplexFunctor E ⋙
      HomologicalComplex.eval AddCommGrpCat.{v} (ComplexShape.up ℤ) n).mapCocone
        (colimit.cocone M))
  exact isColimitOfPreserves _ (colimit.isColimit M)

/-- The cohomology of the Hom complex of a degreewise finite free complex
commutes with filtered colimits. -/
private lemma preservesColimit_homComplexCohomologyFunctor
    {R : Type u} [Ring R] {ι : Type v} [Category.{v} ι] [IsFiltered ι]
    (E : CochainComplex (ModuleCat.{v} R) ℤ)
    (hE : ∀ i : ℤ, Module.Finite R (E.X i) ∧ Module.Free R (E.X i))
    (M : ι ⥤ ModuleCat.{v} R) (n : ℤ) :
    PreservesColimit M
      (homComplexFunctor E ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℤ) n) := by
  have : HasExactColimitsOfShape ι AddCommGrpCat.{v} := inferInstance
  have : PreservesColimit M (homComplexFunctor E) :=
    preservesColimit_homComplexFunctor E hE M
  have : PreservesColimitsOfShape ι
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℤ) n) :=
    preservesColimitsOfShape_homologyFunctor (ComplexShape.up ℤ) n
  infer_instance

/-- `homologyAddEquiv` sends the class of a cycle to the cohomology class of its cocycle. -/
private lemma homologyAddEquiv_homologyπ {R : Type u} [Ring R]
    (E L : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℤ)
    (z : (E.HomComplex L).cycles n) :
    (CochainComplex.HomComplex.homologyAddEquiv E L n) ((E.HomComplex L).homologyπ n z) =
      CochainComplex.HomComplex.CohomologyClass.mk
        ((CochainComplex.HomComplex.leftHomologyData E L n).cyclesIso.hom z) :=
  ConcreteCategory.congr_hom
    (ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom ((E.HomComplex L).sc n)
      (CochainComplex.HomComplex.leftHomologyData E L n)) z

/-- `homologyExtAddEquiv` is natural in the target module. -/
private lemma homologyExtAddEquiv_naturality {R : Type u} [Ring R]
    (E : CochainComplex (ModuleCat.{v} R) ℤ) [E.IsKProjective]
    {M N : ModuleCat.{v} R} (f : M ⟶ N) (n : ℤ)
    (x : (E.HomComplex ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj M)).homology n) :
    homologyExtAddEquiv E N n
      (HomologicalComplex.homologyMap (homComplexMap E f) n x) =
      homologyExtAddEquiv E M n x ≫
        ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).map f)⟦n⟧' := by
  let L := (CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj M
  let L' := (CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj N
  let H := E.HomComplex L
  let H' := E.HomComplex L'
  let h := CochainComplex.HomComplex.leftHomologyData E L n
  let h' := CochainComplex.HomComplex.leftHomologyData E L' n
  have hπ : Function.Surjective (ConcreteCategory.hom (H.homologyπ n)) :=
    (AddCommGrpCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨z, rfl⟩ := hπ x
  let a : CochainComplex.HomComplex.Cocycle E L n := h.cyclesIso.hom z
  have hmap :
      h'.cyclesIso.hom ((HomologicalComplex.cyclesMap (homComplexMap E f) n) z) =
        a.postcomp ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).map f) := by
    apply Subtype.ext
    have h1 := ConcreteCategory.congr_hom h'.cyclesIso_hom_comp_i
      ((HomologicalComplex.cyclesMap (homComplexMap E f) n) z)
    have h2 := ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i (homComplexMap E f) n) z
    have h3 := ConcreteCategory.congr_hom h.cyclesIso_hom_comp_i z
    simp only [ConcreteCategory.comp_apply] at h1 h2 h3
    refine h1.trans ?_
    refine h2.trans ?_
    change ((HomologicalComplex.iCycles H n) z).comp _ (add_zero n) = a.1.comp _ (add_zero n)
    congr 1
  simp only [homologyExtAddEquiv, AddEquiv.trans_apply]
  have hnat := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality (homComplexMap E f) n) z
  simp only [ConcreteCategory.comp_apply] at hnat
  rw [hnat]
  rw [homologyAddEquiv_homologyπ E L n, homologyAddEquiv_homologyπ E L' n, hmap]
  exact cohomologyClassExtEquiv_mk_postcomp E f n a

/-- For a bounded finite free complex `E`, Ext out of `E` into single modules is computed
by the cohomology of the Hom complex, naturally in the module. -/
private noncomputable def extFunctorIsoHomology {R : Type u} [Ring R]
    (E : CochainComplex (ModuleCat.{v} R) ℤ) [E.IsKProjective] (n : ℤ) :
    homComplexFunctor E ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℤ) n ⋙
        AddCommGrpCat.uliftFunctor.{max u (v + 1), v} ≅
      DerivedCategory.singleFunctor (ModuleCat.{v} R) 0 ⋙
        shiftFunctor (DerivedCategory (ModuleCat.{v} R)) n ⋙
        preadditiveCoyoneda.obj (op (DerivedCategory.Q.obj E)) :=
  NatIso.ofComponents
    (fun M => (AddEquiv.ulift.trans (homologyExtAddEquiv E M n)).toAddCommGrpIso) (by
      intro M N f
      ext x
      exact homologyExtAddEquiv_naturality E f n x.down)

/-- Precomposition with `α : E ⟶ K` on `Hom(-, N⟦n⟧)`, where the cone of `α` lies
in degrees `≤ m - 1`: injective for `n ≤ -m` and surjective for `n < -m`. -/
lemma precomp_injective_surjective {C : Type u} [Category.{v} C] [Abelian C]
    {E K : DerivedCategory C} (α : E ⟶ K) (m : ℤ)
    (hcone : ∀ (Z : DerivedCategory C) (g : K ⟶ Z) (h : Z ⟶ E⟦(1 : ℤ)⟧),
      Pretriangulated.Triangle.mk α g h ∈ Pretriangulated.distinguishedTriangles →
        Z.IsLE (m - 1))
    (N : C) (n : ℤ) :
    (n ≤ -m → Function.Injective
      (fun u : K ⟶ ((DerivedCategory.singleFunctor C 0).obj N)⟦n⟧ => α ≫ u)) ∧
    (n < -m → Function.Surjective
      (fun u : K ⟶ ((DerivedCategory.singleFunctor C 0).obj N)⟦n⟧ => α ≫ u)) := by
  obtain ⟨Z, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle α
  have hZ : Z.IsLE (m - 1) := hcone Z g h hT
  constructor
  · intro hn u₁ u₂ hu
    rw [← sub_eq_zero]
    have hu' : α ≫ (u₁ - u₂) = 0 := by
      rw [Preadditive.comp_sub, sub_eq_zero]; exact hu
    set u := u₁ - u₂
    obtain ⟨w, hw⟩ := Pretriangulated.Triangle.yoneda_exact₂ _ hT u hu'
    have : w = 0 := hom_eq_zero_of_isLE_of_single_shift Z m N n hn w
    rw [hw, this, Limits.comp_zero]
  · intro hn u
    have hZ' : (Z⟦(-1 : ℤ)⟧).IsLE (m + 1 - 1) :=
      (DerivedCategory.TStructure.t).isLE_shift Z (m - 1) (-1) (m + 1 - 1) (by omega)
    obtain ⟨w, hw⟩ := Pretriangulated.Triangle.yoneda_exact₂ _
      (Pretriangulated.inv_rot_of_distTriang _ hT) u
      (hom_eq_zero_of_isLE_of_single_shift (Z⟦(-1 : ℤ)⟧) (m + 1) N n (by omega) _)
    exact ⟨w, hw.symm⟩

/-- **Stacks 0G8W.** If `K` is `m`-pseudo-coherent, then the canonical map from the
filtered colimit of `Extⁿ(K, Mᵢ)` to `Extⁿ(K, colim Mᵢ)` is an isomorphism for
`n < -m`, and is a monomorphism for `n = -m`. -/
@[stacks 0G8W]
theorem colimit_ext_comparison_isIso_of_lt_and_mono
    {R : Type u} [Ring R] {ι : Type v} [Category.{v} ι] [IsFiltered ι]
    (M : ι ⥤ ModuleCat.{v} R) (K : DerivedCategory (ModuleCat.{v} R)) (m : ℤ)
    (hK : IsPseudoCoherentFrom K m) :
    let extFunctor (n : ℤ) :=
      DerivedCategory.singleFunctor (ModuleCat.{v} R) 0 ⋙
        shiftFunctor (DerivedCategory (ModuleCat.{v} R)) n ⋙
        preadditiveCoyoneda.obj (Opposite.op K)
    (∀ n : ℤ, n < -m →
      IsIso (colimit.desc (M ⋙ extFunctor n)
        ((extFunctor n).mapCocone (colimit.cocone M)))) ∧
      Mono (colimit.desc (M ⋙ extFunctor (-m))
        ((extFunctor (-m)).mapCocone (colimit.cocone M))) := by
  intro extFunctor
  obtain ⟨E, hE, α, hiso, hepi⟩ := hK
  have : E.IsKProjective := isKProjective_of_boundedFiniteFree hE
  have hcone : ∀ (Z : DerivedCategory (ModuleCat.{v} R)) (g : K ⟶ Z)
      (h : Z ⟶ (DerivedCategory.Q.obj E)⟦(1 : ℤ)⟧),
      Pretriangulated.Triangle.mk α g h ∈ Pretriangulated.distinguishedTriangles →
        Z.IsLE (m - 1) := fun Z g h hT =>
    cone_isLE_of_homology_iso_and_epi _ hT m hiso hepi
  let extE (n : ℤ) :=
    DerivedCategory.singleFunctor (ModuleCat.{v} R) 0 ⋙
      shiftFunctor (DerivedCategory (ModuleCat.{v} R)) n ⋙
      preadditiveCoyoneda.obj (op (DerivedCategory.Q.obj E))
  let τ (n : ℤ) : extFunctor n ⟶ extE n :=
    Functor.whiskerLeft (DerivedCategory.singleFunctor (ModuleCat.{v} R) 0 ⋙
      shiftFunctor (DerivedCategory (ModuleCat.{v} R)) n) (preadditiveCoyoneda.map α.op)
  have hτ : ∀ (n : ℤ) (N : ModuleCat.{v} R),
      (n ≤ -m → Mono ((τ n).app N)) ∧ (n < -m → IsIso ((τ n).app N)) := by
    intro n N
    have key := precomp_injective_surjective α m hcone N n
    refine ⟨fun hn => ?_, fun hn => ?_⟩
    · rw [AddCommGrpCat.mono_iff_injective]
      exact key.1 hn
    · rw [ConcreteCategory.isIso_iff_bijective]
      exact ⟨key.1 hn.le, key.2 hn⟩
  have hE' : ∀ n : ℤ, IsIso (colimit.post M (extE n)) := by
    intro n
    have := preservesColimit_homComplexCohomologyFunctor E hE.finiteFree M n
    have : PreservesColimit M
        (homComplexFunctor E ⋙
          HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℤ) n ⋙
          AddCommGrpCat.uliftFunctor.{max u (v + 1), v}) :=
      comp_preservesColimit (homComplexFunctor E ⋙
          HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℤ) n)
        AddCommGrpCat.uliftFunctor.{max u (v + 1), v}
    have : PreservesColimit M (extE n) :=
      preservesColimit_of_natIso M (extFunctorIsoHomology E n)
    exact inferInstanceAs (IsIso (colimit.post M (extE n)))
  have hsq : ∀ n : ℤ, colimit.post M (extFunctor n) ≫ (τ n).app (colimit M) =
      colim.map (Functor.whiskerLeft M (τ n)) ≫ colimit.post M (extE n) := by
    intro n
    refine colimit.hom_ext fun j => ?_
    rw [colimit.ι_post_assoc, colim_map, ι_colimMap_assoc, colimit.ι_post]
    exact (τ n).naturality (colimit.ι M j)
  have := AB5OfSize_shrink.{v, v, max u (v + 1), max u (v + 1)}
    (C := AddCommGrpCat.{max u (v + 1)})
  constructor
  · intro n hn
    have : ∀ N, IsIso ((τ n).app N) := fun N => (hτ n N).2 hn
    have : ∀ j, IsIso ((Functor.whiskerLeft M (τ n)).app j) := fun j =>
      (hτ n (M.obj j)).2 hn
    have : IsIso (Functor.whiskerLeft M (τ n)) := NatIso.isIso_of_isIso_app _
    have := hE' n
    change IsIso (colimit.post M (extFunctor n))
    have h2 : IsIso (colimit.post M (extFunctor n) ≫ (τ n).app (colimit M)) := by
      rw [hsq]; infer_instance
    exact IsIso.of_isIso_comp_right _ ((τ n).app (colimit M))
  · have : ∀ N, Mono ((τ (-m)).app N) := fun N => (hτ (-m) N).1 le_rfl
    have := hE' (-m)
    have : ∀ j, Mono ((Functor.whiskerLeft M (τ (-m))).app j) := fun j =>
      (hτ (-m) (M.obj j)).1 le_rfl
    have : Mono (Functor.whiskerLeft M (τ (-m))) := NatTrans.mono_of_mono_app _
    change Mono (colimit.post M (extFunctor (-m)))
    have : Mono (colim.map (Functor.whiskerLeft M (τ (-m)))) := inferInstance
    have h2 : Mono (colimit.post M (extFunctor (-m)) ≫ (τ (-m)).app (colimit M)) := by
      rw [hsq]; exact mono_comp _ _
    exact mono_of_mono _ ((τ (-m)).app (colimit M))

end FilteredColimits

section PseudoCoherenceCriterion

open CategoryTheory.Pretriangulated

universe w

-- The witness diagram of quotients and the `Hom`-functor comparison maps below are
-- semireducible, and the `change`/`simp` steps acting on them close only under the pre-4.x
-- defeq transparency behaviour.
set_option backward.isDefEq.respectTransparency false

/-! ### Finiteness from injectivity of the Hom comparison map -/

/-- For a finite subset `E` of a module `N`, the submodule of `N` it generates. -/
private def witnessSub {R : Type u} [Ring R] (N : ModuleCat.{v} R) (E : Finset N) :
    Submodule R N :=
  Submodule.span R (E : Set N)

/-- The submodule generated by a finite subset grows with the subset. -/
private lemma witnessSub_mono {R : Type u} [Ring R] (N : ModuleCat.{v} R)
    {E E' : Finset N} (h : E ≤ E') : witnessSub N E ≤ witnessSub N E' :=
  Submodule.span_mono (by exact_mod_cast h)

/-- The filtered diagram of quotients `N / span E`, indexed by the finite subsets `E` of `N`
ordered by inclusion. -/
private noncomputable def witnessFunctor {R : Type u} [Ring R] (N : ModuleCat.{v} R) :
    Finset N ⥤ ModuleCat.{v} R where
  obj E := ModuleCat.of R (N ⧸ witnessSub N E)
  map {_ _} f := ModuleCat.ofHom (Submodule.factor (witnessSub_mono N (leOfHom f)))
  map_id E := by
    ext x
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_id, LinearMap.coe_comp, Function.comp_apply,
      Submodule.factor_mk, LinearMap.id_coe, id_eq]
  map_comp {_ _ _} f g := by
    ext x
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
      Submodule.factor_mk]

/-- The canonical projection `N ⟶ N / span E`. -/
private noncomputable def witnessProj {R : Type u} [Ring R] (N : ModuleCat.{v} R)
    (E : Finset N) : N ⟶ (witnessFunctor N).obj E :=
  ModuleCat.ofHom ((witnessSub N E).mkQ)

/-- The projections of `witnessFunctor` are compatible with the transition maps. -/
private lemma witnessProj_comp {R : Type u} [Ring R] (N : ModuleCat.{v} R)
    {E E' : Finset N} (f : E ⟶ E') :
    witnessProj N E ≫ (witnessFunctor N).map f = witnessProj N E' := by
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_comp]
  change (Submodule.factor (witnessSub_mono N (leOfHom f))) ∘ₗ (witnessSub N E).mkQ
      = (witnessSub N E').mkQ
  exact Submodule.factor_comp_mk _

/-- Every element of `N` already dies in the colimit of `witnessFunctor`, because it lies in
the submodule generated by itself. -/
private lemma witnessProj_emptyset_zero {R : Type u} [Ring R] (N : ModuleCat.{v} R) (x : N) :
    (colimit.ι (witnessFunctor N) (∅ : Finset N))
      ((witnessSub N (∅ : Finset N)).mkQ x) = 0 := by
  have hle : (∅ : Finset N) ≤ ({x} : Finset N) := by simp
  have hw := colimit.w (witnessFunctor N) (homOfLE hle)
  have key : (colimit.ι (witnessFunctor N) (∅ : Finset N))
      ((witnessSub N (∅ : Finset N)).mkQ x)
      = (colimit.ι (witnessFunctor N) ({x} : Finset N))
          ((witnessSub N ({x} : Finset N)).mkQ x) := by
    rw [← hw]
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
    congr 1
  rw [key]
  have hx : x ∈ witnessSub N ({x} : Finset N) := by
    apply Submodule.subset_span; simp
  rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr hx]
  exact map_zero _

/-- A module whose `Hom` comparison map is injective for every filtered colimit is finite. -/
private lemma finite_of_mono_colimit_post {R : Type u} [Ring R] (N : ModuleCat.{v} R)
    (h : ∀ (J : Type v) [Category.{v} J] [IsFiltered J] (F : J ⥤ ModuleCat.{v} R),
      Mono (colimit.post F (homF N))) :
    Module.Finite R N := by
  set F := witnessFunctor N
  have hfac := colimit.ι_post F (homF N) (∅ : Finset N)
  have hStepA : (colimit.post F (homF N))
      ((colimit.ι (F ⋙ homF N) (∅ : Finset N)) (witnessProj N (∅ : Finset N))) = 0 := by
    have hcm : (colimit.post F (homF N))
        ((colimit.ι (F ⋙ homF N) (∅ : Finset N)) (witnessProj N (∅ : Finset N)))
        = (homF N).map (colimit.ι F (∅ : Finset N)) (witnessProj N (∅ : Finset N)) :=
      ConcreteCategory.congr_hom hfac (witnessProj N (∅ : Finset N))
    rw [hcm]
    change witnessProj N (∅ : Finset N) ≫ colimit.ι F (∅ : Finset N) = 0
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rw [ModuleCat.hom_comp, ModuleCat.hom_zero]
    change (colimit.ι F (∅ : Finset N)) ((witnessSub N (∅ : Finset N)).mkQ x) = 0
    exact witnessProj_emptyset_zero N x
  have hmono := h (Finset N) F
  rw [AddCommGrpCat.mono_iff_injective] at hmono
  have hz0 : (colimit.ι (F ⋙ homF N) (∅ : Finset N)) (witnessProj N (∅ : Finset N)) = 0 :=
    hmono (hStepA.trans (map_zero _).symm)
  have := AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits
  have hz0' : (colimit.ι (F ⋙ homF N) (∅ : Finset N)) (witnessProj N (∅ : Finset N))
      = (colimit.ι (F ⋙ homF N) (∅ : Finset N)) 0 := by
    rw [hz0, map_zero]
  rw [Concrete.colimit_rep_eq_iff_exists (F ⋙ homF N)] at hz0'
  obtain ⟨k, f, g, hfg⟩ := hz0'
  rw [map_zero] at hfg
  have hLHS : (ConcreteCategory.hom ((F ⋙ homF N).map f)) (witnessProj N (∅ : Finset N))
      = witnessProj N k := by
    change (homF N).map (F.map f) (witnessProj N (∅ : Finset N)) = witnessProj N k
    change witnessProj N (∅ : Finset N) ≫ F.map f = witnessProj N k
    exact witnessProj_comp N f
  rw [hLHS] at hfg
  have hmkQ : (witnessSub N k).mkQ = 0 := by
    have := congrArg ModuleCat.Hom.hom hfg
    simpa [witnessProj] using this
  have htop : witnessSub N k = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : (witnessSub N k).mkQ x = 0 := by rw [hmkQ]; rfl
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
  rw [Module.finite_def, Submodule.fg_def]
  refine ⟨(k : Set N), k.finite_toSet, ?_⟩
  rwa [witnessSub] at htop

/-! ### The converse criterion -/

set_option backward.isDefEq.respectTransparency true in
/-- Injectivity of the comparison map out of a filtered colimit, elementwise. -/
private lemma mono_colimit_post_iff
    {C : Type*} [Category* C] {J : Type*} [Category* J] [IsFiltered J]
    (M : J ⥤ C) (G : C ⥤ AddCommGrpCat.{w})
    [HasColimit M] [HasColimit (M ⋙ G)]
    [PreservesColimit (M ⋙ G) (forget AddCommGrpCat.{w})] :
    Mono (colimit.post M G) ↔
      ∀ (i : J) (x : G.obj (M.obj i)), G.map (colimit.ι M i) x = 0 →
        ∃ (j : J) (f : i ⟶ j), G.map (M.map f) x = 0 := by
  rw [AddCommGrpCat.mono_iff_injective, injective_iff_map_eq_zero]
  constructor
  · intro h i x hx
    have hz : colimit.ι (M ⋙ G) i x = 0 := h _ (by
      change (colimit.ι (M ⋙ G) i ≫ colimit.post M G) x = 0
      simpa using hx)
    have hz' : colimit.ι (M ⋙ G) i x = colimit.ι (M ⋙ G) i 0 := by
      simpa using hz
    obtain ⟨j, f, g, hfg⟩ :=
      (Concrete.colimit_rep_eq_iff_exists (M ⋙ G) x 0).mp hz'
    exact ⟨j, f, by simpa only [Functor.comp_map, map_zero] using hfg⟩
  · intro h x hx
    obtain ⟨i, y, rfl⟩ := Concrete.colimit_exists_rep (M ⋙ G) x
    have hy : G.map (colimit.ι M i) y = 0 := by
      change (colimit.ι (M ⋙ G) i ≫ colimit.post M G) y = 0 at hx
      simpa using hx
    obtain ⟨j, f, hf⟩ := h i y hy
    have he : colimit.ι (M ⋙ G) i y = colimit.ι (M ⋙ G) i 0 :=
      (Concrete.colimit_rep_eq_iff_exists (M ⋙ G) y 0).mpr
        ⟨j, f, f, by simpa only [Functor.comp_map, map_zero] using hf⟩
    simpa using he

/-- The top cohomology of an object bounded above in degree `t` is corepresented by a
morphism to a module placed in degree `t`. -/
private lemma exists_top_cohomology_projection
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory C) (t : ℤ) [K.IsLE t] :
    ∃ (N : C) (q : K ⟶ (DerivedCategory.singleFunctor C t).obj N),
      IsIso ((DerivedCategory.homologyFunctor C t).map q) ∧
      ∀ (M : C), Function.Bijective
        (fun f : N ⟶ M => q ≫ (DerivedCategory.singleFunctor C t).map f) := by
  let τ := DerivedCategory.TStructure.t (C := C)
  let T := (τ.triangleLTGE t).obj K
  have hT := τ.triangleLTGE_distinguished t K
  obtain ⟨N, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
    ((τ.truncGE t).obj K) t
  let q := (τ.truncGEπ t).app K ≫ e.hom
  refine ⟨N, q, ?_, fun M => ?_⟩
  · have hm : Mono ((DerivedCategory.homologyFunctor C t).map T.mor₂) := by
      apply (DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff T hT t).mpr
      exact (DerivedCategory.isZero_of_isLE T.obj₁ (t - 1) t (by omega)).eq_of_src _ _
    have he : Epi ((DerivedCategory.homologyFunctor C t).map T.mor₂) := by
      apply (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT t (t + 1)).mpr
      exact (DerivedCategory.isZero_of_isLE T.obj₁ (t - 1) (t + 1) (by omega)).eq_of_tgt _ _
    have : IsIso ((DerivedCategory.homologyFunctor C t).map T.mor₂) :=
      isIso_of_mono_of_epi _
    change IsIso ((DerivedCategory.homologyFunctor C t).map ((τ.truncGEπ t).app K)) at this
    dsimp [q]
    rw [Functor.map_comp]
    exact IsIso.comp_isIso
  · constructor
    · intro f g hfg
      apply (DerivedCategory.singleFunctor C t).map_injective
      apply (cancel_epi e.hom).mp
      apply τ.from_truncGE_obj_ext (n := t)
      simpa [q, Category.assoc] using hfg
    · intro f
      let g := e.inv ≫ τ.descTruncGE f t
      obtain ⟨a, ha⟩ := (DerivedCategory.singleFunctor C t).map_surjective g
      refine ⟨a, ?_⟩
      simp [q, ha, g, Category.assoc, τ.π_descTruncGE]

/-- The corepresentable `Ext` functor in degree `n` out of an object of `D(R)`. -/
private noncomputable abbrev extFunctor {R : Type u} [Ring R]
    (K : DerivedCategory (ModuleCat.{v} R)) (n : ℤ) :=
  DerivedCategory.singleFunctor (ModuleCat.{v} R) 0 ⋙
    shiftFunctor (DerivedCategory (ModuleCat.{v} R)) n ⋙
    preadditiveCoyoneda.obj (Opposite.op K)

/-- Injectivity of the comparison map in degree `-t` makes the top cohomology finite. -/
private lemma finite_top_homology_of_mono_colimit_ext
    {R : Type u} [Ring R]
    (K : DerivedCategory (ModuleCat.{v} R)) (t : ℤ) [K.IsLE t]
    (h : ∀ (J : Type v) [Category.{v} J] [IsFiltered J]
      (M : J ⥤ ModuleCat.{v} R), Mono (colimit.post M (extFunctor K (-t)))) :
    Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) t).obj K) := by
  have : PreservesFilteredColimitsOfSize.{v, v}
      (forget AddCommGrpCat.{max u (v + 1)}) :=
    preservesFilteredColimitsOfSize_shrink.{v, max u (v + 1), v, max u (v + 1)} _
  obtain ⟨N, q, hq, hbij⟩ := exists_top_cohomology_projection K t
  let S := DerivedCategory.singleFunctor (ModuleCat.{v} R) t
  let e := (DerivedCategory.singleFunctors (ModuleCat.{v} R)).shiftIso (-t) t 0 (by omega)
  have hN : Module.Finite R N := by
    apply finite_of_mono_colimit_post N
    intro J _ _ M
    change Mono (colimit.post M (preadditiveCoyoneda.obj (Opposite.op N)))
    apply (mono_colimit_post_iff M (preadditiveCoyoneda.obj (Opposite.op N))).mpr
    intro i x hx
    let y : K ⟶ ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj (M.obj i))⟦-t⟧ :=
      q ≫ S.map x ≫ e.inv.app (M.obj i)
    have hnat : ∀ (Z : ModuleCat.{v} R) (g : M.obj i ⟶ Z),
        (extFunctor K (-t)).map g y = q ≫ S.map (x ≫ g) ≫ e.inv.app Z := by
      intro Z g
      change (q ≫ S.map x ≫ e.inv.app (M.obj i)) ≫
        (DerivedCategory.singleFunctor (ModuleCat.{v} R) 0 ⋙
          shiftFunctor (DerivedCategory (ModuleCat.{v} R)) (-t)).map g = _
      rw [Category.assoc, Category.assoc, ← e.inv.naturality, ← Category.assoc (S.map x),
        ← S.map_comp]
    have hy : (extFunctor K (-t)).map (colimit.ι M i) y = 0 := by
      rw [hnat]
      change x ≫ colimit.ι M i = 0 at hx
      simp [hx]
    obtain ⟨j, f, hf⟩ := (mono_colimit_post_iff M (extFunctor K (-t))).mp (h J M) i y hy
    refine ⟨j, f, ?_⟩
    change x ≫ M.map f = 0
    apply (hbij (M.obj j)).injective
    rw [hnat] at hf
    apply (cancel_mono (e.inv.app (M.obj j))).mp
    simpa [Category.assoc] using hf
  let eH : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) t).obj K ≅ N :=
    asIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) t).map q) ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{v} R) t).app N
  exact Module.Finite.equiv eH.toLinearEquiv.symm

/-- A bounded-above object with finite top cohomology is covered, in top degree, by a bounded
complex of finite free modules. -/
private lemma exists_finite_free_top_cover
    {R : Type u} [Ring R] [Small.{v} R]
    (K : DerivedCategory (ModuleCat.{v} R)) (t : ℤ)
    [Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) t).obj K)] :
    ∃ (E : CochainComplex (ModuleCat.{v} R) ℤ),
      IsBoundedFiniteFree E ∧ E.IsStrictlyLE t ∧
        ∃ q : DerivedCategory.Q.obj E ⟶ K,
          Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) t).map q) := by
  let L := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj L ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let eh : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) t).obj K ≅ L.homology t :=
    (DerivedCategory.homologyFunctor (ModuleCat.{v} R) t).mapIso e.symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) t).app L
  obtain ⟨P, hfin, hfree, f, hf⟩ := exists_finite_free_epi
    ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) t).obj K)
  obtain ⟨φ, hφ⟩ := exists_hom_from_single_of_projective L t P (f ≫ eh.hom)
  refine ⟨_, isBoundedFiniteFree_single P t, inferInstance, DerivedCategory.Q.map φ ≫ e.hom, ?_⟩
  let H := DerivedCategory.homologyFunctor (ModuleCat.{v} R) t
  let eH := DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) t
  have h : H.map (DerivedCategory.Q.map φ) =
      eH.hom.app _ ≫ HomologicalComplex.homologyMap φ t ≫ eH.inv.app _ := by
    simpa [H] using (NatIso.naturality_2 eH φ).symm
  rw [Functor.map_comp, h]
  infer_instance

/-- If both ends of a distinguished triangle are bounded above in degree `t` and the first
morphism is surjective on degree-`t` cohomology, the cone drops one degree. -/
private lemma isLE_cone_of_epi_top_homology
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _) (t : ℤ)
    [T.obj₁.IsLE t] [T.obj₂.IsLE t]
    [Epi ((DerivedCategory.homologyFunctor C t).map T.mor₁)] :
    T.obj₃.IsLE (t - 1) := by
  apply (DerivedCategory.isLE_iff _ _).mpr
  intro i hi
  have hZ := DerivedCategory.isZero_of_isLE T.obj₁ t (i + 1) (by omega)
  have hepi : Epi ((DerivedCategory.homologyFunctor C i).map T.mor₂) := by
    apply (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT i (i + 1)).mpr
    exact hZ.eq_of_tgt _ _
  by_cases hit : i = t
  · subst i
    apply (IsZero.iff_id_eq_zero _).mpr
    apply (cancel_epi ((DerivedCategory.homologyFunctor C t).map T.mor₂)).mp
    have hzero := (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT t).mp
      (inferInstance : Epi ((DerivedCategory.homologyFunctor C t).map T.mor₁))
    simp [hzero]
  · exact IsZero.of_epi ((DerivedCategory.homologyFunctor C i).map T.mor₂)
      (DerivedCategory.isZero_of_isLE T.obj₂ t i (by omega))

/-- A short complex of functors is exact as soon as it is exact at every object. -/
private lemma exact_of_exact_evaluation
    {D C : Type*} [Category* D] [Category* C] [Abelian C]
    (S : ShortComplex (D ⥤ C))
    (h : ∀ d, (S.map ((evaluation D C).obj d)).Exact) : S.Exact := by
  rw [S.exact_iff_isZero_homology]
  refine Functor.isZero _ fun d => ?_
  exact ((S.map ((evaluation D C).obj d)).exact_iff_isZero_homology.mp (h d)).of_iso
    (S.mapHomologyIso ((evaluation D C).obj d)).symm

/-- The comparison maps out of a filtered colimit are natural in the functor. -/
private lemma colimit_post_naturality
    {D : Type*} [Category* D] {J : Type*} [Category* J]
    (M : J ⥤ D) {F G : D ⥤ AddCommGrpCat.{w}} (α : F ⟶ G)
    [HasColimit M] [HasColimitsOfShape J AddCommGrpCat.{w}] :
    colim.map (Functor.whiskerLeft M α) ≫ colimit.post M G =
      colimit.post M F ≫ α.app (colimit M) := by
  apply colimit.hom_ext
  intro j
  simp only [colimit.ι_map_assoc, Functor.whiskerLeft_app,
    colimit.ι_post, colimit.ι_post_assoc]
  exact (α.naturality (colimit.ι M j)).symm

/-- The functor `d ↦ Hom(X, S d)` for a functor `S` and an object `X`. -/
private noncomputable abbrev homFunctor {D C : Type*} [Category* D] [Category* C]
    [Preadditive C] (S : D ⥤ C) (X : C) :=
  S ⋙ preadditiveCoyoneda.obj (Opposite.op X)

/-- Precomposition with a morphism, as a natural transformation of `homFunctor`s. -/
private noncomputable abbrev precomp {D C : Type*} [Category* D] [Category* C]
    [Preadditive C] (S : D ⥤ C) {X Y : C} (f : X ⟶ Y) :
    homFunctor S Y ⟶ homFunctor S X :=
  Functor.whiskerLeft S (preadditiveCoyoneda.map f.op)

/-- Exactness of `Hom(-, S d)` applied to a two-term complex which is universally exact. -/
private lemma exact_homFunctor
    {D C : Type*} [Category* D] [Category* C] [Preadditive C]
    (S : D ⥤ C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0)
    (h : ∀ d (a : Y ⟶ S.obj d), f ≫ a = 0 → ∃ b : Z ⟶ S.obj d, a = g ≫ b) :
    (ShortComplex.mk (precomp S g) (precomp S f) (by
      ext d a
      change f ≫ (g ≫ a) = 0
      rw [← Category.assoc, w, zero_comp])).Exact := by
  refine exact_of_exact_evaluation _ fun d => ?_
  rw [ShortComplex.ab_exact_iff]
  intro a ha
  obtain ⟨b, hb⟩ := h d a ha
  exact ⟨b, hb.symm⟩

/-- Four arrows are exact as a `ComposableArrows` when each consecutive pair is. -/
private lemma exact_four_arrows
    {C : Type*} [Category* C] [HasZeroMorphisms C]
    {X₀ X₁ X₂ X₃ X₄ : C}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄)
    (wab : a ≫ b = 0) (wbc : b ≫ c = 0) (wcd : c ≫ d = 0)
    (hab : (ShortComplex.mk a b wab).Exact)
    (hbc : (ShortComplex.mk b c wbc).Exact)
    (hcd : (ShortComplex.mk c d wcd).Exact) :
    (ComposableArrows.mk₄ a b c d).Exact := by
  rw [ComposableArrows.exact_iff_δ₀]
  refine ⟨hab.exact_toComposableArrows, ?_⟩
  rw [ComposableArrows.exact_iff_δ₀]
  exact ⟨hbc.exact_toComposableArrows, hcd.exact_toComposableArrows⟩

/-- The four lemma applied to the comparison maps along a distinguished triangle: the
comparison for the third object inherits monicity, resp. invertibility, from the second. -/
private lemma colimit_post_triangle
    {C : Type*} [Category.{w} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {D J : Type*} [Category* D] [Category* J]
    (M : J ⥤ D) [HasColimit M] [HasColimitsOfShape J AddCommGrpCat.{w}]
    [PreservesFiniteLimits (colim : (J ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w})]
    (S : D ⥤ C) (T : Triangle C) (hT : T ∈ distTriang C)
    [Epi (colimit.post M (homFunctor S (T.obj₂⟦(1 : ℤ)⟧)))]
    [IsIso (colimit.post M (homFunctor S (T.obj₁⟦(1 : ℤ)⟧)))]
    [IsIso (colimit.post M (homFunctor S T.obj₁))] :
    (Mono (colimit.post M (homFunctor S T.obj₂)) →
      Mono (colimit.post M (homFunctor S T.obj₃))) ∧
    (IsIso (colimit.post M (homFunctor S T.obj₂)) →
      IsIso (colimit.post M (homFunctor S T.obj₃))) := by
  let a := precomp S (-T.mor₁⟦(1 : ℤ)⟧')
  let b := precomp S T.mor₃
  let c := precomp S T.mor₂
  let d := precomp S T.mor₁
  have hab := exact_homFunctor S T.mor₃ (-T.mor₁⟦(1 : ℤ)⟧')
    (comp_distTriang_mor_zero₂₃ T.rotate (rot_of_distTriang T hT))
    (fun _ => T.rotate.yoneda_exact₃ (rot_of_distTriang T hT))
  have hbc := exact_homFunctor S T.mor₂ T.mor₃ (comp_distTriang_mor_zero₂₃ T hT)
    (fun _ => T.yoneda_exact₃ hT)
  have hcd := exact_homFunctor S T.mor₁ T.mor₂ (comp_distTriang_mor_zero₁₂ T hT)
    (fun _ => T.yoneda_exact₂ hT)
  let F : (D ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w} :=
    (Functor.whiskeringLeft J D AddCommGrpCat.{w}).obj M ⋙ colim
  let G := (evaluation D AddCommGrpCat.{w}).obj (colimit M)
  let A := ComposableArrows.mk₄ (F.map a) (F.map b) (F.map c) (F.map d)
  let B := ComposableArrows.mk₄ (G.map a) (G.map b) (G.map c) (G.map d)
  have hA : A.Exact := exact_four_arrows _ _ _ _ _ _ _
    (hab.map F) (hbc.map F) (hcd.map F)
  have hB : B.Exact := exact_four_arrows _ _ _ _ _ _ _
    (hab.map G) (hbc.map G) (hcd.map G)
  let φ : A ⟶ B := ComposableArrows.homMk₄
    (colimit.post M _) (colimit.post M _) (colimit.post M _)
    (colimit.post M _) (colimit.post M _)
    (colimit_post_naturality M a) (colimit_post_naturality M b)
    (colimit_post_naturality M c) (colimit_post_naturality M d)
  constructor
  · intro h
    exact Abelian.mono_of_epi_of_mono_of_mono
      (ComposableArrows.δlastFunctor.map φ) hA.δlast hB.δlast
      (by change Epi (colimit.post M (homFunctor S (T.obj₂⟦(1 : ℤ)⟧))); infer_instance)
      (by change Mono (colimit.post M (homFunctor S (T.obj₁⟦(1 : ℤ)⟧))); infer_instance) h
  · intro h
    exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono hA hB φ
      (by change Epi (colimit.post M (homFunctor S (T.obj₂⟦(1 : ℤ)⟧))); infer_instance)
      (by change IsIso (colimit.post M (homFunctor S (T.obj₁⟦(1 : ℤ)⟧))); infer_instance) h
      (by change Mono (colimit.post M (homFunctor S T.obj₁)); infer_instance)

/-- Shifting the target of a `homFunctor` shifts the functor instead. -/
private noncomputable def homFunctor_shiftIso
    {C : Type*} [Category* C] [Preadditive C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    {D : Type*} [Category* D] (S : D ⥤ C) (K : C) :
    homFunctor S (K⟦(1 : ℤ)⟧) ≅ homFunctor (S ⋙ shiftFunctor C (-1 : ℤ)) K := by
  let adj : shiftFunctor C (1 : ℤ) ⊣ shiftFunctor C (-1 : ℤ) :=
    (shiftEquiv C (1 : ℤ)).toAdjunction
  exact NatIso.ofComponents
    (fun d => (adj.homAddEquiv K (S.obj d)).toAddCommGrpIso)
    (by
      intro X Y f
      ext a
      exact adj.homEquiv_naturality_right a (S.map f))

/-- `Ext` out of a shifted object is `Ext` out of the object in the shifted degree. -/
private noncomputable def extFunctor_shiftIso
    {R : Type u} [Ring R] (K : DerivedCategory (ModuleCat.{v} R)) (n : ℤ) :
    extFunctor (K⟦(1 : ℤ)⟧) n ≅ extFunctor K (n - 1) :=
  homFunctor_shiftIso
      (DerivedCategory.singleFunctor (ModuleCat.{v} R) 0 ⋙ shiftFunctor _ n) K ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (DerivedCategory.singleFunctor (ModuleCat.{v} R) 0)
        (shiftFunctorAdd' (DerivedCategory (ModuleCat.{v} R)) n (-1) (n - 1) (by omega)).symm)
      (preadditiveCoyoneda.obj (Opposite.op K))

/-- Invertibility of a colimit comparison map transports along a natural isomorphism. -/
private lemma isIso_colimit_post_of_natIso
    {D J : Type*} [Category* D] [Category* J] (M : J ⥤ D)
    [HasColimit M] [HasColimitsOfShape J AddCommGrpCat.{w}]
    {F G : D ⥤ AddCommGrpCat.{w}} (e : F ≅ G) [IsIso (colimit.post M G)] :
    IsIso (colimit.post M F) := by
  have heq : colimit.post M F = colim.map (Functor.whiskerLeft M e.hom) ≫
      colimit.post M G ≫ e.inv.app (colimit M) := by
    rw [← Category.assoc, colimit_post_naturality]
    simp
  rw [heq]
  infer_instance

/-- A bounded complex of finite free modules is `m`-pseudo-coherent for every `m`. -/
private lemma isPseudoCoherentFrom_Q_of_boundedFiniteFree
    {R : Type u} [Ring R] (E : CochainComplex (ModuleCat.{v} R) ℤ)
    (hE : IsBoundedFiniteFree E) (m : ℤ) :
    IsPseudoCoherentFrom (DerivedCategory.Q.obj E) m := by
  refine ⟨E, hE, 𝟙 _, ?_, ?_⟩
  · intro i _
    rw [CategoryTheory.Functor.map_id]
    infer_instance
  · rw [CategoryTheory.Functor.map_id]
    infer_instance

/-- `Ext` out of a bounded complex of finite free modules commutes with filtered colimits in
every degree. -/
private lemma isIso_colimit_post_ext_of_boundedFiniteFree
    {R : Type u} [Ring R] {J : Type v} [Category.{v} J] [IsFiltered J]
    (M : J ⥤ ModuleCat.{v} R) (E : CochainComplex (ModuleCat.{v} R) ℤ)
    (hE : IsBoundedFiniteFree E) (n : ℤ) :
    IsIso (colimit.post M (extFunctor (DerivedCategory.Q.obj E) n)) :=
  (colimit_ext_comparison_isIso_of_lt_and_mono M
    (DerivedCategory.Q.obj E) (-n - 1)
    (isPseudoCoherentFrom_Q_of_boundedFiniteFree E hE _)).1 n (by omega)

/-- The filtered-colimit condition on `Ext` out of `K` below the bound `-m`. -/
private abbrev ExtColimitCondition {R : Type u} [Ring R]
    (K : DerivedCategory (ModuleCat.{v} R)) (m : ℤ) : Prop :=
  ∀ (J : Type v) [Category.{v} J] [IsFiltered J] (M : J ⥤ ModuleCat.{v} R),
    (∀ n : ℤ, n < -m → IsIso (colimit.post M (extFunctor K n))) ∧
      Mono (colimit.post M (extFunctor K (-m)))

/-- The colimit condition gives monicity in every degree at most `-m`. -/
private lemma mono_colimit_post_ext_of_le
    {R : Type u} [Ring R] {K : DerivedCategory (ModuleCat.{v} R)} {m : ℤ}
    (hK : ExtColimitCondition K m)
    {J : Type v} [Category.{v} J] [IsFiltered J] (M : J ⥤ ModuleCat.{v} R)
    (n : ℤ) (hn : n ≤ -m) : Mono (colimit.post M (extFunctor K n)) := by
  obtain hn | rfl := hn.lt_or_eq
  · have := (hK J M).1 n hn
    infer_instance
  · exact (hK J M).2

/-- The colimit condition passes to the cone of a morphism from a bounded complex of finite
free modules. -/
private lemma extColimitCondition_cone
    {R : Type u} [Ring R]
    (E : CochainComplex (ModuleCat.{v} R) ℤ) (hE : IsBoundedFiniteFree E)
    {K L : DerivedCategory (ModuleCat.{v} R)} {m : ℤ}
    (f : DerivedCategory.Q.obj E ⟶ K) (g : K ⟶ L)
    (h : L ⟶ (DerivedCategory.Q.obj E)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang _) (hK : ExtColimitCondition K m) :
    ExtColimitCondition L m := by
  intro J _ _ M
  have : PreservesFilteredColimitsOfSize.{v, v}
      (forget AddCommGrpCat.{max u (v + 1)}) :=
    preservesFilteredColimitsOfSize_shrink.{v, max u (v + 1), v, max u (v + 1)} _
  have := AB5OfSize_shrink.{v, v, max u (v + 1), max u (v + 1)}
    (C := AddCommGrpCat.{max u (v + 1)})
  have step (n : ℤ) (hn : n ≤ -m) :
      (Mono (colimit.post M (extFunctor K n)) →
        Mono (colimit.post M (extFunctor L n))) ∧
      (IsIso (colimit.post M (extFunctor K n)) →
        IsIso (colimit.post M (extFunctor L n))) := by
    have : IsIso (colimit.post M (extFunctor K (n - 1))) :=
      (hK J M).1 (n - 1) (by omega)
    have : IsIso (colimit.post M (extFunctor (K⟦(1 : ℤ)⟧) n)) :=
      isIso_colimit_post_of_natIso M (extFunctor_shiftIso K n)
    have : Epi (colimit.post M (extFunctor (K⟦(1 : ℤ)⟧) n)) := inferInstance
    have : IsIso (colimit.post M (extFunctor (DerivedCategory.Q.obj E) (n - 1))) :=
      isIso_colimit_post_ext_of_boundedFiniteFree M E hE (n - 1)
    have : IsIso (colimit.post M (extFunctor ((DerivedCategory.Q.obj E)⟦(1 : ℤ)⟧) n)) :=
      isIso_colimit_post_of_natIso M (extFunctor_shiftIso _ n)
    have : IsIso (colimit.post M (extFunctor (DerivedCategory.Q.obj E) n)) :=
      isIso_colimit_post_ext_of_boundedFiniteFree M E hE n
    let S := DerivedCategory.singleFunctor (ModuleCat.{v} R) 0 ⋙ shiftFunctor _ n
    let T := Triangle.mk f g h
    have : Epi (colimit.post M (homFunctor S (T.obj₂⟦(1 : ℤ)⟧))) :=
      (inferInstance : Epi (colimit.post M (extFunctor (K⟦(1 : ℤ)⟧) n)))
    have : IsIso (colimit.post M (homFunctor S (T.obj₁⟦(1 : ℤ)⟧))) :=
      (inferInstance : IsIso (colimit.post M
        (extFunctor ((DerivedCategory.Q.obj E)⟦(1 : ℤ)⟧) n)))
    have : IsIso (colimit.post M (homFunctor S T.obj₁)) :=
      (inferInstance : IsIso (colimit.post M (extFunctor (DerivedCategory.Q.obj E) n)))
    exact colimit_post_triangle M S T hT
  exact ⟨fun n hn => (step n hn.le).2 ((hK J M).1 n hn),
    (step (-m) le_rfl).1 ((hK J M).2)⟩

/-- Induction on the number of cohomological degrees between the bound `m` and the
bounded-above degree of `K`: the colimit condition implies `m`-pseudo-coherence. -/
private lemma isPseudoCoherentFrom_of_extColimitCondition
    {R : Type u} [Ring R] [Small.{v} R] (m : ℤ) (n : ℕ)
    (K : DerivedCategory (ModuleCat.{v} R)) [K.IsLE (m - 1 + n)]
    (hK : ExtColimitCondition K m) : IsPseudoCoherentFrom K m := by
  induction n generalizing K with
  | zero =>
    exact isPseudoCoherentFrom_of_homology_isZero K m
      (fun i hi => DerivedCategory.isZero_of_isLE K (m - 1 + 0) i (by omega))
  | succ n ih =>
    let t : ℤ := m + n
    have ht : m - 1 + (n + 1 : ℕ) = t := by dsimp [t]; omega
    have hKt : K.IsLE t := by simpa only [ht] using
      (inferInstance : K.IsLE (m - 1 + (n + 1 : ℕ)))
    have hfin : Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) t).obj K) :=
      finite_top_homology_of_mono_colimit_ext K t
        (fun J _ _ M => mono_colimit_post_ext_of_le hK M (-t) (by dsimp [t]; omega))
    obtain ⟨E, hE, hEt, f, hf⟩ := exists_finite_free_top_cover K t
    obtain ⟨L, g, h, hT⟩ := distinguished_cocone_triangle f
    have hLE : (DerivedCategory.Q.obj E).IsLE t := inferInstance
    have hL : L.IsLE (t - 1) :=
      @isLE_cone_of_epi_top_homology _ _ _ _ (Triangle.mk f g h) hT t hLE hKt hf
    have : L.IsLE (m - 1 + n) := by convert hL using 1; dsimp [t]; omega
    exact _root_.PseudoCoherence.isPseudoCoherent_of_distinguished_two m (Triangle.mk f g h) hT
      (isPseudoCoherentFrom_Q_of_boundedFiniteFree E hE m)
      (ih L (extColimitCondition_cone E hE f g h hT hK))

/-- **Stacks 0G8X.** A cohomologically bounded-above object `K` is `m`-pseudo-coherent if and
only if, for every filtered diagram of modules, the canonical map from the filtered colimit of
`Extⁿ(K, -)` to its value on the colimit is an isomorphism for `n < -m` and a monomorphism for
`n = -m`. -/
@[stacks 0G8X]
theorem isPseudoCoherentFrom_iff_colimit_ext_comparison
    {R : Type u} [Ring R] [Small.{v} R]
    (K : DerivedCategory (ModuleCat.{v} R)) (m : ℤ)
    (hK : ∃ n : ℤ, K.IsLE n) :
    IsPseudoCoherentFrom K m ↔
      ∀ (ι : Type v) [Category.{v} ι] [IsFiltered ι]
        (M : ι ⥤ ModuleCat.{v} R),
        let extFunctor (n : ℤ) :=
          DerivedCategory.singleFunctor (ModuleCat.{v} R) 0 ⋙
            shiftFunctor (DerivedCategory (ModuleCat.{v} R)) n ⋙
            preadditiveCoyoneda.obj (Opposite.op K)
        (∀ n : ℤ, n < -m →
          IsIso (colimit.desc (M ⋙ extFunctor n)
            ((extFunctor n).mapCocone (colimit.cocone M)))) ∧
          Mono (colimit.desc (M ⋙ extFunctor (-m))
            ((extFunctor (-m)).mapCocone (colimit.cocone M))) := by
  constructor
  · intro h ι _ _ M
    exact colimit_ext_comparison_isIso_of_lt_and_mono M K m h
  · intro h
    obtain ⟨t, ht⟩ := hK
    have : K.IsLE (m - 1 + (t - (m - 1)).toNat) :=
      DerivedCategory.TStructure.t.isLE_of_le K t _ (by omega)
    exact isPseudoCoherentFrom_of_extColimitCondition m (t - (m - 1)).toNat K h

end PseudoCoherenceCriterion

section DetectingCohomology

-- The `sc`/`sc'` normalisations for `HomologicalComplex.single` below close by `rfl` only
-- under the pre-4.x defeq transparency behaviour.
set_option backward.isDefEq.respectTransparency false

/-- A chain map is injective on derived-category cohomology exactly when it is injective on
cochain cohomology. -/
private lemma monoHomologyQMapIff {R : Type u} [Ring R]
    {E F : CochainComplex (ModuleCat.{v} R) ℤ} (i : ℤ) (f : E ⟶ F) :
    Mono ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map
      (DerivedCategory.Q.map f)) ↔
        Mono ((HomologicalComplex.homologyFunctor (ModuleCat.{v} R)
          (ComplexShape.up ℤ) i).map f) := by
  let e := DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) i
  have hn := e.hom.naturality f
  dsimp at hn
  constructor <;> intro h
  · rw [show (HomologicalComplex.homologyFunctor (ModuleCat.{v} R)
          (ComplexShape.up ℤ) i).map f =
        e.inv.app E ≫ (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map
          (DerivedCategory.Q.map f) ≫ e.hom.app F by
      calc
        _ = e.inv.app E ≫ (e.hom.app E ≫
            (HomologicalComplex.homologyFunctor (ModuleCat.{v} R)
              (ComplexShape.up ℤ) i).map f) := by simp
        _ = e.inv.app E ≫ ((DerivedCategory.homologyFunctor
            (ModuleCat.{v} R) i).map (DerivedCategory.Q.map f) ≫ e.hom.app F) := by rw [hn]
        _ = _ := rfl]
    infer_instance
  · rw [show (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map
          (DerivedCategory.Q.map f) =
        e.hom.app E ≫ (HomologicalComplex.homologyFunctor (ModuleCat.{v} R)
          (ComplexShape.up ℤ) i).map f ≫ e.inv.app F by
      calc
        _ = ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map
            (DerivedCategory.Q.map f) ≫ e.hom.app F) ≫ e.inv.app F := by simp
        _ = (e.hom.app E ≫ (HomologicalComplex.homologyFunctor
            (ModuleCat.{v} R) (ComplexShape.up ℤ) i).map f) ≫ e.inv.app F := by rw [hn]
        _ = _ := by rw [Category.assoc]]
    infer_instance

/-- **Stacks 0G8Y.** For every degree `i`, the degree-`i` cohomology of a pseudo-coherent
object of `D(R)` embeds in a finitely presented `R`-module, and the embedding is induced by a
morphism from the object to that module placed in degree `i`. -/
@[stacks 0G8Y]
theorem exists_finitelyPresented_module_mono_homology {R : Type u} [Ring R]
    (K : DerivedCategory (ModuleCat.{v} R)) (hK : IsPseudoCoherent K) (i : ℤ) :
    ∃ (M : ModuleCat.{v} R), Module.FinitePresentation R M ∧
      ∃ f : K ⟶ (DerivedCategory.singleFunctor (ModuleCat.{v} R) i).obj M,
        Mono ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map f ≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso
            (ModuleCat.{v} R) i).hom.app M) := by
  obtain ⟨E, hE, ⟨e⟩⟩ := hK
  let g : E ⟶ (HomologicalComplex.single (ModuleCat.{v} R)
      (ComplexShape.up ℤ) i).obj (E.opcycles i) :=
    HomologicalComplex.mkHomToSingle (E.pOpcycles i) (by
      intro j hj
      rw [ComplexShape.up_Rel] at hj
      subst hj
      exact E.d_pOpcycles _ _)
  refine ⟨E.opcycles i, ?_, e.inv ≫ DerivedCategory.Q.map g, ?_⟩
  · have : Module.FinitePresentation R (E.X i) :=
      have := (hE.finiteFree i).1
      have := (hE.finiteFree i).2
      Module.finitePresentation_of_projective R (E.X i)
    apply Module.finitePresentation_of_surjective (E.pOpcycles i).hom
    · exact (ModuleCat.epi_iff_surjective _).mp inferInstance
    · let S := ShortComplex.mk (E.d (i - 1) i) (E.pOpcycles i) (E.d_pOpcycles _ _)
      have hex : S.Exact := ShortComplex.exact_of_g_is_cokernel S
        (E.opcyclesIsCokernel (i - 1) i (by simp))
      have heq := hex.moduleCat_range_eq_ker
      rw [← heq]
      have := (hE.finiteFree (i - 1)).1
      exact Submodule.fg_range _
  · rw [Functor.map_comp, Category.assoc]
    have : Mono ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map e.inv) :=
      IsIso.mono_of_iso _
    have hchain : Mono (HomologicalComplex.homologyMap g i ≫
        (HomologicalComplex.singleObjHomologySelfIso
          (ComplexShape.up ℤ) i (E.opcycles i)).hom) := by
      have heq : HomologicalComplex.homologyMap g i ≫
          (HomologicalComplex.singleObjHomologySelfIso
            (ComplexShape.up ℤ) i (E.opcycles i)).hom = E.homologyι i := by
        apply (cancel_mono (HomologicalComplex.singleObjOpcyclesSelfIso
          (ComplexShape.up ℤ) i (E.opcycles i)).hom).1
        rw [Category.assoc,
          HomologicalComplex.singleObjHomologySelfIso_hom_singleObjOpcyclesSelfIso_hom]
        rw [HomologicalComplex.homologyι_naturality g i]
        congr 1
        apply (cancel_epi (E.pOpcycles i)).1
        rw [HomologicalComplex.p_opcyclesMap, HomologicalComplex.mkHomToSingle_f,
          HomologicalComplex.singleObjOpcyclesSelfIso_hom]
        simp only [Category.assoc]
      rw [heq]
      infer_instance
    have hhomology : Mono (HomologicalComplex.homologyMap g i) := by
      have := hchain
      exact mono_of_mono (HomologicalComplex.homologyMap g i)
        (HomologicalComplex.singleObjHomologySelfIso
          (ComplexShape.up ℤ) i (E.opcycles i)).hom
    have hq : Mono ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map
        (DerivedCategory.Q.map g)) := by
      apply (monoHomologyQMapIff i g).2
      rw [HomologicalComplex.homologyFunctor_map]
      exact hhomology
    have hrest : Mono ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map
        (DerivedCategory.Q.map g) ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso
          (ModuleCat.{v} R) i).hom.app (E.opcycles i)) := by
      have := hq
      infer_instance
    exact mono_comp _ _

end DetectingCohomology

end StacksDraft.PseudoCoherence

end
