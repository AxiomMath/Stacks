module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import Mathlib.Algebra.Homology.Embedding.TruncGE
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Homology.ShortComplex.Limits
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import StacksFrontier.Algebra.Homology.Embedding.TruncLEDegreewise
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import StacksFrontier.Homology.HomologyColimit
public import StacksFrontier.Homology.KFlat.Basic
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.TensorComplex.Monoidal
public import StacksFrontier.Homology.TorAmplitude.FaithfullyFlat
public import StacksFrontier.RingTheory.Module.FinitePresentation.Colimit
public import StacksCore.Tactic.StacksAttribute

@[expose] public section

/-!
# K-flatness from finitely presented modules

Let `R` be a commutative ring. A cochain complex `K` of `R`-modules is K-flat as soon as the
total complex `Tot(K ⊗_R M)` is acyclic for every *finitely presented* `R`-module `M`, regarded
as a complex concentrated in degree zero. This upgrades the defining condition of K-flatness,
which quantifies over all acyclic complexes, to a condition about single finitely presented
modules.

## Main results

* `CochainComplex.KFlat.kFlat_of_tensor_finitelyPresented_acyclic`: a cochain complex whose
  tensor product with every finitely presented module is acyclic is K-flat.

## Implementation notes

A module is regarded as a cochain complex concentrated in degree zero. The monoidal product of
cochain complexes is the total complex of the tensor-product double complex, so `L ⊗ K` is
`Tot(L ⊗_R K)`.

The reduction from an arbitrary acyclic complex `L` to single finitely presented modules
proceeds in four stages, each of which is an instance of the same principle: the functor
`L ↦ Tot(L ⊗_R K)` commutes with colimits, and a colimit of acyclic complexes taken over a
shape along which colimits are exact is acyclic (`acyclic_of_isColimit`; for
`ModuleCat R` the relevant exactness is AB5).

* An arbitrary `L` is the colimit over `ℕ` of its truncations `L.truncLE n`, the structure maps
  to `L` being isomorphisms in every fixed degree from some point on.
* A complex bounded above is the colimit over `ℕ` of the stupid truncations
  `L.stupidTrunc (ComplexShape.embeddingUpIntGE (-n))`, which are bounded on both sides.
* For a complex bounded on both sides, the tensor-product double complex has finitely many
  nonzero columns, and one induces on that number: deleting the bottom column gives a short
  exact sequence of total complexes whose outer terms are handled by the inductive hypothesis
  and by the single-column case.
* A single column is a single module, and every module is a filtered colimit of finitely
  presented modules (`Module.exists_linearEquiv_directLimit_finitePresentation`, Stacks Tag 00HA).

## References

* [The Stacks Project, Tag 0E8F](https://stacks.math.columbia.edu/tag/0E8F)
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u v

open Stacks.HomologyColimit

namespace CochainComplex.KFlat

/-- A functor into cochain complexes preserving a colimit over an exact shape sends it to an
acyclic complex as soon as it sends each term to an acyclic complex. -/
private lemma acyclic_of_isColimit {A : Type u} [Category.{v} A] [Abelian A]
    {C : Type*} [Category C] (F : C ⥤ CochainComplex A ℤ)
    {J : Type*} [Category J] [HasColimitsOfShape J A] [HasExactColimitsOfShape J A]
    (D : J ⥤ C) (c : Cocone D) (hc : IsColimit c) [PreservesColimit D F]
    (hD : ∀ j, (F.obj (D.obj j)).Acyclic) : (F.obj c.pt).Acyclic := by
  rw [HomologicalComplex.acyclic_iff]
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  let H := HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) i
  have := preservesColimitsOfShape_homologyFunctor (A := A) (J := J) (ComplexShape.up ℤ) i
  rw [IsZero.iff_id_eq_zero]
  exact (isColimitOfPreserves H (isColimitOfPreserves F hc)).hom_ext fun j ↦
    ((hD j i).isZero_homology).eq_of_src _ _

set_option backward.isDefEq.respectTransparency false in
private lemma preservesColimit_totalFunctor_eval
    {R : Type u} [CommRing R] {J : Type*} [Category J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (D : J ⥤ HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)) (n : ℤ) :
    PreservesColimit D
      (HomologicalComplex₂.totalFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⋙
        HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) n) := by
  let π : ℤ × ℤ → ℤ := (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
  let ev : (↑(π ⁻¹' {n})) →
      (HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) ⥤ ModuleCat.{u} R) :=
    fun i => HomologicalComplex.eval
      (HomologicalComplex (ModuleCat.{u} R) (ComplexShape.up ℤ))
      (ComplexShape.up ℤ) i.1.1 ⋙
      HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) i.1.2
  let B : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⥤
      (Discrete (↑(π ⁻¹' {n})) ⥤ ModuleCat.{u} R) := (Discrete.functor ev).flip
  have iso : (B ⋙ colim) ≅
      (HomologicalComplex₂.totalFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⋙
        HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) n) := by
    refine NatIso.ofComponents (fun K => ?_) ?_
    · exact (HasColimit.isoOfNatIso (F := B.obj K)
        (G := Discrete.functor (K.toGradedObject.mapObjFun π n))
        (Discrete.natIso (fun _ => Iso.refl _))).trans
        (colimit.isoColimitCocone ⟨_, K.toGradedObject.isColimitCofanMapObj π n⟩)
    intro K L f
    apply Limits.colimit.hom_ext
    intro j
    obtain ⟨⟨pq, hpq⟩⟩ := j
    have hBmap : (B.map f).app ⟨⟨pq, hpq⟩⟩ = (f.f pq.1).f pq.2 := rfl
    simp only [Functor.comp_map, Iso.trans_hom, colim_map,
      Category.assoc, ι_colimMap_assoc, HasColimit.isoOfNatIso_ι_hom_assoc,
      colimit.isoColimitCocone_ι_hom, colimit.isoColimitCocone_ι_hom_assoc,
      Discrete.natIso_hom_app, Iso.refl_hom, Category.id_comp, hBmap]
    change (f.f pq.1).f pq.2 ≫ L.toGradedObject.ιMapObj π pq n hpq
      = K.toGradedObject.ιMapObj π pq n hpq ≫
        (HomologicalComplex₂.total.map f (ComplexShape.up ℤ)).f n
    exact (K.ιTotal_map L f (ComplexShape.up ℤ) pq.1 pq.2 n hpq).symm
  have hB : PreservesColimit D B := by
    refine preservesColimit_of_evaluation _ _ (fun k => ?_)
    have h : B ⋙ (evaluation (Discrete (↑(π ⁻¹' {n}))) (ModuleCat.{u} R)).obj k =
        ev k.as := rfl
    rw [h]
    infer_instance
  have hcolim : PreservesColimit (D ⋙ B)
      (colim (J := Discrete (↑(π ⁻¹' {n}))) (C := ModuleCat.{u} R)) := inferInstance
  have hcomp : PreservesColimit D (B ⋙ colim) := comp_preservesColimit _ _
  exact preservesColimit_of_natIso _ iso

private lemma preservesColimitsOfShape_totalFunctor
    {R : Type u} [CommRing R] {J : Type*} [Category J]
    [HasColimitsOfShape J (ModuleCat.{u} R)] :
    PreservesColimitsOfShape J
      (HomologicalComplex₂.totalFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)) where
  preservesColimit {D} := by
    apply preservesColimit_of_preserves_colimit_cocone (colimit.isColimit D)
    refine HomologicalComplex.isColimitOfEval _ _ (fun n => ?_)
    have := preservesColimit_totalFunctor_eval D n
    exact isColimitOfPreserves
      (HomologicalComplex₂.totalFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⋙
        HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) n)
      (colimit.isColimit D)

private noncomputable abbrev tensorComplexLeftFunctor {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  ((curriedTensor (ModuleCat.{u} R)).mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K ⋙
    HomologicalComplex₂.totalFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)

private lemma tensorComplexLeftFunctor_eq_TleftCochain {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    tensorComplexLeftFunctor K = TleftCochain K := by
  apply CategoryTheory.Functor.ext
  · intro L
    intro M f
    let B := (curriedTensor (ModuleCat.{u} R)).mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    change (HomologicalComplex₂.totalFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map ((B.obj K).map f) =
      HomologicalComplex₂.total.map ((B.map (𝟙 K)).app L ≫ (B.obj K).map f)
        (ComplexShape.up ℤ)
    rw [B.map_id]
    simp
    rfl
  · intro L
    rfl

private lemma preservesColimitsOfShape_tensorComplexLeftFunctor
    {R : Type u} [CommRing R] {J : Type*} [Category J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    PreservesColimitsOfShape J (tensorComplexLeftFunctor K) := by
  have hpre : PreservesColimitsOfShape J
      (((curriedTensor (ModuleCat.{u} R)).mapBifunctorHomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K) := by
    refine ⟨fun {D} => preservesColimit_of_preserves_colimit_cocone
      (colimit.isColimit D) ?_⟩
    refine HomologicalComplex.isColimitOfEval _ _ (fun p => ?_)
    have : PreservesColimitsOfShape J
        ((curriedTensor (ModuleCat.{u} R)).obj (K.X p)) := inferInstance
    have : PreservesColimitsOfShape J
        (((curriedTensor (ModuleCat.{u} R)).obj (K.X p)).mapHomologicalComplex
          (ComplexShape.up ℤ)) := inferInstance
    exact isColimitOfPreserves
      (((curriedTensor (ModuleCat.{u} R)).obj (K.X p)).mapHomologicalComplex
        (ComplexShape.up ℤ)) (colimit.isColimit D)
  have htot : PreservesColimitsOfShape J
      (HomologicalComplex₂.totalFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)) :=
    preservesColimitsOfShape_totalFunctor
  exact comp_preservesColimitsOfShape _ _

private lemma acyclic_tensor_single_of_finitelyPresented
    {R : Type u} [CommRing R] (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : ∀ M : ModuleCat.{u} R, Module.FinitePresentation R M →
      (K ⊗ (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj M).Acyclic)
    (M : ModuleCat.{u} R) :
    (K ⊗ (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj M).Acyclic := by
  classical
  obtain ⟨ι, _, _, _, _, G, _, _, f, _, hG, ⟨e⟩⟩ :=
    Module.exists_linearEquiv_directLimit_finitePresentation R M
  let D : ι ⥤ ModuleCat.{u} R := ModuleCat.directLimitDiagram G f
  let c : Cocone D := ModuleCat.directLimitCocone G f
  have hc : IsColimit c := ModuleCat.directLimitIsColimit G f
  let S := HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0
  let F := S ⋙ tensorComplexLeftFunctor K
  have : PreservesColimit D S := inferInstance
  have : PreservesColimitsOfShape ι (tensorComplexLeftFunctor K) :=
    preservesColimitsOfShape_tensorComplexLeftFunctor K
  exact HomologicalComplex.Acyclic.of_iso (F.mapIso (e.toModuleIso : M ≅ c.pt)).symm
    (acyclic_of_isColimit F D c hc fun j ↦ hK (D.obj j) (hG j))

private lemma acyclic_shift {R : Type u} [CommRing R]
    (W : CochainComplex (ModuleCat.{u} R) ℤ) (hW : W.Acyclic) (a : ℤ) :
    ((CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) a).obj W).Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact IsZero.of_iso ((hW (i + a)).isZero_homology)
    ((CochainComplex.ShiftSequence.shiftIso (ModuleCat.{u} R) a i (i + a)
      (add_comm a i)).app W)

private lemma acyclic_totalSingleColumn {R : Type u} [CommRing R]
    (W : CochainComplex (ModuleCat.{u} R) ℤ) (hW : W.Acyclic) (a : ℤ) :
    ((StacksDraft.TotalComplexQuasiIso.singleColumn W a).total (ComplexShape.up ℤ)).Acyclic := by
  let := StacksDraft.TotalComplexQuasiIso.hasTotal_singleColumn W a
  have := StacksDraft.TotalComplexQuasiIso.isIso_totalSingleColumnUnit W a
  exact HomologicalComplex.Acyclic.of_iso
    (asIso (StacksDraft.TotalComplexQuasiIso.totalSingleColumnUnit W a))
    (acyclic_shift W hW (-a))

private lemma acyclic_total_of_bounded_acyclic_columns_aux {R : Type u} [CommRing R]
    (m : ℕ) : ∀ (a : ℤ)
    (Z : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℤ) (ComplexShape.up ℤ)),
    (∀ p, (p < a ∨ a + (m : ℤ) ≤ p) → IsZero (Z.X p)) →
    (∀ p, (Z.X p).Acyclic) →
    (Z.total (ComplexShape.up ℤ)).Acyclic := by
  induction m with
  | zero =>
    intro a Z hZ _
    have hz : IsZero Z := by
      rw [IsZero.iff_id_eq_zero]
      exact HomologicalComplex.Hom.ext (funext fun p ↦ (hZ p (by omega)).eq_of_src _ _)
    exact HomologicalComplex.acyclic_of_isZero _
      (Functor.map_isZero
        (HomologicalComplex₂.totalFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (ComplexShape.up ℤ)) hz)
  | succ m ih =>
    intro a Z hZ hcol
    have hz : IsZero (Z.X (a - 1)) := hZ _ (Or.inl (by omega))
    let P := StacksDraft.TotalComplexQuasiIso.bottomProj Z a hz
    let := StacksDraft.TotalComplexQuasiIso.hasTotal_singleColumn (Z.X a) a
    have hker : ∀ p, (p < a + 1 ∨ a + 1 + (m : ℤ) ≤ p) →
        IsZero ((kernel P).X p) := by
      intro p hp
      rcases hp with hp | hp
      · exact StacksDraft.TotalComplexQuasiIso.isZero_bottomTrunc_X a hz
          (fun j hj => hZ j (Or.inl hj)) p hp
      · exact StacksDraft.TotalComplexQuasiIso.isZero_kernel_bottomProj_X Z a hz p
          (hZ p (Or.inr (by omega)))
    have hacKer : ∀ p, ((kernel P).X p).Acyclic := by
      intro p
      by_cases hp : p = a
      · subst p
        exact HomologicalComplex.acyclic_of_isZero _
          (StacksDraft.TotalComplexQuasiIso.isZero_kernel_bottomProj_X_self Z a hz)
      · have hi := StacksDraft.TotalComplexQuasiIso.isIso_kernel_ι_bottomProj_f
          Z a hz p hp
        exact HomologicalComplex.Acyclic.of_iso
          (asIso ((kernel.ι P).f p)).symm (hcol p)
    exact (StacksDraft.TotalComplexQuasiIso.totalBottomSES_shortExact Z a hz).acyclic_X₂
      (ih (a + 1) (kernel P) hker hacKer) (acyclic_totalSingleColumn (Z.X a) (hcol a) a)

private lemma acyclic_total_of_bounded_acyclic_columns {R : Type u} [CommRing R]
    (Z : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (a b : ℤ) (hbound : ∀ p, (p < a ∨ b < p) → IsZero (Z.X p))
    (hcol : ∀ p, (Z.X p).Acyclic) :
    (Z.total (ComplexShape.up ℤ)).Acyclic := by
  let m : ℕ := (b - a + 1).toNat
  have hm : b < a + (m : ℤ) := by
    dsimp [m]
    omega
  exact acyclic_total_of_bounded_acyclic_columns_aux m a Z
    (fun p hp ↦ hbound p (hp.imp id fun _ ↦ by omega)) hcol

private lemma acyclic_tensor_left_module {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : ∀ M : ModuleCat.{u} R, Module.FinitePresentation R M →
      (K ⊗ (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj M).Acyclic)
    (M : ModuleCat.{u} R) :
    (((MonoidalCategory.tensorLeft M).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic :=
      by
  obtain ⟨s, -⟩ := TotalTensorComplex.cochainComplex_symmetricMonoidalCategory R
  let S := (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj M
  exact HomologicalComplex.Acyclic.of_iso
    (StacksDraft.TorAmplitude.FaithfullyFlat.singleTensorLeftMapHomologicalComplexIso M K)
    (HomologicalComplex.Acyclic.of_iso (s.toBraidedCategory.braiding K S)
      (acyclic_tensor_single_of_finitelyPresented K hK M))

private lemma acyclic_tensor_bounded {R : Type u} [CommRing R]
    (K L : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : ∀ M : ModuleCat.{u} R, Module.FinitePresentation R M →
      (K ⊗ (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj M).Acyclic)
    (a b : ℤ) (hL : ∀ p, (p < a ∨ b < p) → IsZero (L.X p)) :
    (L ⊗ K).Acyclic := by
  let Z := (((curriedTensor (ModuleCat.{u} R)).mapBifunctorHomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj L).obj K
  have hbound : ∀ p, (p < a ∨ b < p) → IsZero (Z.X p) := by
    intro p hp
    rw [IsZero.iff_id_eq_zero]
    exact HomologicalComplex.Hom.ext (funext fun q ↦
      (((curriedTensor (ModuleCat.{u} R)).flip.obj (K.X q)).map_isZero (hL p hp)).eq_of_src _ _)
  exact acyclic_total_of_bounded_acyclic_columns Z a b hbound
    fun p ↦ acyclic_tensor_left_module K hK (L.X p)

private lemma stupidTrunc_d_eq {R : Type u} [CommRing R]
    (L : CochainComplex (ModuleCat.{u} R) ℤ)
    (e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℤ)) [e.IsRelIff]
    {i j : ℕ} {i' j' : ℤ} (hi : e.f i = i') (hj : e.f j = j') :
    (L.stupidTrunc e).d i' j' =
      (L.stupidTruncXIso e hi).hom ≫ L.d i' j' ≫
        (L.stupidTruncXIso e hj).inv := by
  subst hi hj
  have h₁ : ∀ {Z : ModuleCat.{u} R}
      (h : (L.restriction e).X i = L.X (e.f i)) (g : L.X (e.f i) ⟶ Z),
      eqToHom h ≫ g = g := fun _ g => Category.id_comp g
  have h₂ : ∀ {Z : ModuleCat.{u} R}
      (h : L.X (e.f j) = (L.restriction e).X j)
      (g : (L.restriction e).X j ⟶ Z), eqToHom h ≫ g = g :=
    fun _ g => Category.id_comp g
  simp [HomologicalComplex.stupidTrunc, HomologicalComplex.stupidTruncXIso,
    (L.restriction e).extend_d_eq e rfl rfl, h₁, h₂]
  rfl

open Classical in
private noncomputable def ιStupidTruncf {R : Type u} [CommRing R]
    (L : CochainComplex (ModuleCat.{u} R) ℤ)
    (e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℤ)) [e.IsRelIff]
    (i' : ℤ) : (L.stupidTrunc e).X i' ⟶ L.X i' :=
  if hi' : ∃ i, e.f i = i' then (L.stupidTruncXIso e hi'.choose_spec).hom else 0

private lemma ιStupidTruncf_eq {R : Type u} [CommRing R]
    (L : CochainComplex (ModuleCat.{u} R) ℤ)
    (e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℤ)) [e.IsRelIff]
    {i : ℕ} {i' : ℤ} (hi' : e.f i = i') :
    ιStupidTruncf L e i' = (L.stupidTruncXIso e hi').hom := by
  have h : ∃ k, e.f k = i' := ⟨i, hi'⟩
  have : h.choose = i := e.injective_f (by rw [h.choose_spec, hi'])
  grind [ιStupidTruncf]

private noncomputable def ιStupidTrunc {R : Type u} [CommRing R]
    (L : CochainComplex (ModuleCat.{u} R) ℤ)
    (e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℤ)) [e.IsTruncGE] :
    L.stupidTrunc e ⟶ L where
  f i' := ιStupidTruncf L e i'
  comm' i' j' hij' := by
    by_cases hi' : ∃ i, e.f i = i'
    · obtain ⟨i, hi⟩ := hi'
      obtain ⟨j, hj⟩ := e.mem_next (by rw [hi]; exact hij')
      rw [ιStupidTruncf_eq L e hi, ιStupidTruncf_eq L e hj,
        stupidTrunc_d_eq L e hi hj]
      simp
    · exact (L.isZero_stupidTrunc_X e i' (by simpa using hi')).eq_of_src _ _

private lemma isIso_ιStupidTrunc_f {R : Type u} [CommRing R]
    (L : CochainComplex (ModuleCat.{u} R) ℤ)
    (e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℤ)) [e.IsTruncGE]
    {i : ℕ} {i' : ℤ} (hi' : e.f i = i') :
    IsIso ((ιStupidTrunc L e).f i') := by
  change IsIso (ιStupidTruncf L e i')
  rw [ιStupidTruncf_eq L e hi']
  infer_instance

private noncomputable abbrev lowerTrunc {R : Type u} [CommRing R]
    (L : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) :=
  L.stupidTrunc (ComplexShape.embeddingUpIntGE (-(n : ℤ)))

private lemma lowerMapSucc_hasLift {R : Type u} [CommRing R]
    (L : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) :
    (ComplexShape.embeddingUpIntGE (-((n + 1 : ℕ) : ℤ))).HasLift
      (HomologicalComplex.restrictionMap
        (ιStupidTrunc L (ComplexShape.embeddingUpIntGE (-(n : ℤ))))
        (ComplexShape.embeddingUpIntGE (-((n + 1 : ℕ) : ℤ)))) := by
  let e := ComplexShape.embeddingUpIntGE (-((n + 1 : ℕ) : ℤ))
  let φ := HomologicalComplex.restrictionMap
    (ιStupidTrunc L (ComplexShape.embeddingUpIntGE (-(n : ℤ)))) e
  change e.HasLift φ
  intro j hj i' hij'
  obtain rfl : j = 0 := (ComplexShape.boundaryGE_embeddingUpIntGE_iff _ _).1 hj
  have hz : IsZero ((lowerTrunc L n).X (e.f 0)) := by
    apply L.isZero_stupidTrunc_X
    intro k
    simp only [e, ComplexShape.embeddingUpIntGE_f, Nat.cast_zero, add_zero]
    omega
  rw [hz.eq_of_tgt ((lowerTrunc L n).d i' (e.f 0)) 0]
  exact zero_comp

set_option backward.isDefEq.respectTransparency false in
private noncomputable def lowerMapSucc {R : Type u} [CommRing R]
    (L : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) :
    lowerTrunc L n ⟶ lowerTrunc L (n + 1) :=
  (ComplexShape.embeddingUpIntGE (-((n + 1 : ℕ) : ℤ))).liftExtend
    (HomologicalComplex.restrictionMap
      (ιStupidTrunc L (ComplexShape.embeddingUpIntGE (-(n : ℤ))))
      (ComplexShape.embeddingUpIntGE (-((n + 1 : ℕ) : ℤ))))
    (lowerMapSucc_hasLift L n)

set_option backward.isDefEq.respectTransparency false in
private lemma lowerMapSucc_comp_ι {R : Type u} [CommRing R]
    (L : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) :
    lowerMapSucc L n ≫
      ιStupidTrunc L (ComplexShape.embeddingUpIntGE (-((n + 1 : ℕ) : ℤ))) =
      ιStupidTrunc L (ComplexShape.embeddingUpIntGE (-(n : ℤ))) := by
  let e₀ := ComplexShape.embeddingUpIntGE (-(n : ℤ))
  let e₁ := ComplexShape.embeddingUpIntGE (-((n + 1 : ℕ) : ℤ))
  refine HomologicalComplex.Hom.ext (funext fun i ↦ ?_)
  by_cases hi : i < -(n : ℤ)
  · exact (L.isZero_stupidTrunc_X e₀ i
      (by
        intro k
        change -(n : ℤ) + (k : ℤ) ≠ i
        omega)).eq_of_src _ _
  · let j : ℕ := (i + ((n + 1 : ℕ) : ℤ)).toNat
    have hj : e₁.f j = i := by
      change -((n + 1 : ℕ) : ℤ) + (j : ℤ) = i
      dsimp [j]
      omega
    change (lowerMapSucc L n).f i ≫ (ιStupidTrunc L e₁).f i =
      (ιStupidTrunc L e₀).f i
    rw [show (ιStupidTrunc L e₁).f i = (L.stupidTruncXIso e₁ hj).hom from
      ιStupidTruncf_eq L e₁ hj]
    change
      (e₁.liftExtend
          (HomologicalComplex.restrictionMap (ιStupidTrunc L e₀) e₁)
          (lowerMapSucc_hasLift L n)).f i ≫
        ((L.restriction e₁).extendXIso e₁ hj).hom ≫
          (L.restrictionXIso e₁ hj).hom = ιStupidTruncf L e₀ i
    rw [ComplexShape.Embedding.liftExtend_f (hi := hj),
      HomologicalComplex.restrictionMap_f' (hi := hj)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [Iso.inv_hom_id, Category.comp_id]
    rfl

private noncomputable def lowerSequence {R : Type u} [CommRing R]
    (L : CochainComplex (ModuleCat.{u} R) ℤ) :
    ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  Functor.ofSequence (lowerMapSucc L)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def lowerCocone {R : Type u} [CommRing R]
    (L : CochainComplex (ModuleCat.{u} R) ℤ) : Cocone (lowerSequence L) :=
  Cocone.mk L
    (NatTrans.ofSequence (F := lowerSequence L)
      (G := (Functor.const ℕ).obj L)
      (fun n => ιStupidTrunc L (ComplexShape.embeddingUpIntGE (-(n : ℤ))))
      (fun n => by
        simpa [lowerSequence] using lowerMapSucc_comp_ι L n))

private noncomputable def lowerCocone_isColimit {R : Type u} [CommRing R]
    (L : CochainComplex (ModuleCat.{u} R) ℤ) :
    IsColimit (lowerCocone L) := by
  apply isColimit_of_eventually_iso_components
  intro i
  refine ⟨(-i).toNat, fun n hn ↦ ?_⟩
  let j : ℕ := (i + (n : ℤ)).toNat
  have hj : (ComplexShape.embeddingUpIntGE (-(n : ℤ))).f j = i := by
    change -(n : ℤ) + (j : ℤ) = i
    dsimp [j]
    have h := Int.self_le_toNat (-i)
    omega
  exact isIso_ιStupidTrunc_f L _ hj

private lemma exactNatColimitsModuleCat {R : Type u} [CommRing R] :
    HasExactColimitsOfShape ℕ (ModuleCat.{u} R) := by
  have : AB5OfSize.{0,0,u,u+1} (ModuleCat.{u} R) := AB5OfSize_of_univLE.{0,0,u,u} (ModuleCat.{u} R)
  exact AB5OfSize.ofShape ℕ

private lemma acyclic_tensor_of_isColimit {R : Type u} [CommRing R]
    {J : Type*} [Category J] [HasColimitsOfShape J (ModuleCat.{u} R)]
    [HasExactColimitsOfShape J (ModuleCat.{u} R)]
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (D : J ⥤ CochainComplex (ModuleCat.{u} R) ℤ)
    (c : Cocone D) (hc : IsColimit c)
    (hD : ∀ j, (D.obj j ⊗ K).Acyclic) : (c.pt ⊗ K).Acyclic := by
  obtain ⟨s, -⟩ := TotalTensorComplex.cochainComplex_symmetricMonoidalCategory R
  let F := tensorComplexLeftFunctor K
  have : PreservesColimitsOfShape J F :=
    preservesColimitsOfShape_tensorComplexLeftFunctor K
  exact HomologicalComplex.Acyclic.of_iso (s.toBraidedCategory.braiding K c.pt)
    (acyclic_of_isColimit F D c hc fun j ↦
      HomologicalComplex.Acyclic.of_iso (s.toBraidedCategory.braiding (D.obj j) K) (hD j))

private lemma acyclic_tensor_of_bounded_above {R : Type u} [CommRing R]
    (K L : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : ∀ M : ModuleCat.{u} R, Module.FinitePresentation R M →
      (K ⊗ (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj M).Acyclic)
    (b : ℤ) [L.IsStrictlyLE b] : (L ⊗ K).Acyclic := by
  let : HasExactColimitsOfShape ℕ (ModuleCat.{u} R) := exactNatColimitsModuleCat
  exact acyclic_tensor_of_isColimit K (lowerSequence L) (lowerCocone L) (lowerCocone_isColimit L)
    fun n ↦ acyclic_tensor_bounded K (lowerTrunc L n) hK (-(n : ℤ)) b fun p hp ↦ hp.elim
      (fun h ↦ CochainComplex.isZero_of_isStrictlyGE (lowerTrunc L n) (-(n : ℤ)) p h)
      (fun h ↦ CochainComplex.isZero_of_isStrictlyLE (lowerTrunc L n) b p h)

/-- **Stacks 0E8F.** A cochain complex whose tensor product with every finitely presented module
is acyclic is K-flat. -/
@[stacks 0E8F]
public theorem kFlat_of_tensor_finitelyPresented_acyclic {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : ∀ M : ModuleCat.{u} R, Module.FinitePresentation R M →
      (K ⊗ (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj M).Acyclic) :
    K.KFlat := by
  intro L _
  let : HasExactColimitsOfShape ℕ (ModuleCat.{u} R) := exactNatColimitsModuleCat
  exact acyclic_tensor_of_isColimit K (truncLESequence L) (truncLECocone L)
    (truncLECocone_isColimit L) fun n ↦ acyclic_tensor_of_bounded_above K (L.truncLE (n : ℤ)) hK n

end CochainComplex.KFlat

end
