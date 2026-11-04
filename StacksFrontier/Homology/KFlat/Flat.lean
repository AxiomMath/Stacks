module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.BifunctorFlip
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Data.Int.Interval
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.CategoryTheory
public import StacksCore.Algebra.Homology.TotalComplex
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.Embedding.TruncLEDegreewise
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex
public import StacksFrontier.Homology.KFlat.LargeUniverse
import StacksFrontier.CategoryTheory.Limits.FunctorCategory.ShortExactColimit

@[expose] public section

/-!
# Two sources of K-flat complexes: flat terms and filtered colimits

Let `R` be a commutative ring. This file proves the two basic recognition principles for
K-flatness of a cochain complex of `R`-modules (Stacks 06XZ): a bounded above complex of flat
modules is K-flat, and K-flatness is preserved by filtered colimits.

## Main results

* `CochainComplex.KFlat.kFlat_of_flat`: a bounded above cochain complex whose terms are flat
  `R`-modules is K-flat.
* `CochainComplex.KFlat.kFlat_colimit`: a filtered colimit of K-flat cochain complexes of
  `R`-modules is K-flat.

## Implementation notes

The ring `R` and its modules inhabit independent universes: `R : Type u` and the modules
`Type (max u v)`. K-flatness at that generality is `CochainComplex.KFlat`, whose monoidal
product is the total complex of the tensor product double complex, so `M ⊗ K` is
`Tot(M ⊗_R K)`. The tensor bifunctor is the ordinary tensor product of modules in every case,
only the unit being `ULift.{v} R` rather than `R`, so at `v = u` both statements below are the
same propositions as their same-universe readings. Boundedness above is
`HomologicalComplex.IsStrictlyLE`, and acyclicity is `HomologicalComplex.Acyclic`, i.e.
exactness in every degree.

Both proofs run through one shared toolkit, which is the reason the two results live together:
colimits of cochain complexes are computed degreewise, and in `ModuleCat R` filtered colimits
are exact, so an `ℕ`- or filtered-indexed colimit of acyclic complexes is acyclic
(`acyclic_colimit`); and the total complex of the tensor product double complex commutes with
such colimits in either variable (`preservesColimit_mapBifunctorObj` together with
`preservesColimit_totalFunctor`, whose ingredient is that `- ⊗ X` is a left adjoint).

For `kFlat_of_flat` the colimit used is the tower of truncations `L.truncLE n` of the acyclic
complex `L`, which exhausts `L` because `(L.ιTruncLE b).f i` is an isomorphism for `i < b`.
Each `Tot(L^{≤ n} ⊗_R P)` is acyclic by the spectral sequence of the tensor product double
complex: the complex is bounded above in both directions, hence has finite diagonals, and its
columns `L^{≤ n} ⊗_R P^q` are acyclic because `P^q` is flat. `total_acyclic_of_columns` wires
this through the promoted convergence statement
`HomologicalComplex₂.isBounded_and_converges_totalFiltration₁` (Stacks 0132), taking the weak
Serre class to be the objects that are zero and reading off the first page through
`HomologicalComplex₂.exists_iso_pages_totalFiltration₁` (Stacks 0130), where it is the
column-wise homology.

For `kFlat_colimit` the index category `J` lives in universes unrelated to the modules and is
only required to be essentially small relative to the module universe; exactness of
`J`-colimits in the module category is transported from the small model of `J`.

## References

* [The Stacks Project, Tag 064K](https://stacks.math.columbia.edu/tag/064K)
* [The Stacks Project, Tag 06Y3](https://stacks.math.columbia.edu/tag/06Y3)
-/

open CategoryTheory MonoidalCategory Limits

universe u v w x

namespace CochainComplex.KFlat

/-! ### Flatness and acyclicity, degreewise -/

private lemma tensorRight_acyclic {R : Type u} [CommRing R]
    (L : CochainComplex (ModuleCat.{max u v} R) ℤ) (M : ModuleCat.{max u v} R)
    [Module.Flat R M] (hL : L.Acyclic) :
    ((tensorRight M).mapHomologicalComplex (ComplexShape.up ℤ)).obj L |>.Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff, ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  exact Module.Flat.rTensor_exact M
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (L.sc i)).1 (hL i))

private lemma acyclic_truncLE {R : Type u} [CommRing R]
    (L : CochainComplex (ModuleCat.{max u v} R) ℤ) (m : ℤ)
    (hL : L.Acyclic) : (L.truncLE m).Acyclic := by
  rw [L.acyclic_truncLE_iff m (m + 1), L.isGE_iff]
  exact fun i _ => hL i

/-! ### The tensor product double complex -/

private noncomputable abbrev tensorBicomplex {R : Type u} [CommRing R]
    (P L : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    HomologicalComplex₂ (ModuleCat.{max u v} R) (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (((curriedTensor (ModuleCat.{max u v} R)).flip.mapBifunctorHomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj P).obj L

private lemma tensorBicomplex_columns_acyclic {R : Type u} [CommRing R]
    (P L : CochainComplex (ModuleCat.{max u v} R) ℤ)
    [∀ q : ℤ, Module.Flat R (P.X q)] (hL : L.Acyclic) (q : ℤ) :
    ((tensorBicomplex P L).X q).Acyclic :=
  tensorRight_acyclic L (P.X q) hL

private lemma tensorBicomplex_above_isZero {R : Type u} [CommRing R]
    (P L : CochainComplex (ModuleCat.{max u v} R) ℤ) (d q : ℤ)
    [P.IsStrictlyLE d] (hq : d < q) : IsZero ((tensorBicomplex P L).X q) := by
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex.hom_ext
  intro i
  have hz : IsZero (((tensorBicomplex P L).X q).X i) := by
    show IsZero (L.X i ⊗ P.X q)
    exact (tensorLeft (L.X i)).map_isZero (P.isZero_of_isStrictlyLE d q hq)
  exact hz.eq_of_src _ _

private lemma tensorBicomplex_second_above_isZero {R : Type u} [CommRing R]
    (P L : CochainComplex (ModuleCat.{max u v} R) ℤ) (m p q : ℤ)
    [L.IsStrictlyLE m] (hq : m < q) : IsZero (((tensorBicomplex P L).X p).X q) := by
  show IsZero (L.X q ⊗ P.X p)
  exact (tensorRight (P.X p)).map_isZero (L.isZero_of_isStrictlyLE m q hq)

private lemma finite_tensorBicomplex_support {R : Type u} [CommRing R]
    (P L : CochainComplex (ModuleCat.{max u v} R) ℤ) (d m n : ℤ)
    [P.IsStrictlyLE d] [L.IsStrictlyLE m] :
    {pq : ℤ × ℤ | ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) pq = n ∧
      ¬ IsZero (((tensorBicomplex P L).X pq.1).X pq.2)}.Finite := by
  refine Set.Finite.subset ((Set.finite_Icc (n - m) d).image (fun p => (p, n - p))) ?_
  rintro ⟨p, q⟩ ⟨hpq, hz⟩
  have hpq' : p + q = n := hpq
  have hp : p ≤ d := by
    by_contra h
    exact hz ((HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) q).map_isZero
      (tensorBicomplex_above_isZero P L d p (by omega)))
  have hq : q ≤ m := by
    by_contra h
    exact hz (tensorBicomplex_second_above_isZero P L m p q (by omega))
  refine ⟨p, ⟨by omega, hp⟩, ?_⟩
  simp [show n - p = q by omega]

private noncomputable def tensorBicomplex_total_iso_tensor {R : Type u} [CommRing R]
    (P L : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    (tensorBicomplex.{u, v} P L).total (ComplexShape.up ℤ) ≅
      HomologicalComplex.tensorObj L P :=
  HomologicalComplex.mapBifunctorFlipIso L P
    (curriedTensor (ModuleCat.{max u v} R)) (ComplexShape.up ℤ)

/-! ### Acyclicity of a total complex with acyclic columns

A double complex with finite diagonals and acyclic columns has acyclic total complex: the
spectral sequence of the first filtration of `Tot` has first page the column-wise homology
(Stacks 0130), which vanishes, and a weak Serre class containing one whole page contains every
`H^n(Tot)` (Stacks 0132). Taking the weak Serre class to be the zero objects gives the claim. -/

private lemma total_acyclic_of_columns
    {A : Type*} [Category* A] [Abelian A]
    (K : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (hK : ∀ n : ℤ, {pq : ℤ × ℤ | pq.1 + pq.2 = n ∧
      ¬ IsZero ((K.X pq.1).X pq.2)}.Finite)
    [K.HasTotal (ComplexShape.up ℤ)] (h : ∀ p, (K.X p).Acyclic) :
    (K.total (ComplexShape.up ℤ)).Acyclic := by
  classical
  let Fil : ∀ (_p n : ℤ), Subobject (K.totalFiltration₁.X.X n) := fun p n =>
    Subobject.mk ((K.totalFiltration₁.filtration.ι.app (Opposite.op p)).f n)
  let Zc : ∀ (_r _p n : ℤ), Subobject (K.totalFiltration₁.X.X n) := fun r p n =>
    Fil p n ⊓ (Subobject.pullback (K.totalFiltration₁.X.d n (n + 1))).obj (Fil (p + r) (n + 1))
  let Dc : ∀ (_r _p n : ℤ), Subobject (K.totalFiltration₁.X.X n) := fun r p n =>
    Zc (r - 1) (p + 1) n ⊔
      (Subobject.«exists» (K.totalFiltration₁.X.d (n - 1) n)).obj (Zc (r - 1) (p - r + 1) (n - 1))
  let FH : ∀ (n _p : ℤ), Subobject (K.totalFiltration₁.X.homology n) := fun n p =>
    imageSubobject
      (HomologicalComplex.homologyMap (K.totalFiltration₁.filtration.ι.app (Opposite.op p)) n)
  have hFil : ∀ p n : ℤ, Fil p n =
      Subobject.mk ((K.totalFiltration₁.filtration.ι.app (Opposite.op p)).f n) := fun _ _ => rfl
  have hZc : ∀ r p n : ℤ, Zc r p n = Fil p n ⊓
      (Subobject.pullback (K.totalFiltration₁.X.d n (n + 1))).obj (Fil (p + r) (n + 1)) :=
    fun _ _ _ => rfl
  have hDc : ∀ r p n : ℤ, Dc r p n = Zc (r - 1) (p + 1) n ⊔
      (Subobject.«exists» (K.totalFiltration₁.X.d (n - 1) n)).obj
        (Zc (r - 1) (p - r + 1) (n - 1)) := fun _ _ _ => rfl
  have hFH : ∀ n p : ℤ, FH n p = imageSubobject
      (HomologicalComplex.homologyMap
        (K.totalFiltration₁.filtration.ι.app (Opposite.op p)) n) := fun _ _ => rfl
  obtain ⟨E, e, -, hδ, -, -, -⟩ :=
    CochainComplex.exists_cohomologicalSpectralSequence K.totalFiltration₁ Fil hFil Zc hZc Dc hDc
  obtain ⟨-, ⟨β, -⟩, -⟩ :=
    K.exists_iso_pages_totalFiltration₁ Fil hFil Zc hZc Dc hDc E e hδ
  obtain ⟨-, -, -, -, hweak⟩ :=
    K.isBounded_and_converges_totalFiltration₁ hK Fil hFil Zc hZc Dc hDc FH hFH E e
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact hweak (IsZero (C := A)) 1 zero_le_one
    (fun p q => (β p q).isZero_iff.2 ((h p q).isZero_homology)) n

/-! ### Exactness of colimits of complexes -/

/-- **A colimit of acyclic complexes along a shape whose colimits are exact is acyclic.**
Exactness is detected on the short complex in each degree, and that short complex of colimits
is the colimit of the short complexes. Public because consumers outside this file need it as
a hypothesis of the K-flatness criteria of Stacks Tag 06YQ. -/
lemma acyclic_colimit {C : Type*} [Category* C] [Abelian C]
    {I : Type*} {c : ComplexShape I} {J : Type w} [Category.{x} J]
    [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]
    (D : J ⥤ HomologicalComplex C c)
    (hD : ∀ j, (D.obj j).Acyclic) : (colimit D).Acyclic := by
  intro i
  let E := D ⋙ HomologicalComplex.shortComplexFunctor C c i
  let S := (ShortComplex.functorEquivalence J C).inverse.obj E
  have hS : S.Exact := by
    refine (jointlyReflectIsomorphisms_evaluation.exact_iff S).2 fun j ↦ ?_
    exact ShortComplex.exact_of_iso
      (((ShortComplex.functorEquivalence J C).counitIso.app E).app j).symm
      (hD j i)
  let c₁ := (HomologicalComplex.eval C c (c.prev i)).mapCocone (colimit.cocone D)
  let c₂ := (HomologicalComplex.eval C c i).mapCocone (colimit.cocone D)
  let c₃ := (HomologicalComplex.eval C c (c.next i)).mapCocone (colimit.cocone D)
  have hc₁ : IsColimit c₁ := isColimitOfPreserves _ (colimit.isColimit D)
  have hc₂ : IsColimit c₂ := isColimitOfPreserves _ (colimit.isColimit D)
  have hc₃ : IsColimit c₃ := isColimitOfPreserves _ (colimit.isColimit D)
  exact colim.exact_mapShortComplex hS hc₁ hc₂ hc₃
    ((colimit D).d _ _) ((colimit D).d _ _)
    (fun j ↦ (colimit.ι D j).comm _ _) (fun j ↦ (colimit.ι D j).comm _ _)

/-! ### Colimits and the total complex of a tensor product -/

/-- **A functor preserving colimits of a given shape preserves them after being applied
degreewise to complexes.** Colimits of homological complexes are computed degreewise, so a
cocone of complexes is colimiting as soon as it is in every degree. Public because the
K-flatness arguments over a site and over a space apply it to restriction, pullback and stalk
functors. -/
lemma preservesColimit_mapHomologicalComplex
    {C C' : Type*} [Category* C] [Category* C']
    [HasZeroMorphisms C] [HasZeroMorphisms C']
    {I : Type*} {c : ComplexShape I} {J : Type w} [Category.{x} J]
    [HasColimitsOfShape J C]
    (D : J ⥤ HomologicalComplex C c)
    (G : C ⥤ C') [G.PreservesZeroMorphisms] [PreservesColimitsOfShape J G] :
    PreservesColimit D (G.mapHomologicalComplex c) := by
  apply preservesColimit_of_preserves_colimit_cocone (colimit.isColimit D)
  refine HomologicalComplex.isColimitOfEval _ _ (fun q ↦ ?_)
  exact isColimitOfPreserves (HomologicalComplex.eval C c q ⋙ G) (colimit.isColimit D)

/-- **A bifunctor applied degreewise to a bicomplex preserves colimits in the second
variable.** Each degree of the bicomplex is `mapHomologicalComplex` for the bifunctor evaluated
at a term of the first complex, so this is `preservesColimit_mapHomologicalComplex` degreewise.
Public for the same reason.

Also needed by the K-flatness closure properties of `StacksFrontier.Homology.KFlat.Closure`: a
coproduct of K-flat complexes is K-flat by the same toolkit as
`CochainComplex.KFlat.kFlat_colimit`, with the shape `Discrete ι` in place of a filtered
category. -/
lemma preservesColimit_mapBifunctorObj
    {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [HasZeroMorphisms C₃]
    {I₁ I₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
    {J : Type w} [Category.{x} J] [HasColimitsOfShape J C₂]
    (D : J ⥤ HomologicalComplex C₂ c₂) (M : HomologicalComplex C₁ c₁)
    (F : C₁ ⥤ C₂ ⥤ C₃) [F.PreservesZeroMorphisms]
    [∀ X, (F.obj X).PreservesZeroMorphisms]
    [∀ X, PreservesColimitsOfShape J (F.obj X)] :
    PreservesColimit D ((F.mapBifunctorHomologicalComplex c₁ c₂).obj M) := by
  apply preservesColimit_of_preserves_colimit_cocone (colimit.isColimit D)
  refine HomologicalComplex.isColimitOfEval _ _ (fun p ↦ ?_)
  have := preservesColimit_mapHomologicalComplex D (F.obj (M.X p))
  exact isColimitOfPreserves ((F.obj (M.X p)).mapHomologicalComplex c₂)
    (colimit.isColimit D)

section Total

variable {C : Type*} [Category* C] [Preadditive C]
    {I₁ : Type u} {I₂ : Type v} {I : Type*} [DecidableEq I]
    {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} (c : ComplexShape I)
    [TotalComplexShape c₁ c₂ c] [HasCoproducts.{max u v} C]
    {J : Type*} [Category* J] [HasColimitsOfShape J C]

set_option backward.isDefEq.respectTransparency false in
/-- Evaluating the total complex of a bicomplex in degree `n` preserves colimits: the
degree-`n` component is a coproduct over the fibre `(c₁.π c₂ c) ⁻¹' {n}` of the
bidegreewise evaluations, each of which preserves colimits.

Public because the tensor-product-of-complexes material needs it: without it a consumer
has to restate the whole argument, which in practice means carrying a
`backward.isDefEq.respectTransparency` option of its own. -/
lemma preservesColimit_totalFunctorEval
    (D : J ⥤ HomologicalComplex₂ C c₁ c₂) (n : I) :
    PreservesColimit D
      (HomologicalComplex₂.totalFunctor C c₁ c₂ c ⋙ HomologicalComplex.eval C c n) := by
  let π : I₁ × I₂ → I := c₁.π c₂ c
  let ev : (↑(π ⁻¹' {n})) → (HomologicalComplex₂ C c₁ c₂ ⥤ C) := fun i ↦
    HomologicalComplex.eval (HomologicalComplex C c₂) c₁ i.1.1 ⋙
      HomologicalComplex.eval C c₂ i.1.2
  let B : HomologicalComplex₂ C c₁ c₂ ⥤ (Discrete (↑(π ⁻¹' {n})) ⥤ C) :=
    (Discrete.functor ev).flip
  have iso : (B ⋙ colim) ≅
      (HomologicalComplex₂.totalFunctor C c₁ c₂ c ⋙
          HomologicalComplex.eval C c n) := by
    refine NatIso.ofComponents (fun L ↦ ?_) ?_
    · refine (HasColimit.isoOfNatIso (F := B.obj L)
        (G := Discrete.functor (L.toGradedObject.mapObjFun π n))
        (Discrete.natIso (fun _ ↦ Iso.refl _))).trans
        (colimit.isoColimitCocone ⟨_, L.toGradedObject.isColimitCofanMapObj π n⟩)
    intro L L' f
    apply colimit.hom_ext
    intro j
    obtain ⟨⟨pq, hpq⟩⟩ := j
    have hBmap : (B.map f).app ⟨⟨pq, hpq⟩⟩ = (f.f pq.1).f pq.2 := rfl
    simp only [Functor.comp_map, Iso.trans_hom, colim_map, Category.assoc,
      ι_colimMap_assoc, HasColimit.isoOfNatIso_ι_hom_assoc,
      colimit.isoColimitCocone_ι_hom, colimit.isoColimitCocone_ι_hom_assoc,
      Discrete.natIso_hom_app, Iso.refl_hom, Category.id_comp, hBmap]
    show (f.f pq.1).f pq.2 ≫ L'.toGradedObject.ιMapObj π pq n hpq =
      L.toGradedObject.ιMapObj π pq n hpq ≫
        (HomologicalComplex₂.total.map f c).f n
    exact (L.ιTotal_map L' f c pq.1 pq.2 n hpq).symm
  have : PreservesColimit D B := by
    refine preservesColimit_of_evaluation _ _ (fun k ↦ ?_)
    have h : B ⋙ (evaluation (Discrete (↑(π ⁻¹' {n}))) C).obj k =
        ev k.as := rfl
    rw [h]
    exact comp_preservesColimit _ _
  have : PreservesColimit (D ⋙ B)
      (colim (J := Discrete (↑(π ⁻¹' {n}))) (C := C)) := inferInstance
  have : PreservesColimit D (B ⋙ colim) := comp_preservesColimit _ _
  exact preservesColimit_of_natIso _ iso

/-- Taking the total complex of a bicomplex preserves colimits, degreewise from
`preservesColimit_totalFunctorEval`. Public for the same reason. -/
lemma preservesColimit_totalFunctor (D : J ⥤ HomologicalComplex₂ C c₁ c₂) :
    PreservesColimit D (HomologicalComplex₂.totalFunctor C c₁ c₂ c) := by
  apply preservesColimit_of_preserves_colimit_cocone (colimit.isColimit D)
  refine HomologicalComplex.isColimitOfEval _ _ (fun n ↦ ?_)
  have := preservesColimit_totalFunctorEval c D n
  exact isColimitOfPreserves
    (HomologicalComplex₂.totalFunctor C c₁ c₂ c ⋙ HomologicalComplex.eval C c n)
    (colimit.isColimit D)

end Total

/-! ### Vanishing of a homology class, read on cocycles -/

/-- A homology class of a complex of modules vanishes exactly when the cocycle representing it
is a coboundary. -/
public theorem homologyπ_eq_zero_iff {R : Type u} [Ring R]
    (K : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℤ) (z : K.cycles n) :
    K.homologyπ n z = 0 ↔ ∃ y : K.X (n - 1), K.d (n - 1) n y = K.iCycles n z := by
  let S := ShortComplex.mk (K.toCycles (n - 1) n) (K.homologyπ n)
    (K.toCycles_comp_homologyπ (n - 1) n)
  have hS : S.Exact := ShortComplex.exact_of_g_is_cokernel S
    (K.homologyIsCokernel (n - 1) n ((ComplexShape.up ℤ).prev_eq' (by simp)))
  constructor
  · intro hz
    obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff S).mp hS z hz
    exact ⟨y, (congrArg (fun k : K.X (n - 1) ⟶ K.X n => k y)
      (K.toCycles_i (n - 1) n)).symm.trans (congrArg (K.iCycles n) hy)⟩
  · rintro ⟨y, hy⟩
    have hz : K.toCycles (n - 1) n y = z :=
      (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance <|
        (congrArg (fun k : K.X (n - 1) ⟶ K.X n => k y) (K.toCycles_i (n - 1) n)).trans hy
    rw [← hz]
    exact congrArg (fun k : K.X (n - 1) ⟶ K.homology n => k y)
      (K.toCycles_comp_homologyπ (n - 1) n)

/-- The image of a homology class under a map of complexes vanishes exactly when the image of
its representing cocycle is a coboundary in the target. -/
public theorem homologyMap_eq_zero_iff {R : Type u} [Ring R]
    {P K : CochainComplex (ModuleCat.{v} R) ℤ} (f : P ⟶ K) (n : ℤ)
    (x : P.homology n) (z : P.cycles n) (hz : P.homologyπ n z = x) :
    HomologicalComplex.homologyMap f n x = 0 ↔
      ∃ y : K.X (n - 1), K.d (n - 1) n y = f.f n (P.iCycles n z) := by
  have hπ : HomologicalComplex.homologyMap f n x =
      K.homologyπ n (HomologicalComplex.cyclesMap f n z) := by
    subst x
    exact congrArg (fun k : P.cycles n ⟶ K.homology n => k z)
      (HomologicalComplex.homologyπ_naturality f n)
  rw [hπ, homologyπ_eq_zero_iff]
  have hi := congrArg (fun k : P.cycles n ⟶ K.X n => k z)
    (HomologicalComplex.cyclesMap_i f n)
  exact exists_congr fun _ => ⟨fun h => h.trans hi, fun h => h.trans hi.symm⟩

/-! ### The tower of truncations exhausts a complex -/

/-- A sequence of complexes whose maps to a fixed complex are eventually isomorphisms in
each degree has that complex as its colimit. -/
public noncomputable def isColimit_of_eventually_iso_components
    {C : Type*} [Category* C] [Abelian C]
    (D : ℕ ⥤ CochainComplex C ℤ) (c : Cocone D)
    (h : ∀ i : ℤ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      IsIso ((c.ι.app n).f i)) :
    IsColimit c := by
  classical
  apply HomologicalComplex.isColimitOfEval D c
  intro i
  let n₀ := Classical.choose (h i)
  have hn₀ := Classical.choose_spec (h i)
  let E := HomologicalComplex.eval C (ComplexShape.up ℤ) i
  have hev : (D ⋙ E).IsEventuallyConstantFrom n₀ := by
    intro n φ
    have h₁ : IsIso ((c.ι.app n₀).f i) := hn₀ n₀ le_rfl
    have h₂ : IsIso ((c.ι.app n).f i) := hn₀ n (leOfHom φ)
    have heq : (D ⋙ E).map φ ≫ (c.ι.app n).f i = (c.ι.app n₀).f i := by
      change (D.map φ).f i ≫ (c.ι.app n).f i = (c.ι.app n₀).f i
      exact congrArg (fun f : D.obj n₀ ⟶ c.pt => f.f i) (c.w φ)
    exact IsIso.of_isIso_fac_right heq
  haveI : IsIso ((E.mapCocone c).ι.app n₀) := hn₀ n₀ le_rfl
  exact hev.isColimitOfIsIso (E.mapCocone c)

public noncomputable def truncLEMapSucc {C : Type*} [Category* C] [Abelian C]
    (L : CochainComplex C ℤ) (n : ℕ) :
    L.truncLE (n : ℤ) ⟶ L.truncLE ((n + 1 : ℕ) : ℤ) := by
  haveI : (L.truncLE (n : ℤ)).IsStrictlyLE ((n + 1 : ℕ) : ℤ) :=
    CochainComplex.isStrictlyLE_of_le _ (n : ℤ) _ (by omega)
  exact inv ((L.truncLE (n : ℤ)).ιTruncLE ((n + 1 : ℕ) : ℤ)) ≫
    CochainComplex.truncLEMap (L.ιTruncLE (n : ℤ)) ((n + 1 : ℕ) : ℤ)

public lemma truncLEMapSucc_comp_ι {C : Type*} [Category* C] [Abelian C]
    (L : CochainComplex C ℤ) (n : ℕ) :
    truncLEMapSucc L n ≫ L.ιTruncLE ((n + 1 : ℕ) : ℤ) =
      L.ιTruncLE (n : ℤ) := by
  dsimp [truncLEMapSucc]
  rw [Category.assoc, CochainComplex.ιTruncLE_naturality,
    IsIso.inv_hom_id_assoc]

public noncomputable def truncLESequence {C : Type*} [Category* C] [Abelian C]
    (L : CochainComplex C ℤ) :
    ℕ ⥤ CochainComplex C ℤ :=
  Functor.ofSequence (truncLEMapSucc L)

set_option backward.isDefEq.respectTransparency false in
public noncomputable def truncLECocone {C : Type*} [Category* C] [Abelian C]
    (L : CochainComplex C ℤ) : Cocone (truncLESequence L) :=
  Cocone.mk L
    (NatTrans.ofSequence (F := truncLESequence L)
      (G := (Functor.const ℕ).obj L)
      (fun n => L.ιTruncLE (n : ℤ))
      (fun n => by
        simpa [truncLESequence] using truncLEMapSucc_comp_ι L n))

public noncomputable def truncLECocone_isColimit {C : Type*} [Category* C] [Abelian C]
    (L : CochainComplex C ℤ) :
    IsColimit (truncLECocone L) := by
  apply isColimit_of_eventually_iso_components
  intro i
  refine ⟨(i + 1).toNat, fun n hn => ?_⟩
  have hi : i < (n : ℤ) := by
    have h := Int.self_le_toNat (i + 1)
    omega
  exact _root_.CochainComplex.isIso_ιTruncLE_f_of_lt L (n : ℤ) i hi

private noncomputable def tensorRightIsoTensorLeft {R : Type u} [CommRing R]
    (M : ModuleCat.{max u v} R) : tensorRight M ≅ tensorLeft M :=
  NatIso.ofComponents (fun X => (TensorProduct.comm R X M).toModuleIso)
    (by
      intro X Y f
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro x y
      rfl)

/-! ### Main results -/

/-- Colimits over an essentially small filtered category are exact in modules. -/
private lemma hasExactColimitsOfShape_moduleCat {R : Type u} [CommRing R]
    (J : Type v) [Category.{w} J] [Small.{max u x} J] [LocallySmall.{max u x} J] [IsFiltered J]
    [HasColimitsOfShape J (ModuleCat.{max u x} R)] :
    HasExactColimitsOfShape J (ModuleCat.{max u x} R) := by
  have : IsFiltered (SmallModel.{max u x} J) :=
    IsFiltered.of_equivalence (equivSmallModel.{max u x} J)
  have : HasExactColimitsOfShape (SmallModel.{max u x} J) (ModuleCat.{max u x} R) :=
    HasExactColimitsOfShape.domain_of_functor (SmallModel.{max u x} J)
      (forget₂ (ModuleCat.{max u x} R) AddCommGrpCat.{max u x})
  exact HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{max u x} R)
    (equivSmallModel.{max u x} J).symm

/-- The total complex of `M ⊗ -` (for a bifunctor `F` preserving colimits in the second
variable) preserves colimits of complexes. -/
private lemma preservesColimit_mapBifunctor_comp_totalFunctor {R : Type u} [CommRing R]
    {J : Type v} [Category.{w} J] [HasColimitsOfShape J (ModuleCat.{max u x} R)]
    (D : J ⥤ CochainComplex (ModuleCat.{max u x} R) ℤ)
    (M : CochainComplex (ModuleCat.{max u x} R) ℤ)
    (F : ModuleCat.{max u x} R ⥤ ModuleCat.{max u x} R ⥤ ModuleCat.{max u x} R)
    [F.PreservesZeroMorphisms] [∀ X, (F.obj X).PreservesZeroMorphisms]
    [∀ X, PreservesColimitsOfShape J (F.obj X)] :
    PreservesColimit D (((F.mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj M) ⋙
        HomologicalComplex₂.totalFunctor (ModuleCat.{max u x} R) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (ComplexShape.up ℤ)) := by
  have := preservesColimit_mapBifunctorObj D M F
  let : HasColimit (D ⋙ (F.mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj M) :=
    ⟨⟨_, isColimitOfPreserves _ (colimit.isColimit D)⟩⟩
  have := preservesColimit_totalFunctor (ComplexShape.up ℤ) (D ⋙ (F.mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj M)
  exact comp_preservesColimit _ _

/-- **Stacks 064K.** A bounded above cochain complex of flat modules is K-flat. -/
@[stacks 064K, sga "4 XVII 4.1.7" "(ii), modules over ring"]
public theorem kFlat_of_flat {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{max u v} R) ℤ) (d : ℤ) [P.IsStrictlyLE d]
    [∀ n : ℤ, Module.Flat R (P.X n)] :
    P.KFlat := by
  intro L hL
  have : HasExactColimitsOfShape ℕ (ModuleCat.{max u v} R) :=
    hasExactColimitsOfShape_moduleCat.{u, 0, 0, v} ℕ
  let D := truncLESequence L
  let F := ((curriedTensor (ModuleCat.{max u v} R)).flip.mapBifunctorHomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj P ⋙
      HomologicalComplex₂.totalFunctor (ModuleCat.{max u v} R)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
  have (X : ModuleCat.{max u v} R) :
      PreservesColimitsOfShape ℕ ((curriedTensor (ModuleCat.{max u v} R)).flip.obj X) := by
    have : PreservesColimitsOfShape ℕ (tensorLeft X) :=
      (ihom.adjunction X).leftAdjoint_preservesColimits.preservesColimitsOfShape
    exact preservesColimitsOfShape_of_natIso (tensorRightIsoTensorLeft X).symm
  have : PreservesColimit D F :=
    preservesColimit_mapBifunctor_comp_totalFunctor D P
      (curriedTensor (ModuleCat.{max u v} R)).flip
  have h : (colimit (D ⋙ F)).Acyclic := acyclic_colimit _ fun m =>
    total_acyclic_of_columns (tensorBicomplex P (L.truncLE (m : ℤ)))
      (fun n => finite_tensorBicomplex_support P (L.truncLE (m : ℤ)) d m n)
      (tensorBicomplex_columns_acyclic P _ (acyclic_truncLE L m hL))
  have htotal : (F.obj L).Acyclic :=
    HomologicalComplex.Acyclic.of_iso
      ((colimit.isColimit (D ⋙ F)).coconePointUniqueUpToIso
        (isColimitOfPreserves F (truncLECocone_isColimit L))) h
  exact HomologicalComplex.Acyclic.of_iso (tensorBicomplex_total_iso_tensor P L) htotal

set_option backward.isDefEq.respectTransparency false in
/-- A filtered colimit of K-flat complexes of modules is K-flat. -/
@[stacks 06Y3]
public theorem kFlat_colimit {R : Type u} [CommRing R]
    {J : Type v} [Category.{w} J] [Small.{max u x} J] [LocallySmall.{max u x} J] [IsFiltered J]
    (K : J ⥤ CochainComplex (ModuleCat.{max u x} R) ℤ)
    (hK : ∀ j, (K.obj j).KFlat) : (colimit K).KFlat := by
  intro M hM
  let : HasColimitsOfShape J (ModuleCat.{max u x} R) :=
    HasColimitsOfShape.of_essentiallySmall.{max u x, max u x} (C := ModuleCat.{max u x} R) J
  have : HasExactColimitsOfShape J (ModuleCat.{max u x} R) :=
    hasExactColimitsOfShape_moduleCat J
  let F := ((curriedTensor (ModuleCat.{max u x} R)).mapBifunctorHomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj M ⋙
      HomologicalComplex₂.totalFunctor (ModuleCat.{max u x} R)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
  have : PreservesColimit K F := by
    have (X : ModuleCat.{max u x} R) :
        PreservesColimitsOfShape J ((curriedTensor (ModuleCat.{max u x} R)).obj X) :=
      (ihom.adjunction X).leftAdjoint_preservesColimits.preservesColimitsOfShape
    exact preservesColimit_mapBifunctor_comp_totalFunctor K M
      (curriedTensor (ModuleCat.{max u x} R))
  exact HomologicalComplex.Acyclic.of_iso (preservesColimitIso F K).symm
    (acyclic_colimit (K ⋙ F) fun j ↦ hK j M hM)

end CochainComplex.KFlat

end
