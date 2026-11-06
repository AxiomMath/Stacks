module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatnessAndRightExactness
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.Defs
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksFrontier.CategoryTheory.Sites.Modules.Flat
public import StacksFrontier.Homology.KFlat.Flat
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.Data.Int.Interval
import StacksFrontier.CategoryTheory.Limits.FunctorCategory.ShortExactColimit
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# A bounded above complex of flat sheaves of modules is K-flat

Let `R` be a sheaf of commutative rings on a site `(C, J)` and let `K` be a cochain complex of
`R`-modules which is bounded above and whose terms are flat. Then `K` is K-flat: for every
acyclic complex `L` of `R`-modules the total complex `Tot(L ⊗_R K)` is acyclic.

The proof has two steps.

First, suppose `L` is bounded above as well. Then the double complex `L^q ⊗_R K^p` has, in each
total degree, only finitely many nonzero terms, because `K` vanishes above its bound and `L`
above its own. Its columns `L ⊗_R K^p` are acyclic, since `K^p` is flat and `L` is acyclic. A
first-quadrant-style spectral sequence of the column filtration therefore converges and its
`E_1` page vanishes, so the total complex is acyclic.

Second, a general acyclic `L` is the colimit of its upper truncations `τ_{≤ n} L`, each of which
is acyclic and bounded above, and the comparison `τ_{≤ n} L ⟶ L` is an isomorphism in every
degree below `n`. Tensoring with `K` and taking total complexes commutes with this sequential
colimit: tensoring with a fixed module preserves colimits (Stacks 05NB), applying a
colimit-preserving functor degreewise preserves colimits of complexes, and the total-complex
functor preserves colimits. Filtered colimits of sheaves of modules are exact (Stacks 03DB), so
a colimit of acyclic complexes is acyclic, and the first step applies to each truncation.

## Main results

* `Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat`: a bounded above cochain complex of flat
  sheaves of modules is K-flat.

## Implementation notes

K-flatness is `Stacks.SheafOfModules.IsKFlat` of Tag 06Y9 and flatness of a sheaf of modules is
`AlgebraicGeometry.SheafOfModules.IsFlat` of Tag 03ER (3); the tensor product is
`Stacks.SheafOfModules.Tensor.sheafTensor` and the total complex
`Stacks.SheafOfModules.Tensor.tensorComplex`, as in Tag 06Y9.
The universes are those of `Stacks.SheafOfModules.kFlat_colimit` (Tag 06YE): the site has
independent object and morphism universes `u` and `v`, and the sheaf of rings and the module
sections both live in a third universe `w`, independent of those two. The canonical tensor is
used here with both factor universes explicitly set to `w`. That `w` need not contain the site
is `Stacks.hasSheafCompose_forget₂_commRingCat`, which supplies the sheaf-condition composition
for `forget₂ CommRingCat RingCat` at any size.

Boundedness is the hypothesis `∃ n, K.IsStrictlyLE n` rather than an instance argument, since
the bound is irrelevant to the conclusion.

The step "tensoring on the right with a fixed module preserves colimits" uses
`preservesColimits_sheafTensorFlipObj`: Tag 05NB for the canonical tensor functor, transported
to the other tensor order by the canonical `sheafTensorBraiding`. No additional comparison
functor or isomorphism is constructed here.

Acyclicity of a colimit of complexes and degreewise preservation of colimits are
`CochainComplex.KFlat.acyclic_colimit` and `CochainComplex.KFlat.preservesColimit_mapBifunctorObj`,
stated for an arbitrary abelian respectively preadditive category.

## References

* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 06Y9](https://stacks.math.columbia.edu/tag/06Y9)
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe v u w

namespace Stacks.SheafOfModules

section Truncation

variable {A : Type*} [Category* A] [Abelian A]

/-- The canonical morphism `τ_{≤ n} L ⟶ τ_{≤ n+1} L` between successive upper truncations of
`L`. -/
noncomputable def truncLEMapSucc (L : CochainComplex A ℤ) (n : ℕ) :
    L.truncLE (n : ℤ) ⟶ L.truncLE ((n + 1 : ℕ) : ℤ) := by
  have : (L.truncLE (n : ℤ)).IsStrictlyLE ((n + 1 : ℕ) : ℤ) :=
    CochainComplex.isStrictlyLE_of_le _ (n : ℤ) _ (by omega)
  exact inv ((L.truncLE (n : ℤ)).ιTruncLE ((n + 1 : ℕ) : ℤ)) ≫
    CochainComplex.truncLEMap (L.ιTruncLE (n : ℤ)) ((n + 1 : ℕ) : ℤ)

/-- For `i < b`, the component in degree `i` of the inclusion `τ_{≤ b} L ⟶ L` is an
isomorphism. -/
lemma isIso_ιTruncLE_f_of_lt (L : CochainComplex A ℤ) (b i : ℤ) (hi : i < b) :
    IsIso ((L.ιTruncLE b).f i) := by
  let e := ComplexShape.embeddingUpIntLE b
  let j : ℕ := (b - i).natAbs
  have hji : e.f j = i := by
    change b - (j : ℤ) = i
    dsimp [j]
    omega
  have hn : ¬ e.op.BoundaryGE j := by
    change ¬ e.BoundaryLE j
    rw [ComplexShape.boundaryLE_embeddingUpIntLE_iff]
    dsimp [j]
    omega
  have hπ : IsIso ((L.op.πTruncGE e.op).f i) :=
    (e.op.isIso_liftExtend_f_iff (L.op.restrictionToTruncGE' e.op)
      (L.op.restrictionToTruncGE'_hasLift e.op) hji).2 (L.op.isIso_restrictionToTruncGE' e.op j hn)
  exact inferInstanceAs (IsIso ((L.op.πTruncGE e.op).f i).unop)

/-- The transition map `τ_{≤ n} L ⟶ τ_{≤ n+1} L` commutes with the inclusions into `L`. -/
lemma truncLEMapSucc_comp_ι (L : CochainComplex A ℤ) (n : ℕ) :
    truncLEMapSucc L n ≫ L.ιTruncLE ((n + 1 : ℕ) : ℤ) = L.ιTruncLE (n : ℤ) := by
  dsimp [truncLEMapSucc]
  rw [Category.assoc, CochainComplex.ιTruncLE_naturality, IsIso.inv_hom_id_assoc]

/-- The sequence `τ_{≤ 0} L ⟶ τ_{≤ 1} L ⟶ τ_{≤ 2} L ⟶ ⋯` of upper truncations of `L`. -/
noncomputable def truncLESequence (L : CochainComplex A ℤ) :
    ℕ ⥤ CochainComplex A ℤ :=
  Functor.ofSequence (truncLEMapSucc L)

/-- The cocone with point `L` over the sequence of upper truncations of `L`, given by the
inclusions `τ_{≤ n} L ⟶ L`. -/
noncomputable def truncLECocone (L : CochainComplex A ℤ) :
    Cocone (truncLESequence L) :=
  Cocone.mk L
    (NatTrans.ofSequence (F := truncLESequence L) (G := (Functor.const ℕ).obj L)
      (fun n => L.ιTruncLE (n : ℤ))
      (fun n => by
        simp only [truncLESequence, Functor.ofSequence_map_homOfLE_succ,
          Functor.const_obj_map]
        exact (truncLEMapSucc_comp_ι L n).trans (Category.comp_id _).symm))

/-- A cocone over a sequence of cochain complexes is a colimit if, in each degree `i`, its
components in degree `i` are isomorphisms from some index on. -/
noncomputable def isColimit_of_eventually_iso_components
    (D : ℕ ⥤ CochainComplex A ℤ) (c : Cocone D)
    (h : ∀ i : ℤ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → IsIso ((c.ι.app n).f i)) :
    IsColimit c := by
  refine HomologicalComplex.isColimitOfEval D c fun i => ?_
  let n₀ := Classical.choose (h i)
  have hn₀ := Classical.choose_spec (h i)
  let E := HomologicalComplex.eval A (ComplexShape.up ℤ) i
  have hev : (D ⋙ E).IsEventuallyConstantFrom n₀ := fun n φ => by
    have := hn₀ n₀ le_rfl
    have := hn₀ n (leOfHom φ)
    exact IsIso.of_isIso_fac_right (HomologicalComplex.congr_hom (c.w φ) i)
  have : IsIso ((E.mapCocone c).ι.app n₀) := hn₀ n₀ le_rfl
  exact hev.isColimitOfIsIso (E.mapCocone c)

/-- A cochain complex `L` is the colimit of its upper truncations `τ_{≤ n} L`. -/
noncomputable def truncLECocone_isColimit (L : CochainComplex A ℤ) :
    IsColimit (truncLECocone L) :=
  isColimit_of_eventually_iso_components _ _ fun i =>
    ⟨(i + 1).toNat, fun n hn => isIso_ιTruncLE_f_of_lt L (n : ℤ) i (by omega)⟩

end Truncation

section TotalAcyclic

universe a

private lemma total_acyclic_of_columns
    {A : Type a} [Category* A] [Abelian A]
    (K : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (hK : ∀ n : ℤ, {pq : ℤ × ℤ | pq.1 + pq.2 = n ∧
      ¬ IsZero ((K.X pq.1).X pq.2)}.Finite)
    [K.HasTotal (ComplexShape.up ℤ)] (h : ∀ p, (K.X p).Acyclic) :
    (K.total (ComplexShape.up ℤ)).Acyclic := by
  classical
  let Fil : ∀ (_p n : ℤ), Subobject (K.totalFiltration₁.X.X n) := fun p n =>
    Subobject.mk ((K.totalFiltration₁.filtration.ι.app (Opposite.op p)).f n)
  let Zc : ∀ (_r _p n : ℤ), Subobject (K.totalFiltration₁.X.X n) := fun r p n =>
    Fil p n ⊓ (Subobject.pullback (K.totalFiltration₁.X.d n (n + 1))).obj
      (Fil (p + r) (n + 1))
  let Dc : ∀ (_r _p n : ℤ), Subobject (K.totalFiltration₁.X.X n) := fun r p n =>
    Zc (r - 1) (p + 1) n ⊔
      (Subobject.«exists» (K.totalFiltration₁.X.d (n - 1) n)).obj
        (Zc (r - 1) (p - r + 1) (n - 1))
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

end TotalAcyclic

section Sheaf

private lemma acyclic_of_iso {A : Type*} [Category* A] [HasZeroMorphisms A] [HasZeroObject A]
    {K L : CochainComplex A ℤ} (e : K ≅ L) (hK : K.Acyclic) : L.Acyclic :=
  fun i => HomologicalComplex.ExactAt.of_iso (hK i) e

/-- An exact functor carries acyclic complexes to acyclic complexes. -/
lemma acyclic_mapHomologicalComplex_of_exactFunctor
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    (F : A ⥤ B) [F.Additive] (hF : exactFunctor A B F)
    (L : CochainComplex A ℤ) (hL : L.Acyclic) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).Acyclic := by
  obtain ⟨_, _⟩ := (exactFunctor_iff F).1 hF
  intro i
  rw [HomologicalComplex.exactAt_iff]
  exact (hL i).map F

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{w})
  [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

-- The sections universe `w` is independent of the site universes, so Mathlib's
-- size-restricted instances do not supply the sheaf-condition composition used by `IsFlat`.
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

private lemma acyclic_truncLE
    (L : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
    (m : ℤ) (hL : L.Acyclic) : (L.truncLE m).Acyclic := by
  rw [L.acyclic_truncLE_iff m (m + 1), L.isGE_iff]
  exact fun i _ => hL i

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).obj M).Additive]

private noncomputable abbrev tensorBicomplex
    (K L : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ) :
    HomologicalComplex₂ (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R))
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  ((((Stacks.SheafOfModules.Tensor.sheafTensor R).flip.mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj L)

private lemma isZero_tensorBicomplex_X_X
    (K L : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
    (p q : ℤ) (h : IsZero (K.X p) ∨ IsZero (L.X q)) :
    IsZero (((tensorBicomplex R K L).X p).X q) := by
  rcases h with h | h
  · exact ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj (L.X q)).map_isZero h
  · exact ((evaluation _ _).obj (K.X p)).map_isZero
      ((Stacks.SheafOfModules.Tensor.sheafTensor R).map_isZero h)

private lemma finite_tensorBicomplex_support
    (K L : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
    (d m n : ℤ) [K.IsStrictlyLE d] [L.IsStrictlyLE m] :
    {pq : ℤ × ℤ | pq.1 + pq.2 = n ∧
      ¬ IsZero (((tensorBicomplex R K L).X pq.1).X pq.2)}.Finite := by
  refine Set.Finite.subset (Set.finite_Icc (n - m) d |>.image (fun p => (p, n - p))) ?_
  rintro ⟨p, q⟩ ⟨(hpq : p + q = n), hz⟩
  have hp : p ≤ d := by
    by_contra h
    exact hz (isZero_tensorBicomplex_X_X R K L p q
      (.inl (K.isZero_of_isStrictlyLE d p (by omega))))
  have hq : q ≤ m := by
    by_contra h
    exact hz (isZero_tensorBicomplex_X_X R K L p q
      (.inr (L.isZero_of_isStrictlyLE m q (by omega))))
  exact ⟨p, ⟨by omega, hp⟩, by simp [show n - p = q by omega]⟩

private lemma acyclic_tensorBicomplex_columns
    (K L : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
    (hL : L.Acyclic)
    (hflat : ∀ p : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w}
      (O := R) (K.X p)) :
    ∀ p : ℤ, ((tensorBicomplex R K L).X p).Acyclic := by
  intro p
  let G := (Stacks.SheafOfModules.Tensor.sheafTensor R).flip.obj (K.X p)
  have hG : exactFunctor _ _ G := hflat p
  have : G.Additive := (exactFunctor_le_additiveFunctor _ _ G) hG
  exact acyclic_mapHomologicalComplex_of_exactFunctor G hG L hL

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).obj M).Additive] in
/-- Tensoring on the right with a fixed sheaf of modules preserves sequential colimits. -/
lemma preservesColimitsOfShape_nat_sheafTensor_flip_obj
    (X : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    PreservesColimitsOfShape ℕ
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).flip.obj X) := by
  have := preservesColimits_sheafTensorFlipObj R X
  have : PreservesColimitsOfSize.{0, 0}
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).flip.obj X) :=
    preservesSmallestColimits_of_preservesColimits _
  infer_instance

variable [∀ (K₁ K₂ : CochainComplex (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]

private noncomputable def tensorBicomplexTotalIso
    (K L : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ) :
    (tensorBicomplex R K L).total (ComplexShape.up ℤ) ≅
      ((Stacks.SheafOfModules.Tensor.tensorComplex R).obj L).obj K :=
  HomologicalComplex.mapBifunctorFlipIso L K (Stacks.SheafOfModules.Tensor.sheafTensor R)
    (ComplexShape.up ℤ)

/-- **Stacks 06YQ.** A bounded above cochain complex of flat sheaves of modules is K-flat. -/
@[stacks 06YQ]
theorem kFlat_of_boundedAbove_of_flat
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
    (hbound : ∃ n : ℤ, K.IsStrictlyLE n)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w}
      (O := R) (K.X i)) :
    IsKFlat R K := by
  intro L hL
  obtain ⟨d, _⟩ := hbound
  let A := SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)
  have : IsFiltered (SmallModel.{w} ℕ) :=
    IsFiltered.of_equivalence (equivSmallModel.{w} ℕ)
  have : AB5OfSize.{w, w} A :=
    AlgebraicGeometry.SheafOfModules.instAB5SheafOfModules
      (Stacks.SheafOfModules.Tensor.ringSheaf R)
  have : AB5OfSize.{0, 0} A := AB5OfSize_shrink A
  have : HasExactColimitsOfShape ℕ A := inferInstance
  have : HasColimitsOfSize.{w, w} A := inferInstance
  have hC0 : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink.{0, 0, w, w} A
  have : ∀ K : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ),
      K.HasTotal (ComplexShape.up ℤ) :=
    fun _ _ => (hC0.has_colimits_of_shape _).has_colimit _
  have : HasCoproducts.{0} A := fun _ => hC0.has_colimits_of_shape _
  let D := truncLESequence L
  let G := (((Stacks.SheafOfModules.Tensor.sheafTensor R).flip.mapBifunctorHomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K)
  let T := HomologicalComplex₂.totalFunctor A
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
  let F := G ⋙ T
  have := preservesColimitsOfShape_nat_sheafTensor_flip_obj R
  have : PreservesColimit D G :=
    CochainComplex.KFlat.preservesColimit_mapBifunctorObj D K
      (Stacks.SheafOfModules.Tensor.sheafTensor R).flip
  have : PreservesColimit (D ⋙ G) T :=
    CochainComplex.KFlat.preservesColimit_totalFunctor (ComplexShape.up ℤ) (D ⋙ G)
  have : PreservesColimit D F := comp_preservesColimit G T
  have hColimitAcyclic : (colimit (D ⋙ F)).Acyclic :=
    CochainComplex.KFlat.acyclic_colimit (D ⋙ F) fun m =>
      total_acyclic_of_columns (tensorBicomplex R K (L.truncLE (m : ℤ)))
        (fun n => finite_tensorBicomplex_support R K (L.truncLE (m : ℤ)) d m n)
        (acyclic_tensorBicomplex_columns R K (L.truncLE (m : ℤ))
          (acyclic_truncLE R L m hL) hflat)
  have hTotalAcyclic : (F.obj L).Acyclic :=
    acyclic_of_iso
      ((colimit.isColimit (D ⋙ F)).coconePointUniqueUpToIso
        (isColimitOfPreserves F (truncLECocone_isColimit L))) hColimitAcyclic
  exact acyclic_of_iso (tensorBicomplexTotalIso R K L) hTotalAcyclic

end Sheaf

end Stacks.SheafOfModules
