module

public import Mathlib.Algebra.Homology.Embedding.TruncGEHomology
public import Mathlib.Algebra.Homology.Embedding.TruncLEHomology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.Algebra.Homology.InjectiveDimension
public import StacksFrontier.Homology.HomComplex.DerivedAdjunction
public import StacksFrontier.Homology.HomComplex.ProjectiveRHom
public import StacksFrontier.Homology.PseudoCoherent.Characterization
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.RingTheory.Noetherian.ULift

/-!
# Finite cohomology of derived Hom into a complex of finite injective dimension

Let `A` be a Noetherian ring and let `K` and `L` be objects of the derived category of
`A`-modules all of whose cohomology modules are finite. If `L` has finite injective dimension,
then every cohomology module of `RHom_A(K, L)` is again finite.

The proof follows the source: only finitely many degrees of `K` contribute to a fixed cohomology
module of `RHom_A(K, L)`, because `L` is of finite injective dimension and hence bounded, so the
canonical truncation `τ_{≤ n} K` computes that module for `n` large. That truncation is bounded
above with finite cohomology, hence pseudo-coherent, so it is represented by a bounded-above
complex of finite free modules; and `L`, being bounded with finite cohomology, is represented by
a bounded complex of finite modules. The Hom complex of those two models is a complex of finite
modules, so its cohomology is finite.

## Main results

* `Dualizing.finite_homology_homComplexR` — the statement on models: the Hom complex of a
  complex with finite cohomology into a bounded K-injective complex with finite cohomology has
  finite cohomology. This is the affine form of the comparison used by the source.
* `Dualizing.derivedHom_finiteCohomology` — Tag 0G4H.

## References

* [Stacks Project, Tag 0G4H](https://stacks.math.columbia.edu/tag/0G4H)
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex CochainComplex.HomComplex

attribute [local instance] HasDerivedCategory.standard

namespace Dualizing

/-! ### Finiteness of the terms and the cohomology of a complex of modules -/

section ModuleFiniteness

universe u

variable {R : Type u} [CommRing R]

/-- A monomorphism of modules into a finite module over a Noetherian ring has finite source. -/
private theorem finite_of_mono {M N : ModuleCat.{u} R} [IsNoetherianRing R] (f : M ⟶ N) [Mono f]
    (hN : Module.Finite R N) : Module.Finite R M := by
  have : IsNoetherian R M :=
    isNoetherian_of_injective f.hom ((ModuleCat.mono_iff_injective f).1 ‹Mono f›)
  exact Module.IsNoetherian.finite R M

/-- An epimorphism of modules out of a finite module has finite target. -/
private theorem finite_of_epi {M N : ModuleCat.{u} R} (f : M ⟶ N) [Epi f]
    (hM : Module.Finite R M) : Module.Finite R N :=
  Module.Finite.of_surjective f.hom ((ModuleCat.epi_iff_surjective f).1 ‹Epi f›)

/-- Over a Noetherian ring, the cohomology of a complex of modules in a degree where the complex
is finite is itself finite. -/
private theorem finite_homology_of_finite_X [IsNoetherianRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (j : ℤ) (h : Module.Finite R (C.X j)) :
    Module.Finite R (C.homology j) :=
  finite_of_epi (C.homologyπ j) (finite_of_mono (C.iCycles j) h)

end ModuleFiniteness

/-! ### Finiteness of the Hom complex of a finite free complex into a finite complex -/

section CochainFiniteness

universe u

variable {R : Type u} [CommRing R]

/-- A cochain of degree `j` from `P` into a complex `G` concentrated in degrees `[a, b]` is
determined by its components in the finitely many relevant degrees. -/
private theorem cochain_injective_restrict (P G : CochainComplex (ModuleCat.{u} R) ℤ) (a b j : ℤ)
    (hGa : G.IsStrictlyGE a) (hGb : G.IsStrictlyLE b)
    (z z' : Cochain P G j)
    (h : ∀ q ∈ Finset.Icc a b, z.v (q - j) q (by omega) = z'.v (q - j) q (by omega)) :
    z = z' := by
  apply Cochain.ext
  intro p q hpq
  by_cases hq : q ∈ Finset.Icc a b
  · obtain rfl : p = q - j := by omega
    exact h q hq
  · simp only [Finset.mem_Icc, not_and, not_le] at hq
    rcases lt_or_ge q a with hq' | hq'
    · exact (G.isZero_of_isStrictlyGE a q hq').eq_of_tgt _ _
    · exact (G.isZero_of_isStrictlyLE b q (hq hq')).eq_of_tgt _ _

/-- The Hom complex from a complex of finite free modules into a bounded complex of finite
modules has finite terms. -/
private theorem finite_cochain [IsNoetherianRing R]
    (P G : CochainComplex (ModuleCat.{u} R) ℤ) (a b j : ℤ)
    (hGa : G.IsStrictlyGE a) (hGb : G.IsStrictlyLE b)
    (hP : ∀ p : ℤ, Module.Finite R (P.X p) ∧ Module.Free R (P.X p))
    (hG : ∀ q : ℤ, Module.Finite R (G.X q)) :
    Module.Finite R (Cochain P G j) := by
  classical
  let T : Type u := ∀ q : (Finset.Icc a b : Finset ℤ), (P.X ((q : ℤ) - j) ⟶ G.X (q : ℤ))
  have hT : Module.Finite R T := by
    refine Module.Finite.pi (h := fun q => ?_)
    have := (hP ((q : ℤ) - j)).1
    have := (hP ((q : ℤ) - j)).2
    have := hG (q : ℤ)
    have : Module.Finite R (↑(P.X ((q : ℤ) - j)) →ₗ[R] ↑(G.X (q : ℤ))) :=
      Module.Finite.linearMap R R _ _
    exact Module.Finite.equiv (ModuleCat.homLinearEquiv (S := R)).symm
  let f : Cochain P G j →ₗ[R] T :=
    { toFun z := fun q => z.v ((q : ℤ) - j) (q : ℤ) (by omega)
      map_add' z z' := rfl
      map_smul' r z := rfl }
  have hf : Function.Injective f := fun z z' hz =>
    cochain_injective_restrict P G a b j hGa hGb z z' fun q hq => congrFun hz ⟨q, hq⟩
  have : IsNoetherian R (Cochain P G j) := isNoetherian_of_injective f hf
  exact Module.IsNoetherian.finite R _

end CochainFiniteness

/-! ### Degreewise criteria for an isomorphism on cohomology -/

section HomologyIso

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A morphism of cochain complexes which is an isomorphism in the three degrees `i - 1`, `i`
and `i + 1` induces an isomorphism on degree-`i` cohomology. -/
private theorem isIso_homologyMap_of_isIso_f {X Y : CochainComplex C ℤ} (φ : X ⟶ Y) (i : ℤ)
    (h₁ : IsIso (φ.f (i - 1))) (h₂ : IsIso (φ.f i)) (h₃ : IsIso (φ.f (i + 1))) :
    IsIso (HomologicalComplex.homologyMap φ i) := by
  rw [← quasiIsoAt_iff_isIso_homologyMap,
    quasiIsoAt_iff' φ (i - 1) i (i + 1) (by simp) (by simp)]
  have : IsIso ((HomologicalComplex.shortComplexFunctor' C (ComplexShape.up ℤ)
      (i - 1) i (i + 1)).map φ) := (ShortComplex.isIso_iff _).2 ⟨h₁, h₂, h₃⟩
  infer_instance

/-- The canonical map `K.truncLE n ⟶ K` is an isomorphism in every degree below `n`. -/
private theorem isIso_ιTruncLE_f (K : CochainComplex C ℤ) (n p : ℤ) (hp : p < n) :
    IsIso ((K.ιTruncLE n).f p) := by
  set e := (ComplexShape.embeddingUpIntLE n).op with he
  have hf : e.f (n - p).natAbs = p := by
    change n - ((n - p).natAbs : ℤ) = p
    omega
  have hb : ¬ e.BoundaryGE (n - p).natAbs := by
    rw [he, ComplexShape.Embedding.op_boundaryGE_iff,
      ComplexShape.boundaryLE_embeddingUpIntLE_iff]
    omega
  have key : IsIso ((e.liftExtend (K.op.restrictionToTruncGE' e)
      (K.op.restrictionToTruncGE'_hasLift e)).f p) := by
    rw [e.isIso_liftExtend_f_iff _ _ hf]
    exact HomologicalComplex.isIso_restrictionToTruncGE' K.op e _ hb
  have key2 : IsIso ((K.op.πTruncGE e).f p) := key
  change IsIso ((K.op.πTruncGE e).f p).unop
  infer_instance

end HomologyIso

/-! ### Precomposition with the canonical truncation -/

section Precomp

universe u

variable {R : Type u} [CommRing R]

/-- Precomposition with a morphism which is an isomorphism in all degrees below `n` is bijective
on cochains of degree `j` into a complex vanishing above `b`, as soon as `b < n + j`. -/
private theorem bijective_precomp_f (Y F G : CochainComplex (ModuleCat.{u} R) ℤ) (ι : Y ⟶ F)
    (n b j : ℤ) (hG : G.IsStrictlyLE b) (hnj : b < n + j)
    (hiso : ∀ p : ℤ, p < n → IsIso (ι.f p)) :
    Function.Bijective ((Stacks.HomComplex.TensorHomMap.precomp R Y F G ι).f j).hom := by
  have hvanish : ∀ p q : ℤ, p + j = q → n ≤ p → Limits.IsZero (G.X q) := fun p q _ hp =>
    G.isZero_of_isStrictlyLE b q (by omega)
  have hcomp : ∀ (z : Cochain F G j) (p q : ℤ) (hpq : p + j = q),
      (((Stacks.HomComplex.TensorHomMap.precomp R Y F G ι).f j).hom z).v p q hpq = ι.f p ≫ z.v p q
        hpq := by
    intro z p q hpq
    rw [Stacks.HomComplex.TensorHomMap.precomp_f_apply, Cochain.zero_cochain_comp_v,
      Cochain.ofHom_v]
  classical
  constructor
  · intro z z' hz
    apply Cochain.ext
    intro p q hpq
    have hv : ι.f p ≫ z.v p q hpq = ι.f p ≫ z'.v p q hpq := by
      rw [← hcomp z p q hpq, ← hcomp z' p q hpq, hz]
    rcases lt_or_ge p n with hp | hp
    · have := hiso p hp
      exact (cancel_epi (ι.f p)).1 hv
    · exact (hvanish p q hpq hp).eq_of_tgt _ _
  · intro w
    refine ⟨Cochain.mk fun p q hpq =>
      if hp : p < n then (@inv _ _ _ _ (ι.f p) (hiso p hp)) ≫ w.v p q hpq else 0, ?_⟩
    apply Cochain.ext
    intro p q hpq
    rw [hcomp, Cochain.mk_v]
    split_ifs with hp
    · have := hiso p hp
      rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
    · rw [Limits.comp_zero]
      exact ((hvanish p q hpq (by omega)).eq_of_tgt _ _).symm

end Precomp

/-! ### Cohomology of a complex, read in the derived category -/

section DerivedHomology

universe w

variable {R : Type w} [CommRing R]

/-- The degree-`p` cohomology of the image of a complex in the derived category is the
degree-`p` cohomology of the complex. -/
private def homologyQObjIso (X : CochainComplex (ModuleCat.{w} R) ℤ) (p : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{w} R) p).obj (DerivedCategory.Q.obj X) ≅
      X.homology p :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat.{w} R) p).app X

/-- A zero module is finite. -/
private theorem finite_of_isZero {M : ModuleCat.{w} R} (h : Limits.IsZero M) :
    Module.Finite R M := by
  have : Subsingleton (M : Type w) := ModuleCat.isZero_iff_subsingleton.mp h
  have : Finite (M : Type w) := Finite.of_subsingleton
  exact Module.Finite.of_finite

/-- Finiteness of the cohomology of a complex transfers to the derived category. -/
private theorem finite_homologyFunctor_Q_obj (X : CochainComplex (ModuleCat.{w} R) ℤ) (p : ℤ)
    (h : Module.Finite R (X.homology p)) :
    Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{w} R) p).obj
      (DerivedCategory.Q.obj X)) :=
  Module.Finite.equiv (homologyQObjIso X p).toLinearEquiv.symm

/-- Finiteness of the cohomology of a complex, read off in the derived category. -/
private theorem finite_homology_of_finite_homologyFunctor (X : CochainComplex (ModuleCat.{w} R) ℤ)
    (p : ℤ) (h : Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{w} R) p).obj
      (DerivedCategory.Q.obj X))) :
    Module.Finite R (X.homology p) :=
  Module.Finite.equiv (homologyQObjIso X p).toLinearEquiv

/-- Finiteness of degree-`i` cohomology passes from the target to the source of a morphism of
complexes inducing an isomorphism on it. -/
private theorem finite_homology_of_isIso_homologyMap {X Y : CochainComplex (ModuleCat.{w} R) ℤ}
    (φ : X ⟶ Y) (i : ℤ) [IsIso (HomologicalComplex.homologyMap φ i)]
    (h : Module.Finite R (Y.homology i)) : Module.Finite R (X.homology i) :=
  Module.Finite.equiv (asIso (HomologicalComplex.homologyMap φ i)).toLinearEquiv.symm

end DerivedHomology

/-! ### Models with finite terms -/

section Models

universe w

variable {R : Type w} [CommRing R] [IsNoetherianRing R]

open StacksDraft.PseudoCoherence

/-- Over a Noetherian ring, a complex which is cohomologically bounded above and has finite
cohomology is quasi-isomorphic to a bounded-above complex of finite free modules. -/
private theorem exists_finiteFree_model (X : CochainComplex (ModuleCat.{w} R) ℤ) (n : ℤ)
    (hXn : X.IsStrictlyLE n) (hX : ∀ p : ℤ, Module.Finite R (X.homology p)) :
    ∃ P : CochainComplex (ModuleCat.{w} R) ℤ, IsBoundedAboveFiniteFree P ∧
      Nonempty (DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj X) := by
  refine (pseudoCoherent_iff_boundedAbove_finite_homology
    (DerivedCategory.Q.obj X) 0 R).2.1.2 ⟨⟨n, fun p hp => ?_⟩, fun p => ?_⟩
  · exact DerivedCategory.isZero_of_isLE _ n p hp
  · exact finite_homologyFunctor_Q_obj X p (hX p)

/-- Over a Noetherian ring, a complex concentrated in degrees `[a, b]` with finite cohomology is
quasi-isomorphic to a complex of finite modules concentrated in degrees `[a, c]`. -/
private theorem exists_finiteTerms_model (J : CochainComplex (ModuleCat.{w} R) ℤ) (a b : ℤ)
    (hJa : J.IsStrictlyGE a) (hJb : J.IsStrictlyLE b)
    (hJ : ∀ p : ℤ, Module.Finite R (J.homology p)) :
    ∃ (J' : CochainComplex (ModuleCat.{w} R) ℤ) (c : ℤ), J'.IsStrictlyGE a ∧ J'.IsStrictlyLE c ∧
      (∀ q : ℤ, Module.Finite R (J'.X q)) ∧
      Nonempty (DerivedCategory.Q.obj J' ≅ DerivedCategory.Q.obj J) := by
  obtain ⟨E, hE, ⟨eE⟩⟩ := exists_finiteFree_model J b hJb hJ
  obtain ⟨c, hc⟩ := hE.upperBound
  have hEGE : E.IsGE a := by
    rw [CochainComplex.isGE_iff]
    intro p hp
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    refine Limits.IsZero.of_iso ?_ (homologyQObjIso E p).symm
    exact Limits.IsZero.of_iso (DerivedCategory.isZero_of_isGE (DerivedCategory.Q.obj J) a p hp)
      ((DerivedCategory.homologyFunctor (ModuleCat.{w} R) p).mapIso eE)
  have := hEGE
  have hepi : ∀ q : ℤ, Epi ((E.πTruncGE a).f q) := fun q => by
    change Epi ((HomologicalComplex.πTruncGE E (ComplexShape.embeddingUpIntGE a)).f q)
    infer_instance
  have hisoπ : IsIso (DerivedCategory.Q.map (E.πTruncGE a)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{w} R) (E.πTruncGE a)).mpr inferInstance
  refine ⟨E.truncGE a, c, inferInstance, ?_, fun q => ?_,
    ⟨(asIso (DerivedCategory.Q.map (E.πTruncGE a))).symm ≪≫ eE⟩⟩
  · rw [CochainComplex.isStrictlyLE_iff]
    intro q hq
    have := hepi q
    rw [Limits.IsZero.iff_id_eq_zero, ← cancel_epi ((E.πTruncGE a).f q), Category.comp_id,
      Limits.comp_zero]
    exact (E.isZero_of_isStrictlyLE c q hq).eq_of_src _ _
  · have := hepi q
    exact finite_of_epi ((E.πTruncGE a).f q) (hE.finiteFree q).1

end Models

/-! ### The Hom complex into a bounded complex of injectives -/

section Core

universe w

variable {R : Type w} [CommRing R] [IsNoetherianRing R]

open StacksDraft.DerivedHom StacksDraft.PseudoCoherence

omit [IsNoetherianRing R] in
/-- The canonical truncation `F.truncLE n` of a complex with finite cohomology has finite
cohomology. -/
private theorem finite_homology_truncLE (F : CochainComplex (ModuleCat.{w} R) ℤ) (n : ℤ)
    (hF : ∀ p : ℤ, Module.Finite R (F.homology p)) (p : ℤ) :
    Module.Finite R ((F.truncLE n).homology p) := by
  rcases le_or_gt p n with hp | hp
  · have : IsIso (HomologicalComplex.homologyMap (F.ιTruncLE n) p) :=
      (quasiIsoAt_iff_isIso_homologyMap _ p).1 (CochainComplex.quasiIsoAt_ιTruncLE F n p hp)
    exact finite_homology_of_isIso_homologyMap (F.ιTruncLE n) p (hF p)
  · exact finite_of_isZero (CochainComplex.isZero_of_isLE (F.truncLE n) n p hp)

omit [IsNoetherianRing R] in
/-- If `J` vanishes above `b`, the degree-`i` cohomology of `Hom^•(F, J)` is finite as soon as
that of `Hom^•(F.truncLE n, J)` is, for `b < n + i - 1`. -/
private theorem finite_homology_homComplexR_of_truncLE
    (F J : CochainComplex (ModuleCat.{w} R) ℤ) (n b i : ℤ) (hJb : J.IsStrictlyLE b)
    (hbn : b < n + i - 1)
    (h : Module.Finite R ((CochainComplex.HomComplexR R (F.truncLE n) J).homology i)) :
    Module.Finite R ((CochainComplex.HomComplexR R F J).homology i) := by
  have hφ : ∀ j : ℤ, i - 1 ≤ j →
      IsIso ((Stacks.HomComplex.TensorHomMap.precomp R (F.truncLE n) F J (F.ιTruncLE n)).f j) := by
    intro j hj
    rw [ConcreteCategory.isIso_iff_bijective]
    exact bijective_precomp_f _ F J _ n b j hJb (by omega) fun p hp => isIso_ιTruncLE_f F n p hp
  have : IsIso (HomologicalComplex.homologyMap
      (Stacks.HomComplex.TensorHomMap.precomp R (F.truncLE n) F J (F.ιTruncLE n)) i) :=
    isIso_homologyMap_of_isIso_f _ i (hφ _ (by omega)) (hφ _ (by omega)) (hφ _ (by omega))
  exact finite_homology_of_isIso_homologyMap
    (Stacks.HomComplex.TensorHomMap.precomp R (F.truncLE n) F J (F.ιTruncLE n)) i h

/-- **The algebra form of Tag 0G4H, on models.** Over a Noetherian ring, let `F` be a complex
with finite cohomology and let `J` be a K-injective complex concentrated in degrees `[a, b]`
with finite cohomology. Then the Hom complex `Hom^•(F, J)` has finite cohomology.

Only finitely many degrees of `F` contribute to a fixed cohomology module of `Hom^•(F, J)`,
because `J` is bounded; so the canonical truncation `τ_{≤ n} F` for `n` large computes it, and
that truncation is pseudo-coherent. Replacing `F` by a bounded-above complex of finite free
modules and `J` by a bounded complex of finite modules makes the Hom complex a complex of
finite modules. -/
theorem finite_homology_homComplexR
    (F J : CochainComplex (ModuleCat.{w} R) ℤ) (a b : ℤ)
    (hJa : J.IsStrictlyGE a) (hJb : J.IsStrictlyLE b) (hJK : J.IsKInjective)
    (hF : ∀ p : ℤ, Module.Finite R (F.homology p))
    (hJ : ∀ p : ℤ, Module.Finite R (J.homology p))
    (i : ℤ) :
    Module.Finite R ((CochainComplex.HomComplexR R F J).homology i) := by
  refine finite_homology_homComplexR_of_truncLE F J (b - i + 2) b i hJb (by omega) ?_
  obtain ⟨P, hP, ⟨eP⟩⟩ := exists_finiteFree_model (F.truncLE (b - i + 2)) (b - i + 2)
    inferInstance (finite_homology_truncLE F _ hF)
  obtain ⟨c, hc⟩ := hP.upperBound
  have hProj : ∀ p : ℤ, Projective (P.X p) := fun p => by
    have := (hP.finiteFree p).2
    infer_instance
  obtain ⟨J', c', hJ'a, hJ'c, hJ'fin, ⟨eJ'⟩⟩ := exists_finiteTerms_model J a b hJa hJb hJ
  have key : DerivedCategory.Q.obj (CochainComplex.HomComplexR R (F.truncLE (b - i + 2)) J) ≅
      DerivedCategory.Q.obj (CochainComplex.HomComplexR R P J') :=
    ((derivedHomAdjunction (R := R)).homIso (F.truncLE (b - i + 2)) J).symm ≪≫
      (derivedHomAdjunction (R := R)).hom.mapIso (Iso.prod eP.op eJ'.symm) ≪≫
      (projectiveHomComparison (R := R)).iso P J' c
  have hfin : Module.Finite R ((CochainComplex.HomComplexR R P J').homology i) :=
    finite_homology_of_finite_X _ i (finite_cochain P J' a c' i hJ'a hJ'c hP.finiteFree hJ'fin)
  have := finite_homologyFunctor_Q_obj _ i hfin
  exact finite_homology_of_finite_homologyFunctor _ i (Module.Finite.equiv
    (((DerivedCategory.homologyFunctor (ModuleCat.{w} R) i).mapIso key).toLinearEquiv).symm)

end Core

/-! ### Transport along the scalar equivalence -/

section ScalarFiniteness

universe u v

open StacksDraft.DerivedHom

variable (A : Type u) [CommRing A]

/-- Restriction of scalars along `ULift.ringEquiv.symm`, applied degreewise to cochain
complexes. It is the complex-level form of the scalar equivalence used to build
`StacksDraft.DerivedHom.derivedHomAdjunctionOverRing`. -/
abbrev scalarComplexEquivalence :
    CochainComplex (ModuleCat.{max u v} (ULift.{v} A)) ℤ ≌
      CochainComplex (ModuleCat.{max u v} A) ℤ :=
  (uliftModuleEquivalence.{u, max u v, v} A).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Localization commutes with the scalar transport of cochain complexes. -/
def scalarFactors (F : CochainComplex (ModuleCat.{max u v} (ULift.{v} A)) ℤ) :
    (derivedScalarEquivalence.{u, v} A).functor.obj (DerivedCategory.Q.obj F) ≅
      DerivedCategory.Q.obj ((scalarComplexEquivalence.{u, v} A).functor.obj F) :=
  (uliftModuleEquivalence.{u, max u v, v} A).functor.mapDerivedCategoryFactors.app F

/-- A functor preserving zero morphisms carries a strict lower bound of a cochain complex to a
strict lower bound of the image complex. -/
theorem isStrictlyGE_mapHomologicalComplex {C : Type*} {D : Type*} [Category C] [Category D]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D] (Φ : C ⥤ D)
    [Φ.PreservesZeroMorphisms] (K : CochainComplex C ℤ) (n : ℤ) (hK : K.IsStrictlyGE n) :
    CochainComplex.IsStrictlyGE ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact Φ.map_isZero (K.isZero_of_isStrictlyGE n i hi)

/-- A functor preserving zero morphisms carries a strict upper bound of a cochain complex to a
strict upper bound of the image complex. -/
theorem isStrictlyLE_mapHomologicalComplex {C : Type*} {D : Type*} [Category C] [Category D]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D] (Φ : C ⥤ D)
    [Φ.PreservesZeroMorphisms] (K : CochainComplex C ℤ) (n : ℤ) (hK : K.IsStrictlyLE n) :
    CochainComplex.IsStrictlyLE ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact Φ.map_isZero (K.isZero_of_isStrictlyLE n i hi)

/-- An object of `D(A)` of injective amplitude `[a, b]` is the scalar transport of a K-injective
cochain complex of `ULift A`-modules with injective terms concentrated in degrees `[a, b]`. -/
theorem exists_scalarModel_isKInjective
    (X : DerivedCategory (ModuleCat.{max u v} A)) (a b : ℤ)
    (hX : StacksDraft.InjectiveDimension.HasInjectiveAmplitude X a b) :
    ∃ J : CochainComplex (ModuleCat.{max u v} (ULift.{v} A)) ℤ,
      J.IsStrictlyGE a ∧ J.IsStrictlyLE b ∧ J.IsKInjective ∧
      Nonempty (X ≅ (derivedScalarEquivalence.{u, v} A).functor.obj
        (DerivedCategory.Q.obj J)) := by
  obtain ⟨I, hIa, hIb, hIinj, ⟨iI⟩⟩ := hX
  have hGE : CochainComplex.IsStrictlyGE
      ((scalarComplexEquivalence.{u, v} A).inverse.obj I) a :=
    isStrictlyGE_mapHomologicalComplex
      (uliftModuleEquivalence.{u, max u v, v} A).inverse I a hIa
  refine ⟨(scalarComplexEquivalence.{u, v} A).inverse.obj I, hGE,
    isStrictlyLE_mapHomologicalComplex
      (uliftModuleEquivalence.{u, max u v, v} A).inverse I b hIb, ?_,
    ⟨iI ≪≫ ?_⟩⟩
  · have hinj : ∀ i : ℤ,
        Injective (((scalarComplexEquivalence.{u, v} A).inverse.obj I).X i) := fun i =>
      ((uliftModuleEquivalence.{u, max u v, v} A).symm.map_injective_iff (I.X i)).2 (hIinj i)
    have := hinj
    exact CochainComplex.isKInjective_of_injective
      ((scalarComplexEquivalence.{u, v} A).inverse.obj I) a
  · exact (DerivedCategory.Q.mapIso ((scalarComplexEquivalence.{u, v} A).counitIso.app I)).symm ≪≫
      (scalarFactors.{u, v} A ((scalarComplexEquivalence.{u, v} A).inverse.obj I)).symm

/-- Restriction of scalars along the canonical isomorphism `A ≃+* ULift A` preserves
finiteness. -/
private theorem finite_restrictScalars (M : ModuleCat.{max u v} (ULift.{v} A))
    (h : Module.Finite (ULift.{v} A) M) :
    Module.Finite A ((uliftModuleEquivalence.{u, max u v, v} A).functor.obj M) :=
  Module.Finite.of_surjective
    (show M →ₛₗ[(ULift.ringEquiv : ULift.{v} A ≃+* A).toRingHom]
        ((uliftModuleEquivalence.{u, max u v, v} A).functor.obj M) from
      { toFun := id
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }) Function.surjective_id

/-- Finiteness over `ULift A` can be read off after restriction of scalars to `A`. -/
private theorem finite_of_finite_restrictScalars (M : ModuleCat.{max u v} (ULift.{v} A))
    (h : Module.Finite A ((uliftModuleEquivalence.{u, max u v, v} A).functor.obj M)) :
    Module.Finite (ULift.{v} A) M :=
  Module.Finite.of_surjective
    (show ((uliftModuleEquivalence.{u, max u v, v} A).functor.obj M) →ₛₗ[(ULift.ringEquiv :
        ULift.{v} A ≃+* A).symm.toRingHom] M from
      { toFun := id
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }) Function.surjective_id

/-- Cohomology commutes with the scalar transport used to build the derived tensor--Hom
adjunction over the ring itself. -/
private def scalarHomologyIso (X : DerivedCategory (ModuleCat.{max u v} (ULift.{v} A))) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj
        ((derivedScalarEquivalence.{u, v} A).functor.obj X) ≅
      (uliftModuleEquivalence.{u, max u v, v} A).functor.obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} A)) i).obj X) :=
  (StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso
    (uliftModuleEquivalence.{u, max u v, v} A).functor i).app X

/-- Every object of `D(A)` is the scalar transport of a cochain complex of `ULift A`-modules. -/
private theorem exists_scalarModel (X : DerivedCategory (ModuleCat.{max u v} A)) :
    ∃ F : CochainComplex (ModuleCat.{max u v} (ULift.{v} A)) ℤ,
      Nonempty (X ≅ (derivedScalarEquivalence.{u, v} A).functor.obj
        (DerivedCategory.Q.obj F)) := by
  refine ⟨(scalarComplexEquivalence.{u, v} A).inverse.obj (DerivedCategory.Q.objPreimage X),
    ⟨(DerivedCategory.Q.objObjPreimageIso X).symm ≪≫ ?_⟩⟩
  exact (DerivedCategory.Q.mapIso ((scalarComplexEquivalence.{u, v} A).counitIso.app
      (DerivedCategory.Q.objPreimage X))).symm ≪≫
    (scalarFactors.{u, v} A ((scalarComplexEquivalence.{u, v} A).inverse.obj
      (DerivedCategory.Q.objPreimage X))).symm

/-- Finiteness of the cohomology of a scalar model, read from finiteness over `A`. -/
private theorem finite_homology_scalarModel
    (X : DerivedCategory (ModuleCat.{max u v} A))
    (F : CochainComplex (ModuleCat.{max u v} (ULift.{v} A)) ℤ)
    (e : X ≅ (derivedScalarEquivalence.{u, v} A).functor.obj (DerivedCategory.Q.obj F))
    (hX : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj X))
    (i : ℤ) : Module.Finite (ULift.{v} A) (F.homology i) := by
  refine finite_homology_of_finite_homologyFunctor F i
    (finite_of_finite_restrictScalars A _ ?_)
  have := hX i
  exact Module.Finite.equiv
    (((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).mapIso e ≪≫
      scalarHomologyIso.{u, v} A (DerivedCategory.Q.obj F) i).toLinearEquiv)

end ScalarFiniteness

/-! ### Tag 0G4H -/

section Main

universe u v

open StacksDraft.DerivedHom

/-- **Stacks 0G4H.** Let `A` be a Noetherian ring and let `K` and `L` be objects of the derived
category of `A`-modules whose cohomology modules are all finite. If `L` has finite injective
dimension, then every cohomology module of `RHom_A(K, L)` is finite as well. -/
@[stacks 0G4H, sga "5 I App.7.3" "affine case"]
public theorem derivedHom_finiteCohomology
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K L : DerivedCategory (ModuleCat.{max u v} A))
    (hK : DerivedCategoryB.derivedCategoryB
      (fun M : ModuleCat.{max u v} A => Module.Finite A M) K)
    (hL : DerivedCategoryB.derivedCategoryB
      (fun M : ModuleCat.{max u v} A => Module.Finite A M) L)
    (hLinj : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension L) :
    DerivedCategoryB.derivedCategoryB
      (fun M : ModuleCat.{max u v} A => Module.Finite A M)
      ((derivedHomAdjunctionOverRing A).hom.obj (.op K, L)) := by
  obtain ⟨a, b, hamp⟩ := hLinj
  obtain ⟨J, hJa, hJb, hJK, ⟨iJ⟩⟩ := exists_scalarModel_isKInjective.{u, v} A L a b hamp
  obtain ⟨F, ⟨iF⟩⟩ := exists_scalarModel.{u, v} A K
  have key : (derivedHomAdjunctionOverRing A).hom.obj (.op K, L) ≅
      (derivedScalarEquivalence.{u, v} A).functor.obj
        (DerivedCategory.Q.obj (CochainComplex.HomComplexR (ULift.{v} A) F J)) :=
    (derivedHomAdjunctionOverRing A).hom.mapIso (Iso.prod iF.symm.op iJ) ≪≫
      derivedHomModelIso.{u, v} A F J
  intro i
  have hfinB := finite_homologyFunctor_Q_obj (CochainComplex.HomComplexR (ULift.{v} A) F J) i
    (finite_homology_homComplexR F J a b hJa hJb hJK
      (finite_homology_scalarModel.{u, v} A K F iF hK)
      (finite_homology_scalarModel.{u, v} A L J iJ hL) i)
  have hfinA := finite_restrictScalars A _ hfinB
  exact Module.Finite.equiv
    (((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).mapIso key ≪≫
      scalarHomologyIso.{u, v} A
        (DerivedCategory.Q.obj (CochainComplex.HomComplexR (ULift.{v} A) F J))
          i).toLinearEquiv).symm

end Main

end Dualizing

end
