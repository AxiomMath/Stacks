module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import StacksFrontier.Homology.Perfect.DerivedReduction
public import StacksFrontier.RingTheory.Flat.ShortExact
import StacksCore.Tactic.StacksAttribute

@[expose] public section

/-!
# Perfectness modulo a product of two ideals

Let `R` be a commutative ring, let `I` and `J` be ideals of `R`, and let `K` be an object of the
derived category of `R`-modules whose derived reductions `K ⊗_R^L R/I` and `K ⊗_R^L R/J` are both
perfect. Then the derived reduction `K ⊗_R^L R/IJ` is perfect.

The proof is the source's, in two steps.

*Reduction to the case `I ∩ J = 0`.* Since `IJ ⊆ I ∩ J` and `(I ∩ J)² ⊆ IJ`, the kernel of
`R/IJ → R/(I ∩ J)` is nilpotent, so by [stacks 07LU] — in the form
`isPerfect_of_derivedExtensionScalars_surjective` — it suffices to prove that `K ⊗_R^L R/(I ∩ J)`
is perfect. Over `R/(I ∩ J)` the images of `I` and of `J` meet in zero, and the reductions of
`K ⊗_R^L R/(I ∩ J)` modulo those images are the reductions of `K` modulo `I` and modulo `J`.

*The case `I ∩ J = 0`.* Here `K` itself is perfect. By [stacks 07LT] perfectness is compactness,
so one has to show that `Hom(K, -)` commutes with arbitrary direct sums. Choose a K-flat
representative `P i` with flat terms for each member of a family `E : ι → D(R)`. Flatness of the
terms gives `IP ∩ JP = (I ∩ J)P = 0` for each such complex, so the termwise reductions sit in a
degreewise split-free short exact sequence
`P ⟶ P/IP ⊕ P/JP ⟶ P/(I+J)P`,
whose associated distinguished triangle is natural in `P`. The compactness map of `K` against the
reductions of a family is bijective — this is where perfectness of the reductions is used, through
the adjunction between derived extension and restriction of scalars — and the five-term exactness
of the compactness maps along the triangle then forces bijectivity at `P` itself.

## Main results

* `StacksDraft.Perfect.isPerfect_of_isPerfect_reductions`: if `I ∩ J = 0` and `K` is perfect
  modulo `I` and modulo `J`, then `K` is perfect.
* `StacksDraft.Perfect.isPerfect_derivedReduction_mul`: [stacks 09AS], perfectness modulo `I` and
  modulo `J` implies perfectness modulo `I * J`.

## Implementation notes

The reduction `P ↦ P/IP` of a complex is the termwise application of the endofunctor
`M ↦ M/IM` of `Mod R` (`quotientFunctor`), which is the composite of extension and restriction of
scalars along `R → R/I` up to the canonical isomorphism `TensorProduct.quotTensorEquivQuotSMul`.
Working with this endofunctor rather than with `Mod (R/I)` keeps every complex in one category, so
that the Mayer–Vietoris short exact sequence above is a short exact sequence of `R`-module
complexes; the passage to `Mod (R/I)`, and with it the input hypothesis, enters only through
`bijective_cofanMap_quotient`.

The binary product of complexes is built termwise (`productComplex`) rather than as the categorical
biproduct of `CochainComplex (Mod R) ℤ`, so that its terms are literally products of modules and
the degreewise short exactness of the Mayer–Vietoris sequence is the module-theoretic statement
`quotientShortComplex_shortExact`.

## References

* [The Stacks Project, Tag 09AS](https://stacks.math.columbia.edu/tag/09AS)
-/

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Perfect

/-! ### The Mayer–Vietoris sequence of two submodules meeting in zero -/

section QuotientSequence

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]

/-- The pair of the two quotient maps, `x ↦ (x mod P, x mod Q)`. -/
private abbrev quotientDiagonal (P Q : Submodule R M) : M →ₗ[R] (M ⧸ P) × (M ⧸ Q) :=
  P.mkQ.prod Q.mkQ

/-- The difference of the two projections, `(x, y) ↦ x - y mod (P + Q)`. -/
private abbrev quotientDifference (P Q : Submodule R M) :
    (M ⧸ P) × (M ⧸ Q) →ₗ[R] M ⧸ (P ⊔ Q) :=
  (P.mapQ (P ⊔ Q) LinearMap.id (by simp)).comp (LinearMap.fst R (M ⧸ P) (M ⧸ Q)) -
    (Q.mapQ (P ⊔ Q) LinearMap.id (by simp)).comp (LinearMap.snd R (M ⧸ P) (M ⧸ Q))

private theorem exists_mkQ_prod_eq (P Q : Submodule R M) (z : (M ⧸ P) × (M ⧸ Q)) :
    ∃ x y : M, z = (P.mkQ x, Q.mkQ y) := by
  obtain ⟨x, hx⟩ := P.mkQ_surjective z.1
  obtain ⟨y, hy⟩ := Q.mkQ_surjective z.2
  exact ⟨x, y, Prod.ext hx.symm hy.symm⟩

private theorem quotientDifference_mk (P Q : Submodule R M) (x y : M) :
    quotientDifference P Q (P.mkQ x, Q.mkQ y) = (P ⊔ Q).mkQ (x - y) := by
  simp [quotientDifference]

private theorem quotientDifference_comp_quotientDiagonal (P Q : Submodule R M) :
    (quotientDifference P Q).comp (quotientDiagonal P Q) = 0 := by
  ext x
  simp [quotientDifference, quotientDiagonal]

private theorem exact_quotientDiagonal_quotientDifference (P Q : Submodule R M) :
    Function.Exact (quotientDiagonal P Q) (quotientDifference P Q) := by
  intro z
  obtain ⟨x, y, rfl⟩ := exists_mkQ_prod_eq P Q z
  constructor
  · intro h
    rw [quotientDifference_mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp h
    refine ⟨x - p, ?_⟩
    apply Prod.ext
    · change P.mkQ (x - p) = P.mkQ x
      rw [map_sub, show P.mkQ p = 0 from (Submodule.Quotient.mk_eq_zero P).2 hp, sub_zero]
    · change Q.mkQ (x - p) = Q.mkQ y
      have heq : x - p = y + q := by
        apply sub_eq_zero.mp
        calc (x - p) - (y + q) = (x - y) - (p + q) := by abel
          _ = 0 := sub_eq_zero.mpr hpq.symm
      rw [heq, map_add, show Q.mkQ q = 0 from (Submodule.Quotient.mk_eq_zero Q).2 hq, add_zero]
  · rintro ⟨t, ht⟩
    rw [← ht]
    exact LinearMap.congr_fun (quotientDifference_comp_quotientDiagonal P Q) t

private theorem injective_quotientDiagonal (P Q : Submodule R M) (hPQ : P ⊓ Q = ⊥) :
    Function.Injective (quotientDiagonal P Q) := by
  apply LinearMap.ker_eq_bot.mp
  rwa [LinearMap.ker_prod, Submodule.ker_mkQ, Submodule.ker_mkQ]

private theorem surjective_quotientDifference (P Q : Submodule R M) :
    Function.Surjective (quotientDifference P Q) := by
  intro z
  obtain ⟨x, rfl⟩ := (P ⊔ Q).mkQ_surjective z
  exact ⟨(P.mkQ x, Q.mkQ 0), by rw [quotientDifference_mk, sub_zero]⟩

/-- The Mayer–Vietoris short complex `M → M/P ⊕ M/Q → M/(P+Q)`. -/
private def quotientShortComplex (P Q : Submodule R M) : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.moduleCatMk (quotientDiagonal P Q) (quotientDifference P Q)
    (quotientDifference_comp_quotientDiagonal P Q)

private theorem quotientShortComplex_shortExact (P Q : Submodule R M) (hPQ : P ⊓ Q = ⊥) :
    (quotientShortComplex P Q).ShortExact where
  exact := ((quotientShortComplex P Q).moduleCat_exact_iff).2
    fun x hx => (exact_quotientDiagonal_quotientDifference P Q x).1 hx
  mono_f := (ModuleCat.mono_iff_injective _).2 (injective_quotientDiagonal P Q hPQ)
  epi_g := (ModuleCat.epi_iff_surjective _).2 (surjective_quotientDifference P Q)

/-- The Mayer–Vietoris sequence read with a submodule `W` presented as `P + Q`. -/
private theorem quotientShortComplex_shortExact_of_sup_eq (P Q W : Submodule R M)
    (hW : P ⊔ Q = W) (hP : P ≤ W) (hQ : Q ≤ W) (hPQ : P ⊓ Q = ⊥) :
    (ShortComplex.moduleCatMk (quotientDiagonal P Q)
      ((P.mapQ W LinearMap.id (by simpa using hP)).comp (LinearMap.fst R _ _) -
        (Q.mapQ W LinearMap.id (by simpa using hQ)).comp (LinearMap.snd R _ _))
      (by ext x; simp [quotientDiagonal])).ShortExact := by
  subst W
  exact quotientShortComplex_shortExact P Q hPQ

end QuotientSequence

/-! ### Termwise reduction of a complex modulo an ideal -/

section ReductionComplex

-- Numerous `rw`/`change` steps below match objects of `ModuleCat` up to definitional, not
-- syntactic, equality; this restores the pre-bump `isDefEq` behaviour they rely on.
set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- Reduction modulo an ideal, as an endofunctor `M ↦ M/IM` of the category of `R`-modules. -/
@[sga "3 III 4.13"]
private def quotientFunctor (I : Ideal R) : ModuleCat.{v} R ⥤ ModuleCat.{v} R where
  obj M := ModuleCat.of R (M ⧸ (I • (⊤ : Submodule R M)))
  map {M N} f := ModuleCat.ofHom <|
    (I • (⊤ : Submodule R M)).mapQ (I • (⊤ : Submodule R N)) f.hom
      (Submodule.smul_top_le_comap_smul_top I f.hom)
  map_id M := by ext x; rfl
  map_comp {M N P} f g := by ext x; rfl

private theorem quotientFunctor_map_mk (I : Ideal R) {M N : ModuleCat.{v} R} (f : M ⟶ N) (x : M) :
    (quotientFunctor I).map f ((I • (⊤ : Submodule R M)).mkQ x) =
      (I • (⊤ : Submodule R N)).mkQ (f x) := rfl

private theorem quotientFunctor_additive (I : Ideal R) : (quotientFunctor.{u, v} I).Additive where
  map_add {M N} f g := by
    ext x
    obtain ⟨x, rfl⟩ := (I • (⊤ : Submodule R M)).mkQ_surjective x
    exact map_add (I • (⊤ : Submodule R N)).mkQ (f x) (g x)

attribute [local instance] quotientFunctor_additive

/-- Extension of scalars to `R/I` followed by restriction of scalars back to `R` is reduction
modulo `I`: this is `(R/I) ⊗_R M ≅ M/IM`. -/
private noncomputable def extensionRestrictQuotientIso (I : Ideal R) :
    ModuleCat.extendScalars.{u, u, max u v} (Ideal.Quotient.mk I) ⋙
      ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.mk I) ≅
        quotientFunctor.{u, max u v} I := by
  refine NatIso.ofComponents (fun M => (TensorProduct.quotTensorEquivQuotSMul M I).toModuleIso) ?_
  intro M N f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (TensorProduct.quotTensorEquivQuotSMul N I) ((f.hom.baseChange (R ⧸ I)) x) =
    (quotientFunctor I).map f ((TensorProduct.quotTensorEquivQuotSMul M I) x)
  induction x using TensorProduct.inductionOn with
  | tmul r m =>
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    simp only [LinearMap.baseChange_tmul, TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
    change r • Submodule.Quotient.mk (f m) =
      (quotientFunctor I).map f (r • Submodule.Quotient.mk m)
    rw [map_smul]
    rfl
  | add x y hx hy => simp_all

/-- The termwise reduction of a complex modulo an ideal. -/
private abbrev quotientComplex (I : Ideal R) (K : CochainComplex (ModuleCat.{v} R) ℤ) :=
  ((quotientFunctor I).mapHomologicalComplex (ComplexShape.up ℤ)).obj K

/-- Termwise extension of scalars to `R/I`, followed by `Q` and by derived restriction of scalars
back to `R`, is `Q` applied to the termwise reduction modulo `I`. -/
private noncomputable def ordinaryReductionRestrictionIso (I : Ideal R) :
    (ModuleCat.extendScalars.{u, u, max u v} (Ideal.Quotient.mk I)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⋙
        (ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.mk I)).mapDerivedCategory ≅
      (quotientFunctor.{u, max u v} I).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  Functor.isoWhiskerLeft
      ((ModuleCat.extendScalars.{u, u, max u v} (Ideal.Quotient.mk I)).mapHomologicalComplex
        (ComplexShape.up ℤ))
      (ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.mk I)).mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso
      (extensionRestrictQuotientIso.{u, v} I) (ComplexShape.up ℤ)) DerivedCategory.Q

/-- The heart of the argument: if the derived reduction of `K` modulo `I` is perfect, then the
compactness map of `K` against a family of *termwise reductions* modulo `I` is bijective. The
reduction is compact over `R/I` by [stacks 07LT]; the adjunction between derived extension and
restriction of scalars along `R → R/I` converts its compactness map into that of `K`. -/
private theorem bijective_cofanMap_quotient (I : Ideal R)
    (K : DerivedCategory (ModuleCat.{max u v} R))
    (hK : IsPerfect
      ((totalDerivedExtensionScalars.{u, u, v} (Ideal.Quotient.mk I)).functor.obj K))
    {ι : Type (max u v)} [DecidableEq ι]
    {P : ι → CochainComplex (ModuleCat.{max u v} R) ℤ}
    {S : CochainComplex (ModuleCat.{max u v} R) ℤ} (j : ∀ i, P i ⟶ S)
    (hc : IsColimit (Cofan.mk S j)) :
    Function.Bijective (cofanMap K fun i => DerivedCategory.Q.map
      (((quotientFunctor I).mapHomologicalComplex (ComplexShape.up ℤ)).map (j i))) := by
  let D := totalDerivedExtensionScalars.{u, u, v} (Ideal.Quotient.mk I)
  let adj := @derivedExtensionScalarsAdjunction.{u, u, v} R (R ⧸ I) _ _
    (Ideal.Quotient.mk I) _ _ D.functor D.comparison D.isLeftDerived
  have : D.functor.Additive := adj.left_adjoint_additive
  have hcomp : IsCompactObject.{max u v} (D.functor.obj K) :=
    (isPerfect_iff_isCompactObject_max _).mp hK
  have : PreservesColimitsOfShape (Discrete ι)
      (DerivedCategory.Q (C := ModuleCat.{max u v} (R ⧸ I))) :=
    preservesColimitsOfShape_discrete_Q_moduleCat.{u, v} ι
  have : (ModuleCat.extendScalars.{u, u, max u v} (Ideal.Quotient.mk I)).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{v, u, u} (Ideal.Quotient.mk I)).isLeftAdjoint
  let H := (ModuleCat.extendScalars.{u, u, max u v}
    (Ideal.Quotient.mk I)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q
  have hc' : IsColimit (Cofan.mk (H.obj S) fun i => H.map (j i)) :=
    (isColimitMapCoconeCofanMkEquiv H P j) (isColimitOfPreserves H hc)
  exact bijective_cofanMap_of_natIso K (ordinaryReductionRestrictionIso I) j
    (bijective_cofanMap_of_adjunction adj K hcomp _ hc')

/-- The shifted form of `bijective_cofanMap_quotient`, obtained by pushing the colimit cofan
through the shift functor. -/
private theorem bijective_cofanMap_quotient_shift (I : Ideal R)
    (K : DerivedCategory (ModuleCat.{max u v} R))
    (hK : IsPerfect
      ((totalDerivedExtensionScalars.{u, u, v} (Ideal.Quotient.mk I)).functor.obj K))
    {ι : Type (max u v)} [DecidableEq ι]
    {P : ι → CochainComplex (ModuleCat.{max u v} R) ℤ}
    {S : CochainComplex (ModuleCat.{max u v} R) ℤ} (j : ∀ i, P i ⟶ S)
    (hc : IsColimit (Cofan.mk S j)) (n : ℤ) :
    Function.Bijective (cofanMap K fun i => (DerivedCategory.Q.map
      (((quotientFunctor I).mapHomologicalComplex (ComplexShape.up ℤ)).map (j i)))⟦n⟧') := by
  let F := shiftFunctor (CochainComplex (ModuleCat.{max u v} R) ℤ) n
  let H := (quotientFunctor.{u, max u v} I).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q
  have hc' : IsColimit (Cofan.mk (F.obj S) fun i => F.map (j i)) :=
    (isColimitMapCoconeCofanMkEquiv F P j) (isColimitOfPreserves F hc)
  exact bijective_cofanMap_of_natIso K (H.commShiftIso n) j
    (bijective_cofanMap_quotient I K hK _ hc')

/-! ### The termwise binary product of complexes -/

/-- The termwise product of two complexes. -/
private def productComplex (K L : CochainComplex (ModuleCat.{v} R) ℤ) :
    CochainComplex (ModuleCat.{v} R) ℤ where
  X i := ModuleCat.of R (K.X i × L.X i)
  d i j := ModuleCat.ofHom ((K.d i j).hom.prodMap (L.d i j).hom)
  shape i j h := by ext x <;> simp [K.shape i j h, L.shape i j h]
  d_comp_d' i j k _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · exact congrArg (fun f : K.X i ⟶ K.X k => f x.1) (K.d_comp_d i j k)
    · exact congrArg (fun f : L.X i ⟶ L.X k => f x.2) (L.d_comp_d i j k)

private def productComplexInl (K L : CochainComplex (ModuleCat.{v} R) ℤ) :
    K ⟶ productComplex K L where
  f i := ModuleCat.ofHom (LinearMap.inl R (K.X i) (L.X i))
  comm' i j _ := by
    ext x
    change ((K.d i j) x, (L.d i j) 0) = ((K.d i j) x, 0)
    rw [map_zero]

private def productComplexInr (K L : CochainComplex (ModuleCat.{v} R) ℤ) :
    L ⟶ productComplex K L where
  f i := ModuleCat.ofHom (LinearMap.inr R (K.X i) (L.X i))
  comm' i j _ := by
    ext x
    change ((K.d i j) 0, (L.d i j) x) = (0, (L.d i j) x)
    rw [map_zero]

private def productComplexFst (K L : CochainComplex (ModuleCat.{v} R) ℤ) :
    productComplex K L ⟶ K where
  f i := ModuleCat.ofHom (LinearMap.fst R (K.X i) (L.X i))
  comm' i j _ := by ext x; rfl

private def productComplexSnd (K L : CochainComplex (ModuleCat.{v} R) ℤ) :
    productComplex K L ⟶ L where
  f i := ModuleCat.ofHom (LinearMap.snd R (K.X i) (L.X i))
  comm' i j _ := by ext x; rfl

private theorem productComplex_id (K L : CochainComplex (ModuleCat.{v} R) ℤ) :
    productComplexFst K L ≫ productComplexInl K L +
      productComplexSnd K L ≫ productComplexInr K L = 𝟙 (productComplex K L) := by
  ext i x
  change (x.1, 0) + (0, x.2) = x
  exact Prod.ext (add_zero _) (zero_add _)

private def productComplexMap {K K' L L' : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : K ⟶ K') (g : L ⟶ L') : productComplex K L ⟶ productComplex K' L' where
  f i := ModuleCat.ofHom ((f.f i).hom.prodMap (g.f i).hom)
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · exact congrArg (fun t : K.X i ⟶ K'.X j => t x.1) (f.comm i j)
    · exact congrArg (fun t : L.X i ⟶ L'.X j => t x.2) (g.comm i j)

private theorem productComplexMap_inl {K K' L L' : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : K ⟶ K') (g : L ⟶ L') :
    productComplexInl K L ≫ productComplexMap f g = f ≫ productComplexInl K' L' := by
  ext i x
  change ((f.f i) x, (g.f i) 0) = ((f.f i) x, 0)
  rw [map_zero]

private theorem productComplexMap_inr {K K' L L' : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : K ⟶ K') (g : L ⟶ L') :
    productComplexInr K L ≫ productComplexMap f g = g ≫ productComplexInr K' L' := by
  ext i x
  change ((f.f i) 0, (g.f i) x) = (0, (g.f i) x)
  rw [map_zero]

/-- Surjectivity of a compactness map is inherited by a termwise product of families: split the
target using the two projections and reassemble with `productComplex_id`. -/
private theorem surjective_cofanMap_productComplex (K : DerivedCategory (ModuleCat.{v} R))
    {ι : Type*} [DecidableEq ι] {P Q : ι → CochainComplex (ModuleCat.{v} R) ℤ}
    {S T : CochainComplex (ModuleCat.{v} R) ℤ} (j : ∀ i, P i ⟶ S) (k : ∀ i, Q i ⟶ T)
    (hj : Function.Surjective (cofanMap K fun i => DerivedCategory.Q.map (j i)))
    (hk : Function.Surjective (cofanMap K fun i => DerivedCategory.Q.map (k i))) :
    Function.Surjective
      (cofanMap K fun i => DerivedCategory.Q.map (productComplexMap (j i) (k i))) := by
  intro f
  obtain ⟨a, ha⟩ := hj (f ≫ DerivedCategory.Q.map (productComplexFst S T))
  obtain ⟨b, hb⟩ := hk (f ≫ DerivedCategory.Q.map (productComplexSnd S T))
  have hl (i : ι) : DerivedCategory.Q.map (j i) ≫
      DerivedCategory.Q.map (productComplexInl S T) =
        DerivedCategory.Q.map (productComplexInl (P i) (Q i)) ≫
          DerivedCategory.Q.map (productComplexMap (j i) (k i)) := by
    simpa only [Functor.map_comp] using
      (congrArg DerivedCategory.Q.map (productComplexMap_inl (j i) (k i))).symm
  have hr (i : ι) : DerivedCategory.Q.map (k i) ≫
      DerivedCategory.Q.map (productComplexInr S T) =
        DerivedCategory.Q.map (productComplexInr (P i) (Q i)) ≫
          DerivedCategory.Q.map (productComplexMap (j i) (k i)) := by
    simpa only [Functor.map_comp] using
      (congrArg DerivedCategory.Q.map (productComplexMap_inr (j i) (k i))).symm
  refine ⟨DirectSum.map (fun i =>
      Preadditive.rightComp K (DerivedCategory.Q.map (productComplexInl (P i) (Q i)))) a +
    DirectSum.map (fun i =>
      Preadditive.rightComp K (DerivedCategory.Q.map (productComplexInr (P i) (Q i)))) b, ?_⟩
  rw [map_add, cofanMap_naturality K _ _ _ _ hl, cofanMap_naturality K _ _ _ _ hr, ha, hb,
    Category.assoc, Category.assoc, ← Preadditive.comp_add, ← Functor.map_comp,
    ← Functor.map_comp, ← Functor.map_add, productComplex_id, CategoryTheory.Functor.map_id,
    Category.comp_id]

/-! ### The Mayer–Vietoris sequence of the reductions of a flat complex -/

/-- The difference of the two reductions, `M/IM × M/JM → M/(I+J)M`. -/
private abbrev quotientIdealDifference (I J : Ideal R) (M : ModuleCat.{v} R) :
    (M ⧸ (I • (⊤ : Submodule R M))) × (M ⧸ (J • (⊤ : Submodule R M))) →ₗ[R]
      M ⧸ ((I ⊔ J) • (⊤ : Submodule R M)) :=
  ((I • (⊤ : Submodule R M)).mapQ ((I ⊔ J) • ⊤) LinearMap.id
    (by simpa using Submodule.smul_mono_left (le_sup_left : I ≤ I ⊔ J))).comp
      (LinearMap.fst R _ _) -
  ((J • (⊤ : Submodule R M)).mapQ ((I ⊔ J) • ⊤) LinearMap.id
    (by simpa using Submodule.smul_mono_left (le_sup_right : J ≤ I ⊔ J))).comp
      (LinearMap.snd R _ _)

private theorem quotientIdealDifference_mk (I J : Ideal R) (M : ModuleCat.{v} R) (x y : M) :
    quotientIdealDifference I J M
        ((I • (⊤ : Submodule R M)).mkQ x, (J • (⊤ : Submodule R M)).mkQ y) =
      ((I ⊔ J) • (⊤ : Submodule R M)).mkQ (x - y) := by
  simp [quotientIdealDifference]

private def quotientComplexDiagonal (I J : Ideal R) (K : CochainComplex (ModuleCat.{v} R) ℤ) :
    K ⟶ productComplex (quotientComplex I K) (quotientComplex J K) where
  f i := ModuleCat.ofHom (quotientDiagonal (I • (⊤ : Submodule R (K.X i))) (J • ⊤))
  comm' i j _ := by ext x; rfl

private def quotientComplexDifference (I J : Ideal R) (K : CochainComplex (ModuleCat.{v} R) ℤ) :
    productComplex (quotientComplex I K) (quotientComplex J K) ⟶ quotientComplex (I ⊔ J) K where
  f i := ModuleCat.ofHom (quotientIdealDifference I J (K.X i))
  comm' i j _ := by
    ext z
    obtain ⟨x, y, rfl⟩ := exists_mkQ_prod_eq (I • (⊤ : Submodule R (K.X i))) (J • ⊤) z
    change ((quotientFunctor (I ⊔ J)).map (K.d i j)).hom
      (quotientIdealDifference I J (K.X i)
        ((I • (⊤ : Submodule R (K.X i))).mkQ x, (J • (⊤ : Submodule R (K.X i))).mkQ y)) =
      quotientIdealDifference I J (K.X j)
        (((quotientFunctor I).map (K.d i j)).hom ((I • (⊤ : Submodule R (K.X i))).mkQ x),
          ((quotientFunctor J).map (K.d i j)).hom ((J • (⊤ : Submodule R (K.X i))).mkQ y))
    rw [quotientIdealDifference_mk, quotientFunctor_map_mk, quotientFunctor_map_mk,
      quotientFunctor_map_mk, quotientIdealDifference_mk, map_sub]

/-- The Mayer–Vietoris short complex `K → K/IK ⊕ K/JK → K/(I+J)K` of complexes. -/
private def quotientComplexShortComplex (I J : Ideal R) (K : CochainComplex (ModuleCat.{v} R) ℤ) :
    ShortComplex (CochainComplex (ModuleCat.{v} R) ℤ) :=
  ShortComplex.mk (quotientComplexDiagonal I J K) (quotientComplexDifference I J K) (by
    ext i x
    change quotientIdealDifference I J (K.X i)
      ((I • (⊤ : Submodule R (K.X i))).mkQ x, (J • (⊤ : Submodule R (K.X i))).mkQ x) = 0
    rw [quotientIdealDifference_mk, sub_self, map_zero])

/-- For a complex with flat terms and ideals meeting in zero the Mayer–Vietoris sequence is
degreewise short exact: flatness gives `IM ∩ JM = (I ∩ J)M = 0` ([stacks 0BBY]). -/
private theorem quotientComplexShortComplex_shortExact (I J : Ideal R) (hIJ : I ⊓ J = ⊥)
    (K : CochainComplex (ModuleCat.{v} R) ℤ) [∀ i, Module.Flat R (K.X i)] :
    (quotientComplexShortComplex I J K).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  exact quotientShortComplex_shortExact_of_sup_eq
    (I • (⊤ : Submodule R (K.X i))) (J • ⊤) ((I ⊔ J) • ⊤)
    (Submodule.sup_smul I J ⊤).symm
    (Submodule.smul_mono_left le_sup_left) (Submodule.smul_mono_left le_sup_right)
    (by rw [ideal_smul_top_inf, hIJ, Submodule.bot_smul])

/-- Naturality of the Mayer–Vietoris short complex in the complex. -/
private def quotientComplexShortComplexMap (I J : Ideal R)
    {K L : CochainComplex (ModuleCat.{v} R) ℤ} (f : K ⟶ L) :
    quotientComplexShortComplex I J K ⟶ quotientComplexShortComplex I J L where
  τ₁ := f
  τ₂ := productComplexMap
    (((quotientFunctor I).mapHomologicalComplex (ComplexShape.up ℤ)).map f)
    (((quotientFunctor J).mapHomologicalComplex (ComplexShape.up ℤ)).map f)
  τ₃ := ((quotientFunctor (I ⊔ J)).mapHomologicalComplex (ComplexShape.up ℤ)).map f
  comm₁₂ := by ext i x; rfl
  comm₂₃ := by
    ext i z
    obtain ⟨x, y, rfl⟩ := exists_mkQ_prod_eq (I • (⊤ : Submodule R (K.X i))) (J • ⊤) z
    change quotientIdealDifference I J (L.X i)
      (((quotientFunctor I).map (f.f i)).hom ((I • (⊤ : Submodule R (K.X i))).mkQ x),
        ((quotientFunctor J).map (f.f i)).hom ((J • (⊤ : Submodule R (K.X i))).mkQ y)) =
      ((quotientFunctor (I ⊔ J)).map (f.f i)).hom
        (quotientIdealDifference I J (K.X i)
          ((I • (⊤ : Submodule R (K.X i))).mkQ x, (J • (⊤ : Submodule R (K.X i))).mkQ y))
    rw [quotientFunctor_map_mk, quotientFunctor_map_mk, quotientIdealDifference_mk,
      quotientIdealDifference_mk, quotientFunctor_map_mk]
    exact (congrArg (((I ⊔ J) • (⊤ : Submodule R (L.X i))).mkQ)
      (map_sub (f.f i).hom x y)).symm

/-- A coproduct of complexes with flat terms has flat terms, coproducts of complexes being
computed degreewise. -/
private theorem flat_coproduct_complex {ι : Type (max u v)}
    (P : ι → CochainComplex (ModuleCat.{max u v} R) ℤ) [∀ i n, Module.Flat R ((P i).X n)] (n : ℤ) :
    Module.Flat R ((∐ P).X n) := by
  classical
  let hc := (isColimitMapCoconeCofanMkEquiv
    (HomologicalComplex.eval (ModuleCat.{max u v} R) (ComplexShape.up ℤ) n) P (Sigma.ι P))
    (HomotopyCategoryCoproduct.cdeg (ModuleCat.{max u v} R) P n)
  let e := hc.coconePointUniqueUpToIso
    (ModuleCat.coproductCoconeIsColimit (fun i => (P i).X n))
  have : Module.Flat R (ModuleCat.coproductCocone (fun i => (P i).X n)).pt :=
    inferInstanceAs (Module.Flat R (DirectSum ι fun i => (P i).X n))
  exact Module.Flat.of_linearEquiv e.toLinearEquiv

/-- For a family of complexes with flat terms, and `I ∩ J = 0`, the compactness map of `K` against
the coproduct inclusions is surjective once `K` is perfect modulo `I`, `J` and `I + J`: this is
five-term exactness along the Mayer–Vietoris triangles. -/
private theorem surjective_cofanMap_sigma_ι_of_reductions (I J : Ideal R) (hIJ : I ⊓ J = ⊥)
    (K : DerivedCategory (ModuleCat.{max u v} R))
    (hI : IsPerfect
      ((totalDerivedExtensionScalars.{u, u, v} (Ideal.Quotient.mk I)).functor.obj K))
    (hJ : IsPerfect
      ((totalDerivedExtensionScalars.{u, u, v} (Ideal.Quotient.mk J)).functor.obj K))
    (hS : IsPerfect
      ((totalDerivedExtensionScalars.{u, u, v} (Ideal.Quotient.mk (I ⊔ J))).functor.obj K))
    {ι : Type (max u v)} [DecidableEq ι] (P : ι → CochainComplex (ModuleCat.{max u v} R) ℤ)
    [∀ i n, Module.Flat R ((P i).X n)] :
    Function.Surjective (cofanMap K fun i => DerivedCategory.Q.map (Sigma.ι P i)) := by
  have : ∀ n, Module.Flat R ((∐ P).X n) := flat_coproduct_complex P
  let T (i : ι) := DerivedCategory.triangleOfSES
    (quotientComplexShortComplex_shortExact I J hIJ (P i))
  let U := DerivedCategory.triangleOfSES
    (quotientComplexShortComplex_shortExact I J hIJ (∐ P))
  let φ (i : ι) : T i ⟶ U := DerivedCategory.triangleOfSES.map
    (quotientComplexShortComplex_shortExact I J hIJ (P i))
    (quotientComplexShortComplex_shortExact I J hIJ (∐ P))
    (quotientComplexShortComplexMap I J (Sigma.ι P i))
  apply surjective_cofanMap_of_triangleHom K T U φ
    (fun i => DerivedCategory.triangleOfSES_distinguished _)
    (DerivedCategory.triangleOfSES_distinguished _)
  · exact surjective_cofanMap_productComplex K _ _
      (bijective_cofanMap_quotient I K hI _ (coproductIsCoproduct P)).surjective
      (bijective_cofanMap_quotient J K hJ _ (coproductIsCoproduct P)).surjective
  · exact (bijective_cofanMap_quotient (I ⊔ J) K hS _ (coproductIsCoproduct P)).injective
  · exact (bijective_cofanMap_quotient_shift (I ⊔ J) K hS _
      (coproductIsCoproduct P) (-1)).surjective

/-- If `P i` represents `E i` in the derived category and the compactness map of `K` against the
coproduct inclusions of the `P i` is surjective, then the compactness map of `K` against `∐ E` is
bijective. -/
theorem bijective_cofanMap_sigma_ι_of_surjective (K : DerivedCategory (ModuleCat.{max u v} R))
    {ι : Type (max u v)} [DecidableEq ι] (E : ι → DerivedCategory (ModuleCat.{max u v} R))
    [HasCoproduct E] (P : ι → CochainComplex (ModuleCat.{max u v} R) ℤ)
    (e : ∀ i, E i ≅ DerivedCategory.Q.obj (P i))
    (hsurj : Function.Surjective (cofanMap K fun i => DerivedCategory.Q.map (Sigma.ι P i))) :
    Function.Bijective (cofanMap K (Limits.Sigma.ι E)) := by
  have : PreservesColimitsOfShape (Discrete ι)
      (DerivedCategory.Q (C := ModuleCat.{max u v} R)) :=
    preservesColimitsOfShape_discrete_Q_moduleCat.{u, v} ι
  have hc : IsColimit (Cofan.mk (DerivedCategory.Q.obj (∐ P))
      fun i => DerivedCategory.Q.map (Sigma.ι P i)) :=
    (isColimitMapCoconeCofanMkEquiv DerivedCategory.Q P (Sigma.ι P))
      (isColimitOfPreserves DerivedCategory.Q (coproductIsCoproduct P))
  have : HasCoproduct (fun i => DerivedCategory.Q.obj (P i)) := ⟨_, hc⟩
  let eSum : (∐ E) ≅ DerivedCategory.Q.obj (∐ P) :=
    HasColimit.isoOfNatIso (F := Discrete.functor E)
      (G := Discrete.functor fun i => DerivedCategory.Q.obj (P i))
      (Discrete.natIso fun ⟨i⟩ => e i) ≪≫
      (coproductIsCoproduct fun i => DerivedCategory.Q.obj (P i)).coconePointUniqueUpToIso hc
  have heSum (i : ι) : Sigma.ι E i ≫ eSum.hom =
      (e i).hom ≫ DerivedCategory.Q.map (Sigma.ι P i) := by
    dsimp only [eSum, Iso.trans_hom]
    rw [← Category.assoc, HasColimit.ι_isoOfNatIso_hom, Category.assoc]
    exact congrArg (fun f => (e i).hom ≫ f)
      (IsColimit.comp_coconePointUniqueUpToIso_hom
        (coproductIsCoproduct fun i => DerivedCategory.Q.obj (P i)) hc ⟨i⟩)
  exact bijective_cofanMap_of_iso K _ _ (fun i => (e i).symm) eSum.symm
    (fun i => by
      apply (cancel_mono eSum.hom).mp
      simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id, heSum,
        Iso.inv_hom_id_assoc])
    ⟨injective_cofanMap K _ hc, hsurj⟩

/-- **The case `I ∩ J = 0` of [stacks 09AS].** If `I ∩ J = 0` and the derived reductions of `K`
modulo `I` and modulo `J` are perfect, then `K` is itself perfect. -/
theorem isPerfect_of_isPerfect_reductions (I J : Ideal R) (hIJ : I ⊓ J = ⊥)
    (K : DerivedCategory (ModuleCat.{max u v} R))
    (hI : IsPerfect
      ((totalDerivedExtensionScalars.{u, u, v} (Ideal.Quotient.mk I)).functor.obj K))
    (hJ : IsPerfect
      ((totalDerivedExtensionScalars.{u, u, v} (Ideal.Quotient.mk J)).functor.obj K)) :
    IsPerfect K := by
  classical
  have hS : IsPerfect
      ((totalDerivedExtensionScalars.{u, u, v} (Ideal.Quotient.mk (I ⊔ J))).functor.obj K) :=
    isPerfect_of_iso ((derivedReductionComp I (I ⊔ J) le_sup_left).app K).symm
      (isPerfect_derivedExtensionScalars
        (Ideal.Quotient.factor (le_sup_left : I ≤ I ⊔ J)) _ hI)
  apply (isPerfect_iff_isCompactObject_max K).mpr
  constructor
  intro ι _ E _
  choose P hP hflat e₀ using fun i => exists_kFlat_representative.{u, v} (R := R) (E i)
  have : ∀ i n, Module.Flat R ((P i).X n) := hflat
  change Function.Bijective (cofanMap K (Limits.Sigma.ι E))
  exact bijective_cofanMap_sigma_ι_of_surjective K E P (fun i => (e₀ i).some)
    (surjective_cofanMap_sigma_ι_of_reductions I J hIJ K hI hJ hS P)

end ReductionComplex

/-! ### The product of two ideals -/

section Product

variable {R : Type u} [CommRing R]

/-- The image of `I ∩ J` in `R/IJ` is nilpotent: its square already vanishes, since
`(I ∩ J)² ⊆ IJ`. -/
private theorem isNilpotent_map_inf_quotient_mul (I J : Ideal R) :
    IsNilpotent ((I ⊓ J).map (Ideal.Quotient.mk (I * J))) := by
  refine ⟨2, ?_⟩
  rw [pow_two, ← Ideal.map_mul, Submodule.zero_eq_bot, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  exact Ideal.mul_mono inf_le_left inf_le_right

/-- The images of `I` and of `J` in `R/(I ∩ J)` meet in zero. -/
private theorem map_inf_quotient_inf_eq_bot (I J : Ideal R) :
    I.map (Ideal.Quotient.mk (I ⊓ J)) ⊓ J.map (Ideal.Quotient.mk (I ⊓ J)) = ⊥ := by
  apply Ideal.comap_injective_of_surjective
    (Ideal.Quotient.mk (I ⊓ J)) Ideal.Quotient.mk_surjective
  rw [Ideal.comap_inf, Ideal.comap_map_mk inf_le_left, Ideal.comap_map_mk inf_le_right]
  exact Ideal.mk_ker.symm

/-- **Stacks 09AS.** Let `I` and `J` be ideals of a commutative ring `R` and let `K` be an object
of the derived category of `R`-modules. If the derived reductions of `K` modulo `I` and modulo `J`
are both perfect, then so is the derived reduction of `K` modulo `I * J`.

Perfectness modulo `I ∩ J` follows from `isPerfect_of_isPerfect_reductions`, applied over the ring
`R/(I ∩ J)` where the images of `I` and of `J` meet in zero; and `R/(I * J) → R/(I ∩ J)` is
surjective with nilpotent kernel, so perfectness descends along it. -/
@[stacks 09AS]
theorem isPerfect_derivedReduction_mul (I J : Ideal R)
    (K : DerivedCategory (ModuleCat.{max u v} R))
    (hI : IsPerfect
      ((totalDerivedExtensionScalars.{u, u, v} (Ideal.Quotient.mk I)).functor.obj K))
    (hJ : IsPerfect
      ((totalDerivedExtensionScalars.{u, u, v} (Ideal.Quotient.mk J)).functor.obj K)) :
    IsPerfect
      ((totalDerivedExtensionScalars.{u, u, v} (Ideal.Quotient.mk (I * J))).functor.obj K) := by
  have hp : IsPerfect
      ((totalDerivedExtensionScalars.{u, u, v} (Ideal.Quotient.mk (I ⊓ J))).functor.obj K) :=
    isPerfect_of_isPerfect_reductions.{u, v}
      (I.map (Ideal.Quotient.mk (I ⊓ J))) (J.map (Ideal.Quotient.mk (I ⊓ J)))
      (map_inf_quotient_inf_eq_bot I J) _
      (isPerfect_derivedReduction_map (I ⊓ J) I inf_le_left K hI)
      (isPerfect_derivedReduction_map (I ⊓ J) J inf_le_right K hJ)
  have hle : I * J ≤ I ⊓ J := le_inf Ideal.mul_le_left Ideal.mul_le_right
  apply isPerfect_of_derivedExtensionScalars_surjective (Ideal.Quotient.factor hle)
    (Ideal.Quotient.factor_surjective hle)
    (by rw [Ideal.Quotient.factor_ker]; exact isNilpotent_map_inf_quotient_mul I J)
  exact isPerfect_of_iso ((derivedReductionComp (I * J) (I ⊓ J) hle).app K) hp

end Product

end StacksDraft.Perfect

end
