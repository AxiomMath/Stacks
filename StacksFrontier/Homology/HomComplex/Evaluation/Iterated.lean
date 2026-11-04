module

public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import StacksFrontier.Algebra.Homology.InjectiveDimension
public import StacksFrontier.Algebra.Homology.PseudoCoherent
public import StacksFrontier.Algebra.Homology.Resolution.InjectiveResolution
public import StacksFrontier.Homology.HomComplex.DerivedAdjunction
public import StacksFrontier.Homology.HomComplex.Evaluation
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.LargeUniverse
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.Perfect.Defs
public import StacksFrontier.Homology.TensorComplex.ExactFunctor
public import StacksFrontier.Homology.TensorComplex.Monoidal
public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksFrontier.Homology.TorAmplitude.KFlatRepresentative
import StacksCore.Tactic.EgaSgaAttribute

/-!
# When evaluation into an iterated derived Hom is an isomorphism

Let `R` be a commutative ring and let `K`, `L`, `M` be objects of the derived category `D(R)`
of `R`-modules. The canonical evaluation morphism
`RHom_R(L, M) ⊗ᴸ_R K ⟶ RHom_R(RHom_R(K, L), M)` of `StacksDraft.DerivedHom`
`exists_evaluationToIteratedDerivedHom` is an isomorphism as soon as `K` is perfect, and also
as soon as `K` is pseudo-coherent, `L` is cohomologically bounded below and `M` has finite
injective dimension. It is also an isomorphism, without any bound on `K` itself, as soon as `L`
and `M` have finite injective dimension, `RHom_R(L, M)` has finite Tor dimension, and every
truncation `τ_{≤ n} K` is pseudo-coherent.

## Main results

* `StacksDraft.DerivedHom.evaluationToIteratedDerivedHom_isIso`: the two cases, a perfect first
  argument and a pseudo-coherent one against bounds on the other two, in which the canonical
  evaluation morphism is an isomorphism.
* `StacksDraft.DerivedHom.evaluationToIteratedDerivedHom_isIso_of_truncLE_pseudoCoherent`: the
  same conclusion under finite injective dimension of `L` and `M`, finite Tor dimension of
  `RHom_R(L, M)`, and pseudo-coherence of every truncation of `K`.
* `StacksDraft.DerivedHom.homComplexR_isStrictlyLE` and
  `StacksDraft.DerivedHom.homComplexR_isStrictlyGE`: a Hom complex vanishes outside the
  difference of the strict bounds of its two arguments.
* `StacksDraft.DerivedHom.derivedHom_isLE_of_isGE_of_injectiveAmplitude` and
  `StacksDraft.DerivedHom.derivedHom_isGE_of_isLE_of_injectiveAmplitude`: derived Hom into an
  object of bounded injective amplitude exchanges cohomological bounds.

## Implementation notes

The two cases of the first result are combined into a single disjunctive hypothesis, as in the
source. Both are reduced to the chain-level statement: the evaluation morphism of complexes
`ChainEvaluation.chainEvaluation` is an isomorphism for a bounded complex of finite projective
modules, and for a bounded above such complex against a bounded below source and a bounded
above target. Passing from a chain-level isomorphism to a derived one uses the comparison
clause of Tag 0A67 at a K-flat first argument and K-injective second and third arguments, and
then transport along isomorphisms of `D(R)`, which is available because the evaluation family
is natural in all three variables.

The second result compares the evaluation morphism, viewed as a natural transformation between
two exact functors of `K`, on the truncations `τ_{≤ n} K` — where the first result applies —
and controls the error term `τ_{≥ n+1} K` by cohomological bounds. Exactness of tensoring is
obtained by lifting the exactness of the chain-level total tensor product (Tag 064J) along the
localization; exactness of iterated derived Hom comes from the degreewise split short exact
sequence attached to a distinguished triangle, mapped into a K-injective Hom complex. Finite
Tor dimension of `RHom_R(L, M)` is converted into a K-flat representative of flat modules by
Tag 0BYL. That tag is stated for a certified derived tensor bifunctor rather than for the
tensor product of the tensor--Hom adjunction used here, so `nonempty_tensorSingleIso` bridges
the two: both are computed by the total tensor product of K-flat representatives, so they agree
up to isomorphism at a module placed in degree zero, which is all the Tor-amplitude condition
sees.

## References

* [Stacks Project, Tag 0A68](https://stacks.math.columbia.edu/tag/0A68)
* [Stacks Project, Tag 0A69](https://stacks.math.columbia.edu/tag/0A69)
-/

@[expose] public noncomputable section


universe u

open CategoryTheory CochainComplex MonoidalCategory

namespace StacksDraft.DerivedHom

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R]

/-- A chain-level isomorphism of the evaluation morphism transfers, through the comparison
clause of Tag 0A67, to the derived evaluation morphism at the represented objects. -/
private theorem evaluation_isIso_of_model
    (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (hK : K.KFlat)
    [L.IsKInjective] [M.IsKInjective]
    (h : IsIso (ChainEvaluation.chainEvaluation K L M)) :
    IsIso (Classical.choose (exists_evaluationToIteratedDerivedHom (R := R))
      (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)) := by
  rw [← (Classical.choose_spec
    (exists_evaluationToIteratedDerivedHom (R := R))).2.2.2 K L M hK]
  have : IsIso (((derivedHomAdjunction (R := R)).homIso L M).hom,
      𝟙 (DerivedCategory.Q.obj K)) := (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  have : IsIso (((derivedHomAdjunction (R := R)).homIso K L).hom.op,
      𝟙 (DerivedCategory.Q.obj M)) := (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  infer_instance

/-- A functor on a product category sends a pair of isomorphisms to an isomorphism. -/
private theorem isIso_map_prod {C₁ C₂ E : Type*} [Category C₁] [Category C₂] [Category E]
    (F : C₁ × C₂ ⥤ E) {X₁ Y₁ : C₁} {X₂ Y₂ : C₂} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    [IsIso f] [IsIso g] : IsIso (F.map ((f, g) : (X₁, X₂) ⟶ (Y₁, Y₂))) :=
  have : IsIso ((f, g) : (X₁, X₂) ⟶ (Y₁, Y₂)) := (isIso_prod_iff _ _).2 ⟨‹_›, ‹_›⟩
  inferInstance

/-- If `g` is conjugate to an isomorphism by two isomorphisms, it is an isomorphism. -/
private theorem isIso_of_comp_eq_comp {C : Type*} [Category C] {A B A' B' : C}
    (g : A' ⟶ B') (a : A ⟶ A') (f : A ⟶ B) (b : B ⟶ B') [IsIso a] [IsIso f] [IsIso b]
    (h : a ≫ g = f ≫ b) : IsIso g := by
  have : IsIso (a ≫ g) := by rw [h]; infer_instance
  exact IsIso.of_isIso_comp_left a g

/-- If `g` composed with an isomorphism is conjugate to an isomorphism, `g` is an isomorphism. -/
private theorem isIso_of_comp_eq_comp' {C : Type*} [Category C] {A B A' B' : C}
    (g : A ⟶ B) (b : B ⟶ B') (a : A ⟶ A') (f : A' ⟶ B') [IsIso b] [IsIso a] [IsIso f]
    (h : g ≫ b = a ≫ f) : IsIso g := by
  have : IsIso (g ≫ b) := by rw [h]; infer_instance
  exact IsIso.of_isIso_comp_right g b

/-- Being an isomorphism is invariant under replacing each of the three arguments of the
canonical evaluation morphism by an isomorphic object. -/
private theorem evaluation_isIso_of_iso
    {K K' L L' M M' : DerivedCategory (ModuleCat.{u} R)}
    (iK : K ≅ K') (iL : L ≅ L') (iM : M ≅ M')
    (h : IsIso (Classical.choose
      (exists_evaluationToIteratedDerivedHom (R := R)) K L M)) :
    IsIso (Classical.choose
      (exists_evaluationToIteratedDerivedHom (R := R)) K' L' M') := by
  let D := derivedHomAdjunction (R := R)
  let e := Classical.choose (exists_evaluationToIteratedDerivedHom (R := R))
  have he := Classical.choose_spec (exists_evaluationToIteratedDerivedHom (R := R))
  have hK : IsIso (e K' L M) := by
    have : IsIso (e K L M) := h
    have := isIso_map_prod D.tensor (𝟙 (D.hom.obj (Opposite.op L, M))) iK.hom
    let f : (Opposite.op K', L) ⟶ (Opposite.op K, L) := (iK.hom.op, 𝟙 L)
    have := isIso_map_prod D.hom iK.hom.op (𝟙 L)
    have := isIso_map_prod D.hom (D.hom.map f).op (𝟙 M)
    exact isIso_of_comp_eq_comp _ _ _ _ (he.1 iK.hom (L := L) (M := M))
  have hL : IsIso (e K' L' M) := by
    have : IsIso (e K' L M) := hK
    let f : (Opposite.op L', M) ⟶ (Opposite.op L, M) := (iL.hom.op, 𝟙 M)
    let g : (Opposite.op K', L) ⟶ (Opposite.op K', L') := (𝟙 _, iL.hom)
    have := isIso_map_prod D.hom iL.hom.op (𝟙 M)
    have := isIso_map_prod D.tensor (D.hom.map f) (𝟙 K')
    have := isIso_map_prod D.hom (𝟙 (Opposite.op K')) iL.hom
    have := isIso_map_prod D.hom (D.hom.map g).op (𝟙 M)
    exact isIso_of_comp_eq_comp' _ _ _ _ (he.2.1 iL.hom (K := K') (M := M)).symm
  have : IsIso (e K' L' M) := hL
  let f : (Opposite.op L', M) ⟶ (Opposite.op L', M') := (𝟙 _, iM.hom)
  have := isIso_map_prod D.hom (𝟙 (Opposite.op L')) iM.hom
  have := isIso_map_prod D.tensor (D.hom.map f) (𝟙 K')
  have := isIso_map_prod D.hom (𝟙 (Opposite.op (D.hom.obj (Opposite.op K', L')))) iM.hom
  exact isIso_of_comp_eq_comp (e K' L' M') _ (e K' L' M) _ (he.2.2.1 iM.hom (K := K') (L := L'))

/-- A cohomologically bounded below object of `D(R)` is represented by a K-injective complex
which vanishes in all sufficiently small degrees. -/
private theorem exists_boundedBelow_kInjectiveModel
    (X : DerivedCategory (ModuleCat.{u} R)) (hX : DerivedCategoryB.IsBoundedBelow X) :
    ∃ (I : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ),
      I.IsStrictlyGE a ∧ I.IsKInjective ∧ Nonempty (DerivedCategory.Q.obj I ≅ X) := by
  obtain ⟨a, ha⟩ := hX
  obtain ⟨C, iC, hC⟩ := (DerivedCategory.isGE_iff X a).mpr ha
  have : C.IsStrictlyGE a := hC
  obtain ⟨J, -, hJ⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE a C
  have : J.cocomplex.IsStrictlyGE a := hJ
  exact ⟨J.cocomplex, a, hJ, CochainComplex.isKInjective_of_injective J.cocomplex a,
    ⟨(asIso (DerivedCategory.Q.map J.ι)).symm ≪≫ iC.symm⟩⟩

/-- **Stacks 0A68.** The canonical evaluation morphism
`RHom_R(L, M) ⊗ᴸ_R K ⟶ RHom_R(RHom_R(K, L), M)` is an isomorphism if `K` is
perfect, or if `K` is pseudo-coherent, `L` is cohomologically bounded below, and `M` has
finite injective dimension. -/
@[stacks 0A68]
public theorem evaluationToIteratedDerivedHom_isIso
    (K L M : DerivedCategory (ModuleCat R))
    (h : StacksDraft.Perfect.IsPerfect K ∨
      (StacksDraft.PseudoCoherence.IsPseudoCoherent K ∧
        DerivedCategoryB.IsBoundedBelow L ∧
        StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension M)) :
    let e := Classical.choose
      (exists_evaluationToIteratedDerivedHom (R := R))
    IsIso (e K L M) := by
  rcases h with hK | ⟨hK, hL, hM⟩
  · obtain ⟨P, a, b, hPa, hPb, hPf, hPp, ⟨iP⟩⟩ := hK
    have : P.IsStrictlyGE a := hPa
    have : P.IsStrictlyLE b := hPb
    have : ∀ s, Module.Finite R (P.X s) := hPf
    have : ∀ s, Module.Projective R (P.X s) := hPp
    have hP : P.KFlat := CochainComplex.KFlat.kFlat_of_flat P b
    obtain ⟨J, hJ, ⟨iJ⟩⟩ := exists_kInjective_model L
    obtain ⟨I, hI, ⟨iI⟩⟩ := exists_kInjective_model M
    have : J.IsKInjective := hJ
    have : I.IsKInjective := hI
    exact evaluation_isIso_of_iso iP.symm iJ iI (evaluation_isIso_of_model P J I hP
      (ChainEvaluation.chainEvaluation_isIso_of_bounded P J I a b))
  · obtain ⟨P, hP, ⟨iP⟩⟩ := hK
    obtain ⟨b, hb⟩ := hP.upperBound
    have : P.IsStrictlyLE b := hb
    have : ∀ s, Module.Finite R (P.X s) := fun s => (hP.finiteFree s).1
    have : ∀ s, Module.Free R (P.X s) := fun s => (hP.finiteFree s).2
    have hPf : P.KFlat := CochainComplex.KFlat.kFlat_of_flat P b
    obtain ⟨J, a, hJa, hJ, ⟨iJ⟩⟩ := exists_boundedBelow_kInjectiveModel L hL
    have : J.IsStrictlyGE a := hJa
    have : J.IsKInjective := hJ
    obtain ⟨c, d, I, hIc, hId, hIi, ⟨iI⟩⟩ := hM
    have : I.IsStrictlyGE c := hIc
    have : I.IsStrictlyLE d := hId
    have : ∀ s, Injective (I.X s) := hIi
    have : I.IsKInjective := CochainComplex.isKInjective_of_injective I c
    exact evaluation_isIso_of_iso iP iJ iI.symm (evaluation_isIso_of_model P J I hPf
      (ChainEvaluation.chainEvaluation_isIso_of_boundedAbove_boundedBelow P J I a b d))

/-! ### Stacks 0A69 -/

/-- An object of finite injective dimension is cohomologically bounded below. -/
private theorem isBoundedBelow_of_finiteInjectiveDimension
    (L : DerivedCategory (ModuleCat.{u} R))
    (hL : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension L) :
    DerivedCategoryB.IsBoundedBelow L := by
  obtain ⟨a, _, I, hI, _, _, ⟨e⟩⟩ := hL
  exact ⟨a, fun i hi => (DerivedCategory.isGE_iff L a).mp (⟨I, e, hI⟩ : L.IsGE a) i hi⟩

/-- A Hom complex term is zero if in each component the source or the target is zero. -/
private theorem isZero_cochain_of_forall_isZero_or
    (F G : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ)
    (h : ∀ p q : ℤ, p + i = q → Limits.IsZero (F.X p) ∨ Limits.IsZero (G.X q)) :
    Limits.IsZero (ModuleCat.of R (HomComplex.Cochain F G i)) := by
  have : Subsingleton (HomComplex.Cochain F G i) :=
    ⟨fun x y => by
      apply HomComplex.Cochain.ext
      intro p q hpq
      exact (h p q hpq).elim (fun hp => hp.eq_of_src _ _) (fun hq => hq.eq_of_tgt _ _)⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- The Hom complex out of a complex vanishing below `a`, into one vanishing above `b`,
vanishes above `b - a`. -/
theorem homComplexR_isStrictlyLE
    (F G : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (hF : F.IsStrictlyGE a) (hG : G.IsStrictlyLE b) :
    (HomComplexR R F G).IsStrictlyLE (b - a) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  refine isZero_cochain_of_forall_isZero_or F G i fun p q hpq => ?_
  by_cases hp : p < a
  · exact Or.inl (F.isZero_of_isStrictlyGE a p hp)
  · exact Or.inr (G.isZero_of_isStrictlyLE b q (by omega))

/-- If `Y` has injective amplitude in `[a, b]` and `X` is represented by `F`, then `Y` is
represented by a bounded K-injective complex `I` with `RHom(X, Y)` represented by `Hom(F, I)`. -/
private theorem exists_homComplexR_model
    (D : DerivedHomData R) (X Y : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ)
    (hY : StacksDraft.InjectiveDimension.HasInjectiveAmplitude Y a b)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (eF : X ≅ DerivedCategory.Q.obj F) :
    ∃ I : CochainComplex (ModuleCat.{u} R) ℤ, I.IsStrictlyGE a ∧ I.IsStrictlyLE b ∧
      Nonempty (D.hom.obj (Opposite.op X, Y) ≅ DerivedCategory.Q.obj (HomComplexR R F I)) := by
  obtain ⟨I, hIa, hIb, hIinj, ⟨eI⟩⟩ := hY
  have := hIa
  have : ∀ i : ℤ, Injective (I.X i) := hIinj
  have : I.IsKInjective := CochainComplex.isKInjective_of_injective I a
  exact ⟨I, hIa, hIb, ⟨D.hom.mapIso (Iso.prod eF.symm.op eI) ≪≫ D.homIso F I⟩⟩

/-- The derived Hom out of a cohomologically bounded below object, into one of bounded
injective amplitude, is cohomologically bounded above. -/
@[sga "6 I 7.1" "Upper half of 7.1 b)"]
theorem derivedHom_isLE_of_isGE_of_injectiveAmplitude
    (D : DerivedHomData R) (X Y : DerivedCategory (ModuleCat.{u} R)) (n a b : ℤ)
    (hX : X.IsGE n) (hY : StacksDraft.InjectiveDimension.HasInjectiveAmplitude Y a b) :
    (D.hom.obj (Opposite.op X, Y)).IsLE (b - n) := by
  obtain ⟨F, hF, ⟨eF⟩⟩ := X.exists_iso_Q_obj_of_isGE n
  obtain ⟨I, hIa, hIb, ⟨e⟩⟩ := exists_homComplexR_model D X Y a b hY F eF
  have := homComplexR_isStrictlyLE F I n b hF hIb
  exact DerivedCategory.TStructure.t.isLE_of_iso e.symm (b - n)

/-- The Hom complex out of a complex vanishing above `a`, into one vanishing below `b`,
vanishes below `b - a`. -/
theorem homComplexR_isStrictlyGE
    (F G : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (hF : F.IsStrictlyLE a) (hG : G.IsStrictlyGE b) :
    (HomComplexR R F G).IsStrictlyGE (b - a) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  refine isZero_cochain_of_forall_isZero_or F G i fun p q hpq => ?_
  by_cases hp : a < p
  · exact Or.inl (F.isZero_of_isStrictlyLE a p hp)
  · exact Or.inr (G.isZero_of_isStrictlyGE b q (by omega))

/-- The derived Hom out of a cohomologically bounded above object, into one of bounded
injective amplitude, is cohomologically bounded below. -/
@[sga "6 I 7.1" "Lower half of 7.1 b)"]
theorem derivedHom_isGE_of_isLE_of_injectiveAmplitude
    (D : DerivedHomData R) (X Y : DerivedCategory (ModuleCat.{u} R)) (n a b : ℤ)
    (hX : X.IsLE n) (hY : StacksDraft.InjectiveDimension.HasInjectiveAmplitude Y a b) :
    (D.hom.obj (Opposite.op X, Y)).IsGE (a - n) := by
  obtain ⟨F, hF, ⟨eF⟩⟩ := X.exists_iso_Q_obj_of_isLE n
  obtain ⟨I, hIa, hIb, ⟨e⟩⟩ := exists_homComplexR_model D X Y a b hY F eF
  have := homComplexR_isStrictlyGE F I n a hF hIa
  exact DerivedCategory.TStructure.t.isGE_of_iso e.symm (a - n)

/-- Iterating derived Hom into two objects of finite injective dimension shifts cohomological
lower bounds by a fixed amount. -/
private theorem iteratedDerivedHom_isGE_of_finiteInjectiveDimension
    (D : DerivedHomData R) (L M : DerivedCategory (ModuleCat.{u} R))
    (hL : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension L)
    (hM : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension M) :
    ∃ c : ℤ, ∀ (X : DerivedCategory (ModuleCat.{u} R)) (n : ℤ), X.IsGE n →
      (D.hom.obj (Opposite.op (D.hom.obj (Opposite.op X, L)), M)).IsGE (n - c) := by
  obtain ⟨a, b, hab⟩ := hL
  obtain ⟨d, e, hde⟩ := hM
  refine ⟨b - d, fun X n hX => ?_⟩
  have hA := derivedHom_isLE_of_isGE_of_injectiveAmplitude D X L n a b hX hab
  have hB := derivedHom_isGE_of_isLE_of_injectiveAmplitude D
    (D.hom.obj (Opposite.op X, L)) M (b - n) d e hA hde
  simpa only [show n - (b - d) = d - (b - n) by omega] using hB

open MonoidalCategory

/-- The total tensor product of two complexes vanishing below `a` and below `b` vanishes
below `a + b`. -/
private theorem tensor_isStrictlyGE
    (F G : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (hF : F.IsStrictlyGE a) (hG : G.IsStrictlyGE b) :
    (F ⊗ G).IsStrictlyGE (a + b) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  apply (Limits.IsZero.iff_id_eq_zero _).mpr
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  have hz : Limits.IsZero (F.X p ⊗ G.X q) := by
    by_cases hp : p < a
    · exact (tensorRight (G.X q)).map_isZero (F.isZero_of_isStrictlyGE a p hp)
    · have hq : q < b := by
        change p + q = i at hpq
        omega
      exact (tensorLeft (F.X p)).map_isZero (G.isZero_of_isStrictlyGE b q hq)
  exact hz.eq_of_src _ _

/-- The derived tensor product of the tensor--Hom adjunction and any certified derived tensor
bifunctor agree, up to isomorphism, when the second argument is a module placed in degree zero:
both are computed by the total tensor product of K-flat representatives. -/
private theorem nonempty_tensorSingleIso
    (D : DerivedHomData R) (T : CochainComplex.DerivedTensor.DerivedTensorProduct R)
    (X : DerivedCategory (ModuleCat.{u} R)) (N : ModuleCat.{u} R) :
    Nonempty (D.tensor.obj (X, (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N) ≅
      (T.tensor.obj X).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)) := by
  obtain ⟨P, p, hPlarge, -, hp, -⟩ :=
    CochainComplex.KFlat.exists_kFlat_resolution.{u, u} (DerivedCategory.Q.objPreimage X)
  have hP : P.KFlat := hPlarge
  have := hp
  let eX : X ≅ DerivedCategory.Q.obj P :=
    (DerivedCategory.Q.objObjPreimageIso X).symm ≪≫ (asIso (DerivedCategory.Q.map p)).symm
  obtain ⟨E, q, hElarge, -, hq, -⟩ :=
    CochainComplex.KFlat.exists_kFlat_resolution.{u, u} (DerivedCategory.Q.objPreimage
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N))
  have hE : E.KFlat := hElarge
  have := hq
  let eN : (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N ≅
      DerivedCategory.Q.obj E :=
    (DerivedCategory.Q.objObjPreimageIso _).symm ≪≫ (asIso (DerivedCategory.Q.map q)).symm
  exact ⟨D.tensor.mapIso (Iso.prod eX eN) ≪≫ D.tensorIso P E hE ≪≫
    (T.comparison P E hP hE).symm ≪≫
    ((T.tensor.mapIso eX).app (DerivedCategory.Q.obj E)).symm ≪≫
    ((T.tensor.obj X).mapIso eN).symm⟩

/-- An object whose derived tensor products with modules in degree zero have vanishing
cohomology outside `[a, b]` is represented by a K-flat complex of flat modules vanishing below
`a`. This is Stacks 0BYL, read through the comparison of the adjunction's derived tensor product
with a certified derived tensor bifunctor. -/
private theorem exists_kFlat_flat_representative_of_tensor_amplitude
    (D : DerivedHomData R) (X : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ)
    (hX : ∀ (N : ModuleCat.{u} R) (i : ℤ), i ∉ Set.Icc a b →
      Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
        (D.tensor.obj (X, (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)))) :
    ∃ F : CochainComplex (ModuleCat.{u} R) ℤ,
      F.KFlat ∧ (∀ i : ℤ, Module.Flat R (F.X i)) ∧ F.IsStrictlyGE a ∧
        Nonempty (X ≅ DerivedCategory.Q.obj F) :=
  (StacksDraft.TorAmplitude.hasTorAmplitudeAbove_iff_exists_kFlat_flat_representative
    (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R) X a).mp <| by
      intro N i hi
      obtain ⟨cmp⟩ := nonempty_tensorSingleIso D
        (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R) X N
      refine (hX N i ?_).of_iso
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso cmp).symm
      simp only [Set.mem_Icc, not_and_or, not_le]
      exact Or.inl hi

/-- Tensoring with an object represented by a K-flat complex of flats vanishing below `a`
shifts cohomological lower bounds by `a`. -/
private theorem tensor_isGE_of_flat_representative
    (D : DerivedHomData R) (X Y : DerivedCategory (ModuleCat.{u} R)) (a n : ℤ)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : F.KFlat) (hFa : F.IsStrictlyGE a)
    (eF : X ≅ DerivedCategory.Q.obj F) (hY : Y.IsGE n) :
    (D.tensor.obj (X, Y)).IsGE (a + n) := by
  obtain ⟨G, hG, ⟨eG⟩⟩ := Y.exists_iso_Q_obj_of_isGE n
  let e : D.tensor.obj (X, Y) ≅ DerivedCategory.Q.obj (G ⊗ F) :=
    D.tensorSwap X Y ≪≫ D.tensor.mapIso (Iso.prod eG eF) ≪≫ D.tensorIso G F hF
  have : (G ⊗ F).IsStrictlyGE (a + n) := by
    simpa only [add_comm] using tensor_isStrictlyGE G F n a hG hFa
  exact DerivedCategory.TStructure.t.isGE_of_iso e.symm (a + n)

private theorem tensorIso_naturality_left (D : DerivedHomData R)
    (K K' L : CochainComplex (ModuleCat.{u} R) ℤ) (hL : L.KFlat) (f : K ⟶ K') :
    D.tensor.map (DerivedCategory.Q.map f, 𝟙 (DerivedCategory.Q.obj L)) ≫
        (D.tensorIso K' L hL).hom =
      (D.tensorIso K L hL).hom ≫ DerivedCategory.Q.map (f ▷ L) := by
  have h := D.tensorIso_naturality f (𝟙 L) hL hL
  rwa [CategoryTheory.Functor.map_id, tensorHom_id] at h

private abbrev tensorRightDerived (D : DerivedHomData R)
    (L : DerivedCategory (ModuleCat.{u} R)) :
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R) :=
  (Functor.curry.obj D.tensor).flip.obj L

private def tensorRightDerivedFactors (D : DerivedHomData R)
    (L : CochainComplex (ModuleCat.{u} R) ℤ) (hL : L.KFlat) :
    DerivedCategory.Q ⋙ tensorRightDerived D (DerivedCategory.Q.obj L) ≅
      tensorRight L ⋙ DerivedCategory.Q :=
  NatIso.ofComponents (fun K => D.tensorIso K L hL)
    (fun f => tensorIso_naturality_left D _ _ L hL f)

private def tensorRightDerivedFactorsh (D : DerivedHomData R)
    (L : CochainComplex (ModuleCat.{u} R) ℤ) (hL : L.KFlat) :
    DerivedCategory.Qh ⋙ tensorRightDerived D (DerivedCategory.Q.obj L) ≅
      Tright L ⋙ DerivedCategory.Qh := by
  let q := HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)
  let W := (Functor.whiskeringLeft _ _ (DerivedCategory (ModuleCat.{u} R))).obj q
  apply W.preimageIso
  change q ⋙ (DerivedCategory.Qh ⋙ tensorRightDerived D (DerivedCategory.Q.obj L)) ≅
    q ⋙ (Tright L ⋙ DerivedCategory.Qh)
  refine (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)) _ ≪≫
    tensorRightDerivedFactors D L hL ≪≫ ?_
  exact Functor.isoWhiskerLeft (tensorRight L)
    (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (eqToIso (descendF_comp_quotient (TrightCochain L)
        (TrightCochain_preservesHomotopyRel L))).symm _ ≪≫
      Functor.associator _ _ _

private theorem tensorRightDerived_triangulated (D : DerivedHomData R)
    (L : CochainComplex (ModuleCat.{u} R) ℤ) (hL : L.KFlat) :
    ∃ h : (tensorRightDerived D (DerivedCategory.Q.obj L)).CommShift ℤ,
      letI := h
      (tensorRightDerived D (DerivedCategory.Q.obj L)).IsTriangulated := by
  let F := tensorRightDerived D (DerivedCategory.Q.obj L)
  let q := DerivedCategory.Qh (C := ModuleCat.{u} R)
  let W := HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)
  let : Localization.Lifting q W (Tright L ⋙ q) F :=
    ⟨tensorRightDerivedFactorsh D L hL⟩
  let := (TotalTensorComplex.tright_isTriangulated L).choose
  have : (Tright L).IsTriangulated := (TotalTensorComplex.tright_isTriangulated L).choose_spec
  let h := Functor.commShiftOfLocalization q W ℤ (Tright L ⋙ q) F
  let := h
  exact ⟨h, Functor.isTriangulated_of_precomp_iso
    (Localization.Lifting.iso q W (Tright L ⋙ q) F)⟩

private abbrev tensorLeftDerived (D : DerivedHomData R)
    (L : DerivedCategory (ModuleCat.{u} R)) :
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R) :=
  (Functor.curry.obj D.tensor).obj L

private def tensorRightDerivedIsoLeft (D : DerivedHomData R)
    {X X' : DerivedCategory (ModuleCat.{u} R)} (e : X ≅ X') :
    tensorRightDerived D X' ≅ tensorLeftDerived D X :=
  NatIso.ofComponents
    (fun Y => D.tensorSwap Y X' ≪≫ D.tensor.mapIso (Iso.prod e.symm (Iso.refl Y)))
    (fun {Y Y'} f => by
      change D.tensor.map (show (Y, X') ⟶ (Y', X') from (f, 𝟙 X')) ≫ (D.tensorSwap Y' X').hom ≫
          D.tensor.map (show (X', Y') ⟶ (X, Y') from (e.inv, 𝟙 Y')) =
        ((D.tensorSwap Y X').hom ≫
          D.tensor.map (show (X', Y) ⟶ (X, Y) from (e.inv, 𝟙 Y))) ≫
            D.tensor.map (show (X, Y) ⟶ (X, Y') from (𝟙 X, f))
      rw [← Category.assoc, D.tensorSwap_naturality]
      simp only [Category.assoc, D.toDerivedHomAdjunction.tensor_map_comp,
        Category.id_comp, Category.comp_id])

private theorem tensorLeftDerived_triangulated_of_representative
    (D : DerivedHomData R) (X : DerivedCategory (ModuleCat.{u} R))
    (L : CochainComplex (ModuleCat.{u} R) ℤ) (hL : L.KFlat)
    (e : X ≅ DerivedCategory.Q.obj L) :
    ∃ h : (tensorLeftDerived D X).CommShift ℤ,
      let := h
      (tensorLeftDerived D X).IsTriangulated := by
  obtain ⟨h, hh⟩ := tensorRightDerived_triangulated D L hL
  let := h
  have := hh
  let i := tensorRightDerivedIsoLeft D e
  let h' := Functor.CommShift.ofIso i ℤ
  let := h'
  have : NatTrans.CommShift i.hom ℤ := Functor.CommShift.ofIso_compatibility i ℤ
  exact ⟨h', Functor.isTriangulated_of_iso i⟩

open CategoryTheory.Pretriangulated HomComplex

private theorem isIso_homologyMap_mor₁_of_isZero
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang (DerivedCategory C)) (i : ℤ)
    (h₀ : Limits.IsZero ((DerivedCategory.homologyFunctor C (i - 1)).obj T.obj₃))
    (h₁ : Limits.IsZero ((DerivedCategory.homologyFunctor C i).obj T.obj₃)) :
    IsIso ((DerivedCategory.homologyFunctor C i).map T.mor₁) := by
  have : Mono ((DerivedCategory.homologyFunctor C i).map T.mor₁) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT (i - 1) i (by omega)).mpr
      (h₀.eq_zero_of_src _)
  have : Epi ((DerivedCategory.homologyFunctor C i).map T.mor₁) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i).mpr
      (h₁.eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi _

private theorem isIso_app_of_isGE_truncGE
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (F G : DerivedCategory C ⥤ DerivedCategory C)
    (hFtri : ∀ (T : Triangle (DerivedCategory C)), T ∈ distTriang (DerivedCategory C) →
      ∃ δ, Triangle.mk (F.map T.mor₁) (F.map T.mor₂) δ ∈ distTriang (DerivedCategory C))
    (hGtri : ∀ (T : Triangle (DerivedCategory C)), T ∈ distTriang (DerivedCategory C) →
      ∃ δ, Triangle.mk (G.map T.mor₁) (G.map T.mor₂) δ ∈ distTriang (DerivedCategory C))
    (α : F ⟶ G) (K : DerivedCategory C)
    (hα : ∀ n : ℤ, IsIso (α.app ((DerivedCategory.TStructure.t.truncLE n).obj K)))
    (hF : ∃ c : ℤ, ∀ n : ℤ,
      (F.obj ((DerivedCategory.TStructure.t.truncGE (n + 1)).obj K)).IsGE (n - c))
    (hG : ∃ c : ℤ, ∀ n : ℤ,
      (G.obj ((DerivedCategory.TStructure.t.truncGE (n + 1)).obj K)).IsGE (n - c)) :
    IsIso (α.app K) := by
  obtain ⟨cF, hcF⟩ := hF
  obtain ⟨cG, hcG⟩ := hG
  apply (DerivedCategory.isIso_iff _ _).mpr
  intro i
  let n : ℤ := i + max cF cG + 1
  let t := DerivedCategory.TStructure.t (C := C)
  let T := (t.triangleLEGE n (n + 1) rfl).obj K
  have hT : T ∈ distTriang (DerivedCategory C) :=
    t.triangleLEGE_distinguished n (n + 1) rfl K
  have hmap (H : DerivedCategory C ⥤ DerivedCategory C)
      (hHtri : ∃ δ, Triangle.mk (H.map T.mor₁) (H.map T.mor₂) δ ∈ distTriang _)
      (c : ℤ) (hc : (H.obj ((t.truncGE (n + 1)).obj K)).IsGE (n - c))
      (hci : i < n - c) :
      IsIso ((DerivedCategory.homologyFunctor C i).map (H.map ((t.truncLEι n).app K))) := by
    obtain ⟨δ, hδ⟩ := hHtri
    apply isIso_homologyMap_mor₁_of_isZero
      (Triangle.mk (H.map T.mor₁) (H.map T.mor₂) δ) hδ i
    · exact (DerivedCategory.isGE_iff _ _).mp hc (i - 1) (by omega)
    · exact (DerivedCategory.isGE_iff _ _).mp hc i hci
  have hF := hmap F (hFtri T hT) cF (hcF n) (by dsimp [n]; omega)
  have hG := hmap G (hGtri T hT) cG (hcG n) (by dsimp [n]; omega)
  have := hα n
  let H := DerivedCategory.homologyFunctor C i
  have hw : H.map (F.map ((t.truncLEι n).app K)) ≫ H.map (α.app K) =
      H.map (α.app ((t.truncLE n).obj K)) ≫ H.map (G.map ((t.truncLEι n).app K)) := by
    simpa only [H.map_comp, Functor.id_obj] using
      congrArg H.map (α.naturality ((t.truncLEι n).app K))
  have : IsIso (H.map (α.app ((t.truncLE n).obj K))) := by
    infer_instance
  exact IsIso.of_isIso_fac_left hw

private abbrev iteratedHomFunctor (D : DerivedHomData R)
    (L M : DerivedCategory (ModuleCat.{u} R)) :
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R) :=
  ((Functor.curry.obj D.hom).flip.obj L).rightOp ⋙
    (Functor.curry.obj D.hom).flip.obj M

private theorem exists_distinguished_iteratedHom
    (D : DerivedHomData R) (L M : DerivedCategory (ModuleCat.{u} R))
    (T : Triangle (DerivedCategory (ModuleCat.{u} R))) (hT : T ∈ distTriang _) :
    ∃ δ, Triangle.mk ((iteratedHomFunctor D L M).map T.mor₁)
      ((iteratedHomFunctor D L M).map T.mor₂) δ ∈ distTriang _ := by
  obtain ⟨δ, hδ⟩ := exists_distinguished_derivedHom D L T hT
  exact exists_distinguished_derivedHom D M _ hδ

/-- **Stacks 0A69.** The canonical evaluation morphism
`RHom_R(L, M) ⊗ᴸ_R K ⟶ RHom_R(RHom_R(K, L), M)` is an isomorphism if `L` and `M`
have finite injective dimension, `RHom_R(L, M)` has finite Tor dimension, and every
truncation `τ_{≤ n} K` is pseudo-coherent. -/
@[stacks 0A69]
public theorem evaluationToIteratedDerivedHom_isIso_of_truncLE_pseudoCoherent
    (K L M : DerivedCategory (ModuleCat R))
    (hL : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension L)
    (hM : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension M)
    (hTor :
      let D := derivedHomAdjunction (R := R)
      ∃ a b : ℤ, ∀ (N : ModuleCat R) (i : ℤ), i ∉ Set.Icc a b →
        Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj
          (D.tensor.obj
            (D.hom.obj (Opposite.op L, M),
              (DerivedCategory.singleFunctor (ModuleCat R) 0).obj N))))
    (hK : ∀ n : ℤ, StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((DerivedCategory.TStructure.t.truncLE n).obj K)) :
    let e := Classical.choose
      (exists_evaluationToIteratedDerivedHom (R := R))
    IsIso (e K L M) := by
  let D := derivedHomAdjunction (R := R)
  let X := D.hom.obj (Opposite.op L, M)
  obtain ⟨a, b, hab⟩ := hTor
  obtain ⟨P, hP, hPflat, hPa, ⟨eP⟩⟩ :=
    exists_kFlat_flat_representative_of_tensor_amplitude D X a b hab
  obtain ⟨hFshift, hFtri⟩ := tensorLeftDerived_triangulated_of_representative D X P hP eP
  let := hFshift
  have := hFtri
  let e := Classical.choose (exists_evaluationToIteratedDerivedHom (R := R))
  let α : tensorLeftDerived D X ⟶ iteratedHomFunctor D L M :=
    { app := fun Y => e Y L M
      naturality := fun {_ _} f => (Classical.choose_spec
        (exists_evaluationToIteratedDerivedHom (R := R))).1 f }
  apply isIso_app_of_isGE_truncGE (tensorLeftDerived D X) (iteratedHomFunctor D L M)
    (fun T hT => ⟨_, (tensorLeftDerived D X).map_distinguished T hT⟩)
    (exists_distinguished_iteratedHom D L M) α K
  · intro n
    exact evaluationToIteratedDerivedHom_isIso _ L M
      (Or.inr ⟨hK n, isBoundedBelow_of_finiteInjectiveDimension L hL, hM⟩)
  · refine ⟨-a - 1, fun n => ?_⟩
    have h := tensor_isGE_of_flat_representative D X
      ((DerivedCategory.TStructure.t.truncGE (n + 1)).obj K) a (n + 1) P hP hPa eP
      (by infer_instance)
    simpa only [tensorLeftDerived, Functor.curry_obj_obj_obj,
      show n - (-a - 1) = a + (n + 1) by omega] using h
  · obtain ⟨c, hc⟩ := iteratedDerivedHom_isGE_of_finiteInjectiveDimension D L M hL hM
    refine ⟨c - 1, fun n => ?_⟩
    have h := hc ((DerivedCategory.TStructure.t.truncGE (n + 1)).obj K) (n + 1)
      (by infer_instance)
    simpa only [iteratedHomFunctor, Functor.comp_obj, Functor.rightOp_obj,
      Functor.flip_obj_obj, Functor.curry_obj_obj_obj,
      show n - (c - 1) = n + 1 - c by omega] using h

end StacksDraft.DerivedHom

end
