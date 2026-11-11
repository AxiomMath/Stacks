module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautRepresentability
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteType

/-!
# Finite type morphisms of formal spectra

Let `S` be a scheme and let `φ : A → B` be a continuous homomorphism of weakly admissible
topological rings over `S`. **Stacks 0ANT** says that `Spf (φ) : Spf B → Spf A` is of finite
type exactly when `φ` is taut and `B` is topologically of finite type over `A`.

## Main results

* `TopologicalRing.isTopologicallyOfFiniteType_of_finiteTypeModuloEveryWeakIdeal`: a taut
  homomorphism which is of finite type modulo every weak ideal of definition is topologically
  of finite type.
* `AlgebraicGeometry.FormalSpace.finiteType_quotientMap_of_isFiniteType_formalSpectrumMap`:
  if `Spf (φ)` is of finite type and `φ` is taut, then `A ⧸ I → B ⧸ J(I)` is of finite type
  for every weak ideal of definition `I` of `A`.
* `AlgebraicGeometry.FormalSpace.isTopologicallyOfFiniteType_of_isFiniteType_formalSpectrumMap`:
  the implication (1) ⟹ (2) of Stacks 0ANT for a taut homomorphism.
* `AlgebraicGeometry.FormalSpace.exists_isPullback_isFiniteTypeULift_formalSpectrumMap_stage`:
  the base change of `Spf (φ)` along a thickening stage, a step of the implication (2) ⟹ (1)
  of Stacks 0ANT.

## Implementation notes

The ring-theoretic half is the argument of Stacks 0ANT: generators of `B ⧸ J(I)` over `A ⧸ I`
are lifted to `b₁, …, b_r ∈ B`, and for a smaller weak ideal of definition `I' ⊆ I` the
identity `B ⧸ (J(I') + I B) = B ⧸ J(I)` — which holds because `J(I)` is the closure of `I B`
and `J(I')` is open — lets Stacks 07RD upgrade surjectivity of `(A ⧸ I')[x] → B ⧸ J(I)` to
surjectivity of `(A ⧸ I')[x] → B ⧸ J(I')`. Since the ideals `J(I')` form a neighbourhood basis
of zero, the map `A[x₁, …, x_r] → B` has dense image. This is independent of the countability
hypotheses of `TopologicalRing.finiteType_tfae`, which proves the same implication through a
fundamental sequence of weak ideals of definition.

The geometric half extracts the ring condition from the morphism of fppf sheaves. For a taut
`φ` the square with vertices `Spec (B ⧸ J(I))`, `Spec (A ⧸ I)`, `Spf B` and `Spf A` is
cartesian, which is
`AlgebraicGeometry.FormalSpace.isPullback_formalSpectrumMap_stage_of_isTaut`. Base changing the
finite type condition along that square and reading it on the identity étale chart of
`Spec (B ⧸ J(I)) → Spec (A ⧸ I)` gives that this morphism of affine schemes is locally of
finite type, i.e. that `A ⧸ I → B ⧸ J(I)` is a finite type ring map.

### Where Stacks 0ANT is proved

The two results of this file are the stagewise pieces of Stacks 0ANT: the implication
(1) ⟹ (2) for a homomorphism already known to be taut, and the base change of `Spf (φ)` along
a thickening stage. The equivalence itself, with both conditions read verbatim and tautness
deduced from condition (1), is
`FormalSpace.isFiniteType_formalSpectrumMap_iff_isTaut_and_isTopologicallyOfFiniteType`
in `StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFiniteTypeRepresentable`.

## References

* [Stacks Project, Tag 0ANT](https://stacks.math.columbia.edu/tag/0ANT)
* [Stacks Project, Tag 0AJK](https://stacks.math.columbia.edu/tag/0AJK)
* [Stacks Project, Tag 0ANS](https://stacks.math.columbia.edu/tag/0ANS)
* [Stacks Project, Tag 0ANU](https://stacks.math.columbia.edu/tag/0ANU)
* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
* [Stacks Project, Tag 07RD](https://stacks.math.columbia.edu/tag/07RD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace TopologicalRing

section Algebra

universe u v

variable {A : Type u} [CommRing A] [TopologicalSpace A]
  {B : Type v} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

/-- A taut homomorphism of linearly topologized rings whose source is weakly pre-admissible
and which is of finite type modulo every weak ideal of definition is topologically of finite
type. This is the implication of **Stacks 0ANT** from its condition on the thickening stages
to its density condition, and it needs no countability assumption. -/
theorem isTopologicallyOfFiniteType_of_finiteTypeModuloEveryWeakIdeal
    (φ : A →+* B) (hA : IsWeaklyPreAdmissible A)
    (h : FiniteTypeModuloEveryWeakIdeal φ) :
    IsTopologicallyOfFiniteType φ := by
  classical
  obtain ⟨htaut, hft⟩ := h
  obtain ⟨I, hI⟩ := hA
  -- Generators of `B ⧸ J(I)` over `A ⧸ I`, lifted to elements `b i` of `B`.
  let _ : Algebra (A ⧸ I) (B ⧸ Ideal.closure (I.map φ)) :=
    (Ideal.quotientMap (Ideal.closure (I.map φ)) φ
      (Ideal.map_le_iff_le_comap.mp subset_closure)).toAlgebra
  obtain ⟨r, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (RingHom.finiteType_algebraMap.mp (hft I hI))
  choose b hb using fun i : Fin r ↦
    Ideal.Quotient.mk_surjective (I := Ideal.closure (I.map φ)) (g (MvPolynomial.X i))
  let Φ : MvPolynomial (Fin r) A →+* B := MvPolynomial.eval₂Hom φ b
  -- `A[x₁, …, x_r] → B ⧸ J(I)` is surjective.
  have hsurjI : Function.Surjective
      ((Ideal.Quotient.mk (Ideal.closure (I.map φ))).comp Φ) := by
    have hring : (Ideal.Quotient.mk (Ideal.closure (I.map φ))).comp Φ =
        g.toRingHom.comp (MvPolynomial.map (Ideal.Quotient.mk I)) := by
      refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)
      · have hcom := g.commutes (Ideal.Quotient.mk I a)
        rw [MvPolynomial.algebraMap_eq] at hcom
        simp only [RingHom.comp_apply, MvPolynomial.map_C, Φ, MvPolynomial.eval₂Hom_C]
        rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hcom]
        exact Ideal.quotientMap_mk.symm
      · simp only [RingHom.comp_apply, MvPolynomial.map_X, Φ, MvPolynomial.eval₂Hom_X',
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
        exact hb i
    rw [hring]
    exact hg.comp (MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective)
  -- `A[x₁, …, x_r] → B ⧸ J(I')` is surjective for every weak ideal of definition `I' ⊆ I`.
  have key : ∀ I' : Ideal A, IsWeakIdealOfDefinition I' → I' ≤ I →
      Function.Surjective ((Ideal.Quotient.mk (Ideal.closure (I'.map φ))).comp Φ) := by
    intro I' hI' hle
    let _ : Algebra (A ⧸ I') (B ⧸ Ideal.closure (I'.map φ)) :=
      (Ideal.quotientMap (Ideal.closure (I'.map φ)) φ
        (Ideal.map_le_iff_le_comap.mp subset_closure)).toAlgebra
    have hftR : Algebra.FiniteType (A ⧸ I') (B ⧸ Ideal.closure (I'.map φ)) :=
      RingHom.finiteType_algebraMap.mp (hft I' hI')
    let N : Ideal (A ⧸ I') := I.map (Ideal.Quotient.mk I')
    have hN : N.IsLocallyNilpotent := by
      intro x hx
      have himg : (N : Set (A ⧸ I')) = Ideal.Quotient.mk I' '' (I : Set A) := by
        change (Ideal.map (Ideal.Quotient.mk I') I : Set (A ⧸ I')) = _
        exact Ideal.map_eq_image_of_surjective _ Ideal.Quotient.mk_surjective
      change x ∈ (N : Set (A ⧸ I')) at hx
      rw [himg] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp
        ((hI.2 a ha).eventually (hI'.1.mem_nhds I'.zero_mem))
      refine ⟨k, ?_⟩
      change Ideal.Quotient.mk I' (a ^ k) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact hk k le_rfl
    let fAlg : MvPolynomial (Fin r) (A ⧸ I') →ₐ[A ⧸ I'] B ⧸ Ideal.closure (I'.map φ) :=
      MvPolynomial.aeval (fun i ↦ Ideal.Quotient.mk (Ideal.closure (I'.map φ)) (b i))
    have hcomp : (Ideal.Quotient.mk (Ideal.closure (I'.map φ))).comp Φ =
        fAlg.toRingHom.comp (MvPolynomial.map (Ideal.Quotient.mk I')) := by
      refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)
      · simp only [RingHom.comp_apply, MvPolynomial.map_C, Φ, MvPolynomial.eval₂Hom_C,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe, fAlg, MvPolynomial.aeval_C]
        exact Ideal.quotientMap_mk.symm
      · simp only [RingHom.comp_apply, MvPolynomial.map_X, Φ, MvPolynomial.eval₂Hom_X',
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe, fAlg, MvPolynomial.aeval_X]
    -- `J(I)` is contained in `J(I') + I B`, since the latter is open hence closed.
    have hsup : Ideal.closure (I.map φ) ≤ Ideal.closure (I'.map φ) ⊔ I.map φ := by
      have hopen : IsOpen ((Ideal.closure (I'.map φ) ⊔ I.map φ : Ideal B) : Set B) :=
        AddSubgroup.isOpen_mono
          (H₁ := (Ideal.closure (I'.map φ)).toAddSubgroup)
          (H₂ := (Ideal.closure (I'.map φ) ⊔ I.map φ : Ideal B).toAddSubgroup)
          (fun x hx ↦ (le_sup_left : Ideal.closure (I'.map φ) ≤ _) hx) (htaut.1 I' hI'.1)
      refine SetLike.coe_subset_coe.mp ?_
      rw [Ideal.coe_closure]
      exact closure_minimal (SetLike.coe_subset_coe.mpr le_sup_right)
        ((Ideal.closure (I'.map φ) ⊔ I.map φ : Ideal B).toAddSubgroup.isClosed_of_isOpen hopen)
    -- surjectivity of `(A ⧸ I')[x] → B ⧸ J(I')` modulo the extended ideal
    have hext : _root_.extendedIdeal N (B ⧸ Ideal.closure (I'.map φ)) =
        (I.map φ).map (Ideal.Quotient.mk (Ideal.closure (I'.map φ))) := by
      change Ideal.map (algebraMap (A ⧸ I') (B ⧸ Ideal.closure (I'.map φ)))
        (I.map (Ideal.Quotient.mk I')) = _
      rw [Ideal.map_map, Ideal.map_map]
      congr 1
    have hmod : Function.Surjective
        ((Ideal.Quotient.mk (_root_.extendedIdeal N (B ⧸ Ideal.closure (I'.map φ)))).comp
          fAlg.toRingHom) := by
      intro z
      obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective w
      obtain ⟨p, hp⟩ := hsurjI (Ideal.Quotient.mk (Ideal.closure (I.map φ)) y)
      obtain ⟨j, hj, w', hw', hsum⟩ := Submodule.mem_sup.mp (hsup (Ideal.Quotient.eq.mp hp.symm))
      refine ⟨MvPolynomial.map (Ideal.Quotient.mk I') p, ?_⟩
      have hfp : fAlg.toRingHom (MvPolynomial.map (Ideal.Quotient.mk I') p) =
          Ideal.Quotient.mk (Ideal.closure (I'.map φ)) (Φ p) :=
        (congrArg (fun ρ : MvPolynomial (Fin r) A →+*
          B ⧸ Ideal.closure (I'.map φ) ↦ ρ p) hcomp).symm
      simp only [RingHom.comp_apply, hfp]
      refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr ?_
      rw [hext]
      have hdiff : Ideal.Quotient.mk (Ideal.closure (I'.map φ)) (Φ p) -
          Ideal.Quotient.mk (Ideal.closure (I'.map φ)) y =
          -Ideal.Quotient.mk (Ideal.closure (I'.map φ)) w' := by
        rw [← map_sub]
        have : Φ p - y = -(j + w') := by rw [hsum]; ring
        rw [this, map_neg, map_add,
          (Ideal.Quotient.eq_zero_iff_mem (I := Ideal.closure (I'.map φ))).mpr hj]
        ring
      rw [hdiff]
      exact neg_mem (Ideal.mem_map_of_mem _ hw')
    have hsurj := surjective_of_surjective_mod_locallyNilpotent N hN fAlg hmod hftR
    intro y
    obtain ⟨q, hq⟩ := hsurj y
    obtain ⟨p, hp⟩ := MvPolynomial.map_surjective (Ideal.Quotient.mk I')
      Ideal.Quotient.mk_surjective q
    refine ⟨p, ?_⟩
    have := congrArg (fun ρ : MvPolynomial (Fin r) A →+*
      B ⧸ Ideal.closure (I'.map φ) ↦ ρ p) hcomp
    simp only [RingHom.comp_apply] at this ⊢
    rw [this, hp]
    exact hq
  -- Density of `A[x₁, …, x_r] → B`.
  refine ⟨r, Φ, by ext a; simp [Φ], ?_⟩
  rw [denseRange_iff_closure_range]
  refine Set.eq_univ_iff_forall.mpr fun x ↦ mem_closure_iff.mpr fun U hUopen hxU ↦ ?_
  have hpre : (fun y : B ↦ x - y) ⁻¹' U ∈ nhds (0 : B) := by
    have hc : ContinuousAt (fun y : B ↦ x - y) 0 :=
      (continuous_const.sub continuous_id).continuousAt
    exact hc.preimage_mem_nhds (by simpa using hUopen.mem_nhds hxU)
  obtain ⟨I', hI'open, hI'sub⟩ := htaut.2.mem_iff.mp hpre
  obtain ⟨p, hp⟩ := key (I ⊓ I') (isWeakIdealOfDefinition_inf_of_isOpen_right hI hI'open)
    inf_le_left (Ideal.Quotient.mk _ x)
  have hmem : x - Φ p ∈ Ideal.closure (I'.map φ) := by
    have h1 : x - Φ p ∈ Ideal.closure ((I ⊓ I').map φ) := Ideal.Quotient.eq.mp hp.symm
    have hle2 : Ideal.closure ((I ⊓ I').map φ) ≤ Ideal.closure (I'.map φ) :=
      SetLike.coe_subset_coe.mp (by
        rw [Ideal.coe_closure, Ideal.coe_closure]
        exact closure_mono (SetLike.coe_subset_coe.mpr (Ideal.map_mono inf_le_right)))
    exact hle2 h1
  exact ⟨Φ p, by simpa using hI'sub hmem, ⟨p, rfl⟩⟩

end Algebra

end TopologicalRing

namespace AlgebraicGeometry.FormalSpace

section Geometry

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The identity of a universe-lifted Yoneda presheaf is an étale chart of itself: every
represented base change of it is an isomorphism of the site, hence an étale morphism of
schemes. -/
theorem relative_etale_id (T : BigFppfOver B S hS) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1})
        (𝟙 ((uliftYoneda.{u + 1}).obj T)) := by
  refine ⟨Functor.relativelyRepresentable.of_isIso (uliftYoneda.{u + 1}) _, ?_⟩
  intro X Y g fst snd hpb
  have h1 : IsIso ((uliftYoneda.{u + 1}).map snd) := hpb.isIso_snd_of_isIso
  have h2 : IsIso snd :=
    Functor.FullyFaithful.isIso_of_isIso_map (ULiftYoneda.fullyFaithful _) snd
  change AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map snd)
  infer_instance

/-- Reading the every-étale-chart condition of a morphism of the site on the identity charts
of its source and target returns the property for the underlying morphism of schemes. This is
the converse of `AlgebraicGeometry.Space.holdsOnEveryEtaleChartULift_uliftYoneda_map`. -/
theorem prop_of_holdsOnEveryEtaleChartULift {P : MorphismProperty Scheme.{u}}
    {V U : BigFppfOver B S hS} (k : V ⟶ U)
    (h : Space.HoldsOnEveryEtaleChartULift.{u + 1} B S hS P ((uliftYoneda.{u + 1}).map k)) :
    P ((BigFppfOver.toScheme B S hS).map k) :=
  h V U (𝟙 _) (𝟙 _) k (relative_etale_id B S hS V) (relative_etale_id B S hS U) (by simp)

/-- On the big fppf site of `S`, which is subcanonical, the presheaf represented by an object
is already a sheaf, so it agrees with the underlying presheaf of its sheafification. -/
noncomputable def sheafifiedYonedaObjIso (X : BigFppfOver B S hS) :
    (uliftYoneda.{u + 1}).obj X ≅
      (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).obj
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj X) :=
  letI : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).mapIso
    ((Sheaf.uliftYonedaIsoSheafifiedYoneda (BigFppfOver.topology B S hS)).app X)

/-- The comparison isomorphism between a represented presheaf and the underlying presheaf of
its sheafification is natural. -/
theorem sheafifiedYonedaObjIso_naturality {X Y : BigFppfOver B S hS} (k : X ⟶ Y) :
    (uliftYoneda.{u + 1}).map k ≫ (sheafifiedYonedaObjIso B S hS Y).hom =
      (sheafifiedYonedaObjIso B S hS X).hom ≫
        (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).map
          ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map k) := by
  let _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  exact (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).congr_map
    ((Sheaf.uliftYonedaIsoSheafifiedYoneda (BigFppfOver.topology B S hS)).hom.naturality k)

variable {B S hS}
variable {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
  [IsLinearTopology C C]

/-- The stage square of a taut homomorphism, pasted with the comparison between represented
presheaves and sheafified ones, is cartesian. -/
private theorem isPullback_stage_paste
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (hf : RingHom.IsTaut f.toRingHom)
    (I : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :
    ∃ (K : { K : Ideal C // TopologicalRing.IsWeakIdealOfDefinition K })
      (_ : K.1 = (I.1.map f.toRingHom).closure) (hIK : I.1 ≤ Ideal.comap f.toRingHom K.1),
      IsPullback
        ((sheafifiedYonedaObjIso B S hS ((BigAffineFppf.inclusion B S hS).obj (E.stage K))).hom ≫
          (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).map
            (formalSpectrumInclusion E K))
        ((uliftYoneda.{u + 1}).map ((BigAffineFppf.inclusion B S hS).map (f.stageMap I K hIK)))
        ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).map
          (formalSpectrumMap hA f))
        ((sheafifiedYonedaObjIso B S hS ((BigAffineFppf.inclusion B S hS).obj (D.stage I))).hom ≫
          (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).map
            (formalSpectrumInclusion D I)) := by
  obtain ⟨K, hKeq, hIK, hsq⟩ :=
    isPullback_formalSpectrumMap_stage_of_isTaut B S hS hA hC D E f hf I
  refine ⟨K, hKeq, hIK, ?_⟩
  have hleft := IsPullback.of_horiz_isIso ⟨(sheafifiedYonedaObjIso_naturality B S hS
    ((BigAffineFppf.inclusion B S hS).map (f.stageMap I K hIK))).symm⟩
  exact hleft.paste_horiz (hsq.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))))

/-- **Stacks 0ANT, the stage half of (1) ⟹ (2).** Let `φ : A ⟶ C` be a taut continuous
homomorphism of weakly admissible topological rings over `S`. If `Spf (φ)` is of finite type,
then for every weak ideal of definition `I` of `A` the induced ring map
`A ⧸ I → C ⧸ J(I)`, with `J(I)` the closure of `φ(I)C`, is of finite type. -/
theorem finiteType_quotientMap_of_isFiniteType_formalSpectrumMap
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (hf : RingHom.IsTaut f.toRingHom) (hFT : IsFiniteType B S hS (formalSpectrumMap hA f))
    (I : Ideal A) (hI : TopologicalRing.IsWeakIdealOfDefinition I) :
    (Ideal.quotientMap (Ideal.closure (I.map f.toRingHom)) f.toRingHom
      (Ideal.map_le_iff_le_comap.mp subset_closure)).FiniteType := by
  obtain ⟨hrep, hprop⟩ := hFT
  obtain ⟨⟨Kv, hKw⟩, hKeq, hIK, hpaste⟩ := isPullback_stage_paste hA hC D E f hf ⟨I, hI⟩
  subst hKeq
  set G := sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)) with hG
  set k := (BigAffineFppf.inclusion B S hS).map
    (f.stageMap ⟨I, hI⟩ ⟨Ideal.closure (I.map f.toRingHom), hKw⟩ hIK) with hk
  have hlft : Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS
      (pullback.fst ((sheafifiedYonedaObjIso B S hS
          ((BigAffineFppf.inclusion B S hS).obj (D.stage ⟨I, hI⟩))).hom ≫
        G.map (formalSpectrumInclusion D ⟨I, hI⟩)) (G.map (formalSpectrumMap hA f))) :=
    (hprop _ _).1
  have hchart := Space.holdsOnEveryEtaleChartULift_precomp B S hS
    (@AlgebraicGeometry.LocallyOfFiniteType.{u}) hpaste.flip.isoPullback.hom _ hlft
  have hchart' : Space.HoldsOnEveryEtaleChartULift.{u + 1} B S hS
      (@AlgebraicGeometry.LocallyOfFiniteType.{u}) ((uliftYoneda.{u + 1}).map k) := by
    rw [← hpaste.flip.isoPullback_hom_fst]
    exact hchart
  have hk' := prop_of_holdsOnEveryEtaleChartULift B S hS k hchart'
  rw [hk] at hk'
  exact AlgebraicGeometry.HasRingHomProperty.Spec_iff.mp
    (show AlgebraicGeometry.LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
      (Ideal.quotientMap (Ideal.closure (I.map f.toRingHom)) f.toRingHom hIK))) from hk')

/-- Let `φ : A ⟶ C` be a taut continuous homomorphism of weakly admissible topological rings
over `S`. If `Spf (φ)` is of finite type, then `C` is topologically of finite type over `A`.
This is a step of Stacks 0ANT; the equivalence, with tautness deduced, is
`isFiniteType_formalSpectrumMap_iff_isTaut_and_isTopologicallyOfFiniteType`. -/
theorem isTopologicallyOfFiniteType_of_isFiniteType_formalSpectrumMap
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (hf : RingHom.IsTaut f.toRingHom) (hFT : IsFiniteType B S hS (formalSpectrumMap hA f)) :
    TopologicalRing.IsTopologicallyOfFiniteType f.toRingHom :=
  TopologicalRing.isTopologicallyOfFiniteType_of_finiteTypeModuloEveryWeakIdeal
    f.toRingHom hA.1
    ⟨hf, fun I hI ↦ finiteType_quotientMap_of_isFiniteType_formalSpectrumMap
      hA hC D E f hf hFT I hI⟩

add_to_stacks 0AJK "part (4), the conclusion that `B` is topologically of finite type over `A` \
for a finite type `f : Y → X` with `Y` McQuillan, and with it part (4)'s restatement that `f` \
factors as `Y → A^r_X → X` with the first arrow a closed immersion: the conclusion \
`TopologicalRing.IsTopologicallyOfFiniteType` produces the integer `r` together with a \
homomorphism `A[x_1, ..., x_r] → B` restricting to `φ` on constants and having dense image, \
which is that factorization and the dense image of its first arrow. Tautness of `φ`, part \
(4)'s other conclusion, is carried here as a hypothesis rather than deduced. Part (4) closes \
by observing that questions (1) and (2) are then in force for `Y → A^r_X`; those are \
questions and are asserted nowhere."
  isTopologicallyOfFiniteType_of_isFiniteType_formalSpectrumMap

/-- A step of the implication (2) ⟹ (1) of Stacks 0ANT. Let `φ : A ⟶ C` be a continuous
homomorphism of weakly admissible topological rings over `S` which is taut and of finite type
modulo every weak ideal of definition, and let `I` be a weak ideal of definition of `A`. Then
the base change of `Spf (φ)` along the point of `Spf A` cut out by the thickening stage
`Spec (A ⧸ I)` is represented by an object of the site, and the representing morphism is of
finite type. -/
theorem exists_isPullback_isFiniteTypeULift_formalSpectrumMap_stage
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (h : TopologicalRing.FiniteTypeModuloEveryWeakIdeal f.toRingHom)
    (I : Ideal A) (hI : TopologicalRing.IsWeakIdealOfDefinition I) :
    ∃ (V : BigFppfOver B S hS)
      (p : V ⟶ (BigAffineFppf.inclusion B S hS).obj (D.stage ⟨I, hI⟩))
      (q : (uliftYoneda.{u + 1}).obj V ⟶
        (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).obj (formalSpectrum E)),
      IsPullback q ((uliftYoneda.{u + 1}).map p)
        ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).map
          (formalSpectrumMap hA f))
        ((sheafifiedYonedaObjIso B S hS
            ((BigAffineFppf.inclusion B S hS).obj (D.stage ⟨I, hI⟩))).hom ≫
          (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).map
            (formalSpectrumInclusion D ⟨I, hI⟩)) ∧
      Space.IsFiniteTypeULift.{u + 1} B S hS ((uliftYoneda.{u + 1}).map p) := by
  obtain ⟨⟨Kv, hKw⟩, hKeq, hIK, hpaste⟩ := isPullback_stage_paste hA hC D E f h.1 ⟨I, hI⟩
  subst hKeq
  set k := (BigAffineFppf.inclusion B S hS).map
    (f.stageMap ⟨I, hI⟩ ⟨Ideal.closure (I.map f.toRingHom), hKw⟩ hIK) with hk
  have hlft : AlgebraicGeometry.LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map k) := by
    rw [hk]
    exact (show AlgebraicGeometry.LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
      (Ideal.quotientMap (Ideal.closure (I.map f.toRingHom)) f.toRingHom hIK))) from
      AlgebraicGeometry.HasRingHomProperty.Spec_iff.mpr (h.2 I hI))
  have hqc : AlgebraicGeometry.QuasiCompact ((BigFppfOver.toScheme B S hS).map k) := by
    rw [hk]
    exact (show AlgebraicGeometry.QuasiCompact (Spec.map (CommRingCat.ofHom
      (Ideal.quotientMap (Ideal.closure (I.map f.toRingHom)) f.toRingHom hIK))) from
      inferInstance)
  exact ⟨_, k, _, hpaste, Space.isFiniteTypeULift_uliftYoneda_map B S hS k hlft hqc⟩

end Geometry

end AlgebraicGeometry.FormalSpace

end
