module

public import Mathlib.Algebra.MvPolynomial.Cardinal
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.AlgebraicGeometry.Sites.Representability
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.RepresentedBy
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.FreeOnAffineOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Representability
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.RelativeMorphisms
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.BootstrapEtaleSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartComparisonAssembly
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Stability
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RelativeMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RelativeMorphismsFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Diagonal
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeHomRepresentableAffineTarget.HomEquivalences

/-!
# Representability on the slice with a bound on the size

The relative morphism functor on the slice of all schemes over `Q`, for a finite locally free `z`
and a coproduct-of-affines target `x`, is represented by a scheme whose size is bounded in terms of
`Q` and `X`: the affine case via the bounded universal algebra of Stacks 05Y6, then charts by
affine opens of the target.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u v w u'

namespace AlgebraicGeometry.RelativeHomAffineTarget

private lemma exists_isPullback_yoneda_of_lift_iff
    {C : Type*} [Category.{u} C] {F G : Cᵒᵖ ⥤ Type u}
    (α : F ⟶ G) [Mono α] {V T : C} (i : V ⟶ T) [Mono i]
    (ξ : yoneda.obj T ⟶ G)
    (h : ∀ (W : C) (t : W ⟶ T),
      (∃ η : F.obj (Opposite.op W), α.app _ η = ξ.app _ t) ↔
        ∃ l : W ⟶ V, l ≫ i = t) :
    ∃ δ : yoneda.obj V ⟶ F, IsPullback δ (yoneda.map i) α ξ := by
  obtain ⟨η, hη⟩ := (h V i).mpr ⟨𝟙 V, by simp⟩
  let δ : yoneda.obj V ⟶ F := yonedaEquiv.symm η
  have hw : δ ≫ α = yoneda.map i ≫ ξ := by
    apply yonedaEquiv.injective
    simpa only [yonedaEquiv_comp, δ, Equiv.apply_symm_apply,
      yonedaEquiv_yoneda_map] using hη
  refine ⟨δ, IsPullback.of_forall_isPullback_app (fun W => ?_)⟩
  rw [Types.isPullback_iff]
  refine ⟨congrArg (fun τ => τ.app W) hw, ?_, ?_⟩
  · intro l₁ l₂ hl
    exact (cancel_mono i).mp hl.2
  · intro η' t ht
    obtain ⟨l, hl⟩ := (h W.unop t).mp ⟨η', ht⟩
    refine ⟨l, ?_, hl⟩
    apply (CategoryTheory.mono_iff_injective (α.app W)).mp inferInstance
    have he := congrArg (fun τ : yoneda.obj V ⟶ G => τ.app W l) hw
    change α.app W (δ.app W l) = ξ.app W (l ≫ i) at he
    rwa [hl, ← ht] at he

private lemma range_subset_kernImage_iff_of_isPullback
    {Z T T' Z' : Scheme.{u}} {f : Z ⟶ T} {t : T' ⟶ T}
    {a : Z' ⟶ Z} {f' : Z' ⟶ T'} (h : IsPullback a f' f t) (A : Set Z) :
    Set.range t ⊆ Set.kernImage f A ↔ Set.range a ⊆ A := by
  have hr : Set.range a = f ⁻¹' Set.range t := by
    simpa only [Set.preimage_univ, Set.image_univ] using
      Scheme.image_preimage_eq_of_isPullback h.flip Set.univ
  rw [Set.subset_kernImage_iff, hr]

private lemma exists_open_fiberwise_preimage_of_isPullback
    {Z T X : Scheme.{u}} (f : Z ⟶ T) [UniversallyClosed f]
    (b : Z ⟶ X) (U : X.Opens) :
    ∃ V : T.Opens, ∀ {T' Z' : Scheme.{u}} (t : T' ⟶ T)
      (a : Z' ⟶ Z) (f' : Z' ⟶ T'), IsPullback a f' f t →
      (Set.range t ⊆ V ↔ Set.range (a ≫ b) ⊆ U) := by
  let V : T.Opens := ⟨Set.kernImage f (b ⁻¹ᵁ U),
    (isClosedMap_iff_kernImage.mp f.isClosedMap) (b ⁻¹ᵁ U).isOpen⟩
  refine ⟨V, fun t a f' h => ?_⟩
  rw [show (V : Set T) = Set.kernImage f (b ⁻¹ᵁ U) from rfl,
    range_subset_kernImage_iff_of_isPullback h]
  simp only [Set.range_subset_iff, Scheme.Hom.comp_apply, Set.mem_preimage,
    TopologicalSpace.Opens.map_coe]

private lemma over_exists_lift_iff_range_subset
    {S : Scheme.{u}} {U X W : Over S} (j : U ⟶ X)
    [IsOpenImmersion j.left] (b : W ⟶ X) :
    (∃ l : W ⟶ U, l ≫ j = b) ↔ Set.range b.left ⊆ Set.range j.left := by
  constructor
  · rintro ⟨l, rfl⟩
    exact Set.range_comp_subset_range l.left j.left
  · intro h
    let l := IsOpenImmersion.lift j.left b.left h
    have hl : l ≫ j.left = b.left := IsOpenImmersion.lift_fac _ _ _
    refine ⟨Over.homMk l ?_, ?_⟩
    · rw [← Over.w j, ← Category.assoc, hl]
      exact Over.w b
    · ext
      exact hl

private lemma isPullback_prod_snd
    {C : Type*} [Category C] [HasBinaryProducts C] {W T : C}
    (Z : C) (t : W ⟶ T) :
    IsPullback (prod.map (𝟙 Z) t) (prod.snd : Z ⨯ W ⟶ W)
      (prod.snd : Z ⨯ T ⟶ T) t := by
  refine IsPullback.mk' (by simp) ?_ ?_
  · intro M φ ψ h₁ h₂
    apply prod.hom_ext
    · simpa using congrArg (fun k => k ≫ (prod.fst : Z ⨯ T ⟶ Z)) h₁
    · exact h₂
  · intro M a b h
    refine ⟨prod.lift (a ≫ prod.fst) b, ?_, by simp⟩
    apply prod.hom_ext <;> simp [h]

/-- A base-change-stable property of `Z.hom` passes to the projection `Z ⨯ T ⟶ T`. -/
private lemma prod_snd_left_of_hom {S : Scheme.{u}} (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] (Z T : Over S) (h : P Z.hom) :
    P (prod.snd : Z ⨯ T ⟶ T).left :=
  MorphismProperty.of_isPullback
    (Over.isPullback_of_binaryFan_isLimit
      (BinaryFan.mk (prod.fst : Z ⨯ T ⟶ Z) prod.snd) (prodIsProd Z T)) h

private lemma presheaf_isOpenImmersion_relativeHomPostcomp
    {S : Scheme.{u}} (Z X' X : Over S) [UniversallyClosed Z.hom]
    (j : X' ⟶ X) [IsOpenImmersion j.left] :
    (MorphismProperty.inverseImage (@IsOpenImmersion.{u}) (Over.forget S)).presheaf
      (Functor.whiskerLeft (prod.functor.obj Z).op (yoneda.map j)) := by
  let H := prod.functor.obj Z
  let α := Functor.whiskerLeft H.op (yoneda.map j)
  apply MorphismProperty.relative.of_exists
  intro T ξ
  let b : H.obj T ⟶ X := yonedaEquiv ξ
  have : UniversallyClosed (prod.snd : Z ⨯ T ⟶ T).left :=
    prod_snd_left_of_hom @UniversallyClosed Z T inferInstance
  obtain ⟨V, hV⟩ := exists_open_fiberwise_preimage_of_isPullback
    (prod.snd : Z ⨯ T ⟶ T).left b.left j.left.opensRange
  let V' : Over S := Over.mk (V.ι ≫ T.hom)
  let i : V' ⟶ T := Over.homMk V.ι rfl
  have : IsOpenImmersion i.left := inferInstanceAs (IsOpenImmersion V.ι)
  have : Mono i := (Over.forget S).mono_of_mono_map (f := i) inferInstance
  have : Mono j :=
    (Over.forget S).mono_of_mono_map (f := j) (inferInstanceAs (Mono j.left))
  have : Mono α := by
    have (W : (Over S)ᵒᵖ) : Mono (α.app W) :=
      inferInstanceAs (Mono ((yoneda.map j).app (H.op.obj W)))
    exact NatTrans.mono_of_mono_app α
  obtain ⟨δ, hδ⟩ := exists_isPullback_yoneda_of_lift_iff α i ξ (by
    intro W t
    have hξ : ξ.app (Opposite.op W) t = H.map t ≫ b :=
      (congrArg (fun τ => τ.app (Opposite.op W) t) (yonedaEquiv.symm_apply_apply ξ)).symm
    rw [hξ]
    change (∃ l : H.obj W ⟶ X', l ≫ j = H.map t ≫ b) ↔ _
    rw [over_exists_lift_iff_range_subset, over_exists_lift_iff_range_subset]
    have ht := hV t.left (H.map t).left (prod.snd : Z ⨯ W ⟶ W).left
      ((isPullback_prod_snd Z t).map (Over.forget S))
    change (Set.range ((H.map t).left ≫ b.left) ⊆ Set.range j.left) ↔
      Set.range t.left ⊆ Set.range V.ι
    rw [Scheme.Opens.range_ι]
    exact ht.symm)
  exact ⟨V', δ, i, hδ, inferInstanceAs (IsOpenImmersion V.ι)⟩


private lemma isOpenImmersion_finite_coproduct_inclusion
    {I : Type u} (X : I → Scheme.{u}) (E : Finset I) :
    IsOpenImmersion (Sigma.desc (fun i : E => Sigma.ι X i)) := by
  apply isOpenImmersion_sigmaDesc
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro x ⟨yi, hyi⟩ ⟨yj, hyj⟩
  have h := (sigmaι_eq_iff X i j yi yj).mp (hyi.trans hyj.symm)
  exact hij (Subtype.ext (congrArg Sigma.fst h))


private lemma exists_bounded_universal_tensor_hom
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] {ι : Type u} [Finite ι]
    (b : Module.Basis ι R B) :
    ∃ (Q : Type u) (_ : CommRing Q) (_ : Algebra R Q)
      (e : A →ₐ[R] Q ⊗[R] B),
      Cardinal.mk Q ≤ max (max (Cardinal.mk R) (Cardinal.mk (A × ι))) Cardinal.aleph0 ∧
      ∀ (C : Type u) [CommRing C] [Algebra R C],
        Function.Bijective (fun k : Q →ₐ[R] C ↦
          (Algebra.TensorProduct.map k (AlgHom.id R B)).comp e) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let P := MvPolynomial (A × ι) R
  let π : MvPolynomial A R →ₐ[R] A := MvPolynomial.aeval id
  have hπ : Function.Surjective π := fun a ↦ ⟨MvPolynomial.X a, MvPolynomial.aeval_X _ _⟩
  let ψ : MvPolynomial A R →ₐ[R] P ⊗[R] B :=
    MvPolynomial.aeval (fun a ↦ ∑ i, MvPolynomial.X (a, i) ⊗ₜ[R] b i)
  have hψ (a : A) (i : ι) :
      (b.baseChange P).repr (ψ (MvPolynomial.X a)) i = MvPolynomial.X (a, i) := by
    simp [ψ, Module.Basis.baseChange_repr_tmul, Module.Basis.repr_self, Finsupp.single_apply]
  have universal (C : Type u) [CommRing C] [Algebra R C] :
      Function.Bijective (fun k : P →ₐ[R] C ↦
        (Algebra.TensorProduct.map k (AlgHom.id R B)).comp ψ) := by
    constructor
    · intro k l h
      apply MvPolynomial.algHom_ext
      rintro ⟨a, i⟩
      have := congrArg (fun f : MvPolynomial A R →ₐ[R] C ⊗[R] B ↦
        (b.baseChange C).repr (f (MvPolynomial.X a)) i) h
      simpa only [AlgHom.comp_apply, tensor_repr_map, hψ] using this
    · intro h
      let k : P →ₐ[R] C := MvPolynomial.aeval
        (fun ai ↦ (b.baseChange C).repr (h (MvPolynomial.X ai.1)) ai.2)
      refine ⟨k, ?_⟩
      apply MvPolynomial.algHom_ext
      intro a
      apply (b.baseChange C).ext_elem
      intro i
      rw [AlgHom.comp_apply, tensor_repr_map, hψ]
      exact MvPolynomial.aeval_X _ _
  let J : Ideal P := Ideal.span
    { c | ∃ p : MvPolynomial A R, π p = 0 ∧ ∃ i, c = (b.baseChange P).repr (ψ p) i }
  have descent (C : Type u) [CommRing C] [Algebra R C] (k : P →ₐ[R] C) :
      J ≤ RingHom.ker k.toRingHom ↔
        RingHom.ker π.toRingHom ≤
          RingHom.ker ((Algebra.TensorProduct.map k (AlgHom.id R B)).comp ψ).toRingHom := by
    rw [Ideal.span_le]
    constructor
    · intro hk p hp
      apply (b.baseChange C).ext_elem
      intro i
      simp only [AlgHom.toRingHom_eq_coe, RingHom.mem_ker, AlgHom.coe_toRingHom] at hp ⊢
      rw [AlgHom.comp_apply, tensor_repr_map]
      simpa using hk ⟨p, hp, i, rfl⟩
    · rintro hk c ⟨p, hp, i, rfl⟩
      have h := congrArg (fun x ↦ (b.baseChange C).repr x i) (hk hp)
      simpa [tensor_repr_map] using h
  let Q := P ⧸ J
  let : CommRing Q := inferInstanceAs (CommRing (P ⧸ J))
  let : Algebra R Q := inferInstanceAs (Algebra R (P ⧸ J))
  let q : P →ₐ[R] Q := Ideal.Quotient.mkₐ R J
  have hq : J ≤ RingHom.ker q.toRingHom := fun _ hp => Ideal.Quotient.eq_zero_iff_mem.mpr hp
  let e : A →ₐ[R] Q ⊗[R] B :=
    π.liftOfSurjective hπ ((Algebra.TensorProduct.map q (AlgHom.id R B)).comp ψ)
      ((descent Q q).mp hq)
  have he : e.comp π = (Algebra.TensorProduct.map q (AlgHom.id R B)).comp ψ :=
    AlgHom.liftOfSurjective_comp ..
  refine ⟨Q, inferInstance, inferInstance, e,
    Cardinal.mk_quotient_le.trans MvPolynomial.cardinalMk_le_max, ?_⟩
  intro C _ _
  have base_change (k : Q →ₐ[R] C) :
      ((Algebra.TensorProduct.map k (AlgHom.id R B)).comp e).comp π =
        (Algebra.TensorProduct.map (k.comp q) (AlgHom.id R B)).comp ψ := by
    rw [AlgHom.comp_assoc, he, ← AlgHom.comp_assoc]
    congr 1
    exact (Algebra.TensorProduct.map_comp k q (AlgHom.id R B) (AlgHom.id R B)).symm
  constructor
  · intro k l h
    dsimp only at h
    have hkl : k.comp q = l.comp q :=
      (universal C).injective (by rw [← base_change, ← base_change, h])
    apply AlgHom.ext
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact DFunLike.congr_fun hkl p
  · intro h
    obtain ⟨k, hk⟩ := (universal C).surjective (h.comp π)
    dsimp only at hk
    have hkJ : J ≤ RingHom.ker k.toRingHom := (descent C k).mpr (by
      rw [hk]
      intro p hp
      change h (π p) = 0
      rw [show π p = 0 from hp, map_zero])
    let l : Q →ₐ[R] C := Ideal.Quotient.liftₐ J k hkJ
    refine ⟨l, ?_⟩
    have hl : l.comp q = k := Ideal.Quotient.liftₐ_comp J k hkJ
    have H := base_change l
    rw [hl, hk] at H
    apply AlgHom.ext
    intro a
    obtain ⟨p, rfl⟩ := hπ a
    exact DFunLike.congr_fun H p

private lemma exists_bounded_universal_tensor_hom_right
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] {ι : Type u} [Finite ι]
    (b : Module.Basis ι R B) :
    ∃ (Q : Type u) (_ : CommRing Q) (_ : Algebra R Q)
      (e : A →ₐ[R] B ⊗[R] Q),
      Cardinal.mk Q ≤ max (max (Cardinal.mk R) (Cardinal.mk (A × ι))) Cardinal.aleph0 ∧
      ∀ (C : Type u) [CommRing C] [Algebra R C],
        Function.Bijective (fun k : Q →ₐ[R] C ↦
          (Algebra.TensorProduct.map (AlgHom.id R B) k).comp e) := by
  obtain ⟨Q, _, _, e, hQ, he⟩ := exists_bounded_universal_tensor_hom R A B b
  refine ⟨Q, inferInstance, inferInstance,
    (Algebra.TensorProduct.comm R Q B).toAlgHom.comp e, hQ, ?_⟩
  intro C _ _
  let E : (A →ₐ[R] C ⊗[R] B) ≃ (A →ₐ[R] B ⊗[R] C) :=
    { toFun := fun h ↦ (Algebra.TensorProduct.comm R C B).toAlgHom.comp h
      invFun := fun h ↦ (Algebra.TensorProduct.comm R B C).toAlgHom.comp h
      left_inv := fun h ↦ by
        ext x; exact (Algebra.TensorProduct.comm R C B).symm_apply_apply (h x)
      right_inv := fun h ↦ by
        ext x; exact (Algebra.TensorProduct.comm R B C).symm_apply_apply (h x) }
  convert E.bijective.comp (he C) using 1
  funext k
  dsimp [E, Function.comp_def]
  rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc]
  congr 1
  ext <;> simp

open MonoidalCategory CartesianMonoidalCategory

section
variable (R : CommRingCat.{u}) {S : Scheme.{u}}
  (F : (CommAlgCat.{u} R)ᵒᵖ ⥤ Over S) [F.Full] [F.Faithful] [PreservesFiniteLimits F]

private lemma relativeHom_representable_of_bounded_algebra_universal
    (A B : CommAlgCat.{u} R) {ι : Type u} [Finite ι] (b : Module.Basis ι R B)
    (hFaff : ∀ C, IsAffine (F.obj (op C)).left)
    (hFsize : ∀ C, (F.obj (op C)).left.size = max Cardinal.aleph0 (Cardinal.mk C))
    (hFess : ∀ T : Over S, IsAffine T.left →
      ∃ C : CommAlgCat.{u} R, Nonempty (F.obj (op C) ≅ T)) :
    ∃ W : Over S, IsAffine W.left ∧
      W.left.size ≤ max (max (Cardinal.mk R) (Cardinal.mk (A × ι))) Cardinal.aleph0 ∧ Nonempty
      (((prod.functor.obj (F.obj (op B))).op ⋙ yoneda.obj (F.obj (op A))).RepresentableBy W) := by
  classical
  obtain ⟨Q, _, _, e, hQ, he⟩ := exists_bounded_universal_tensor_hom_right R A B b
  let Q' : CommAlgCat.{u} R := .of R Q
  let W := F.obj (op Q')
  let H := (prod.functor.obj (F.obj (op B))).op ⋙ yoneda.obj (F.obj (op A))
  let α : yoneda.obj W ⟶ H := yonedaEquiv.symm (specTensorHomEquiv R F A B Q' e)
  have hspec (C : CommAlgCat.{u} R) : Function.Bijective (α.app (op (F.obj (op C)))) := by
    have hb := (specTensorHomEquiv R F A B C).bijective.comp (he C)
    have hn : ((α.app (op (F.obj (op C)))) ∘ (algSpecHomEquiv R F Q' C)) =
        (specTensorHomEquiv R F A B C) ∘
          (fun k : Q →ₐ[R] C ↦ (Algebra.TensorProduct.map (AlgHom.id R B) k).comp e) := by
      funext k; exact (specTensorHomEquiv_natural R F A B Q' C e k).symm
    rw [← hn] at hb
    exact (Function.Bijective.of_comp_iff _ (algSpecHomEquiv R F Q' C).bijective).mp hb
  have : IsIso α := isIso_of_affine_components α
    ((isSheaf_iff_isSheaf_of_type _ _).mpr
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _))
    (relativeHom_isSheaf _ _) (by
      intro T hT
      obtain ⟨C, ⟨i⟩⟩ := hFess T hT
      have := (isIso_iff_bijective _).mpr (hspec C)
      exact (isIso_iff_bijective _).mp ((α.isIso_app_iff_of_iso i.op).mpr this))
  refine ⟨W, hFaff Q', ?_, ⟨Functor.representableByEquiv.symm (asIso α)⟩⟩
  rw [hFsize]
  exact max_le (le_max_right _ _) hQ
end


lemma relativeHom_representableBy_affine_size_le
    (S Z X : Scheme.{u}) (f : Z ⟶ S) (g : X ⟶ S)
    [IsAffine S] [IsAffine Z] [IsAffine X]
    (hfinite : letI := f.appTop.hom.toAlgebra
      Module.Finite Γ(S, ⊤) Γ(Z, ⊤))
    (hfree : letI := f.appTop.hom.toAlgebra
      Module.Free Γ(S, ⊤) Γ(Z, ⊤)) :
    ∃ W : Over S, IsAffine W.left ∧ W.left.size ≤ max S.size X.size ∧
      Nonempty
        (((Limits.prod.functor.obj (Over.mk f)).op ⋙ yoneda.obj (Over.mk g)).RepresentableBy W) :=
  by
    classical
    let R := Γ(S, ⊤)
    let : Algebra R Γ(Z, ⊤) := f.appTop.hom.toAlgebra
    let : Algebra R Γ(X, ⊤) := g.appTop.hom.toAlgebra
    let : Module.Finite R Γ(Z, ⊤) := hfinite
    let : Module.Free R Γ(Z, ⊤) := hfree
    let A : CommAlgCat.{u} R := .of R Γ(X, ⊤)
    let B : CommAlgCat.{u} R := .of R Γ(Z, ⊤)
    let F : (CommAlgCat.{u} R)ᵒᵖ ⥤ Over S :=
      algSpec R ⋙ Over.map S.isoSpec.inv
    have hFaff (C : CommAlgCat.{u} R) : IsAffine (F.obj (op C)).left := by
      change IsAffine (Spec (.of C)); infer_instance
    have hFess (T : Over S) (hT : IsAffine T.left) :
        ∃ C : CommAlgCat.{u} R, Nonempty (F.obj (op C) ≅ T) := by
      let T' := (Over.map S.isoSpec.hom).obj T
      obtain ⟨C, ⟨i⟩⟩ := (essImage_algSpec (R := R) (G := T')).mpr hT
      exact ⟨C.unop, ⟨(Over.map S.isoSpec.inv).mapIso i ≪≫
        (Over.mapIso S.isoSpec).unitIso.symm.app T⟩⟩
    obtain ⟨W, hW, hsize, ⟨h⟩⟩ := relativeHom_representable_of_bounded_algebra_universal R F A B
      (Module.Free.chooseBasis R Γ(Z, ⊤)) hFaff
      (fun C => Scheme.size_Spec (.of C)) hFess
    let eZ : F.obj (op B) ≅ Over.mk f :=
      Over.isoMk Z.isoSpec.symm (by exact (arrowIsoSpecΓOfIsAffine f).inv.w)
    let eX : F.obj (op A) ≅ Over.mk g :=
      Over.isoMk X.isoSpec.symm (by exact (arrowIsoSpecΓOfIsAffine g).inv.w)
    refine ⟨W, hW, ?_, ⟨h.ofIso ?_⟩⟩
    · have hR : Cardinal.mk R ≤ max S.size X.size :=
        (Scheme.mk_sections_le_size S ⟨⊤, isAffineOpen_top S⟩).trans (le_max_left _ _)
      have hA : Cardinal.mk A ≤ max S.size X.size :=
        (Scheme.mk_sections_le_size X ⟨⊤, isAffineOpen_top X⟩).trans (le_max_right _ _)
      have hℵ : Cardinal.aleph0 ≤ max S.size X.size :=
        S.aleph0_le_size.trans (le_max_left _ _)
      refine hsize.trans (max_le (max_le hR ?_) hℵ)
      simp only [Cardinal.mk_prod, Cardinal.lift_id]
      exact (Cardinal.mul_le_max _ _).trans
        (max_le (max_le hA (Cardinal.mk_le_aleph0.trans hℵ)) hℵ)
    · exact Functor.isoWhiskerRight (NatIso.op (prod.functor.mapIso eZ).symm)
        (yoneda.obj (F.obj (op A))) ≪≫
        Functor.isoWhiskerLeft (prod.functor.obj (Over.mk f)).op (yoneda.mapIso eX)




private lemma exists_affineOpen_of_isCompact_in_coproduct
    {I : Type u} (X : I → Scheme.{u}) [∀ i, IsAffine (X i)]
    (t : Set (∐ X : Scheme.{u})) (ht : IsCompact t) :
    ∃ U : (∐ X).Opens, IsAffineOpen U ∧ t ⊆ U := by
  classical
  obtain ⟨E, hE⟩ := ht.elim_finite_subcover
    (fun i => Set.range (Sigma.ι X i))
    (fun i => (Sigma.ι X i).isOpenEmbedding.isOpen_range) (by
      intro x hx
      obtain ⟨⟨i, y⟩, rfl⟩ := (sigmaMk X).surjective x
      exact Set.mem_iUnion.mpr ⟨i, y, (sigmaMk_mk X i y).symm⟩)
  let j := Sigma.desc (fun i : E => Sigma.ι X i)
  have : IsOpenImmersion j := isOpenImmersion_finite_coproduct_inclusion X E
  refine ⟨j.opensRange, isAffineOpen_opensRange j, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hE hx)
  obtain ⟨hi, y, hy⟩ := Set.mem_iUnion.mp hi
  refine ⟨Sigma.ι (fun i : E => X i) ⟨i, hi⟩ y, ?_⟩
  rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
  exact hy

private lemma relativeHom_isRepresentable_coproduct
    {I : Type u} (X : I → Scheme.{u}) [∀ i, IsAffine (X i)]
    {S Z : Scheme.{u}} (z : Z ⟶ S) (x : (∐ X) ⟶ S)
    [Stacks.Morphisms.IsFiniteLocallyFree z] :
    ((prod.functor.obj (Over.mk z)).op ⋙ yoneda.obj (Over.mk x)).IsRepresentable :=
  Stacks.Morphisms.homFromFiniteLocallyFree_isRepresentable z x
    (fun _ t ht _ => exists_affineOpen_of_isCompact_in_coproduct X t ht.isCompact)


private noncomputable def representedHomMap
    {C : Type v} [Category.{u} C] {F G : Cᵒᵖ ⥤ Type u} {V W : C}
    (rF : F.RepresentableBy V) (rG : G.RepresentableBy W) (α : F ⟶ G) : V ⟶ W :=
  yoneda.preimage (rF.toIso.hom ≫ α ≫ rG.toIso.inv)

private lemma representedHomMap_homEquiv
    {C : Type v} [Category.{u} C] {F G : Cᵒᵖ ⥤ Type u} {V W T : C}
    (rF : F.RepresentableBy V) (rG : G.RepresentableBy W) (α : F ⟶ G)
    (t : T ⟶ V) :
    rG.homEquiv (t ≫ representedHomMap rF rG α) = α.app (op T) (rF.homEquiv t) := by
  have h := congrArg (fun k : yoneda.obj V ⟶ yoneda.obj W => k.app (op T) t)
    (yoneda.map_preimage (rF.toIso.hom ≫ α ≫ rG.toIso.inv))
  change t ≫ representedHomMap rF rG α = rG.homEquiv.symm (α.app (op T) (rF.homEquiv t)) at h
  rw [h, Equiv.apply_symm_apply]

private lemma representedHomMap_property
    {C : Type v} [Category.{u} C] {F G : Cᵒᵖ ⥤ Type u} {V W : C}
    (rF : F.RepresentableBy V) (rG : G.RepresentableBy W) (α : F ⟶ G)
    (P : MorphismProperty C) [P.RespectsIso] (hα : P.presheaf α) :
    P (representedHomMap rF rG α) := by
  apply MorphismProperty.of_relative_map (F := yoneda) (P := P)
  rw [representedHomMap, yoneda.map_preimage]
  exact (P.presheaf.cancel_left_of_respectsIso _ _).mpr
    ((P.presheaf.cancel_right_of_respectsIso _ _).mpr hα)

private lemma relativeHom_size_le_of_affine_charts
    {S : Scheme.{u}} (Z X W : Over S)
    [UniversallyClosed Z.hom]
    (r : ((prod.functor.obj Z).op ⋙ yoneda.obj X).RepresentableBy W)
    (hcharts : ∀ U : X.left.affineOpens, ∃ V : Over S,
      V.left.size ≤ max S.size X.left.size ∧ Nonempty
        (((prod.functor.obj Z).op ⋙
          yoneda.obj (Over.mk (U.1.ι ≫ X.hom))).RepresentableBy V))
    (hfactor : ∀ (T : Over S), IsAffine T.left → ∀ b : Z ⨯ T ⟶ X,
      ∃ (U : X.left.affineOpens) (c : Z ⨯ T ⟶ Over.mk (U.1.ι ≫ X.hom)),
        c ≫ (Over.homMk U.1.ι rfl : Over.mk (U.1.ι ≫ X.hom) ⟶ X) = b) :
    W.left.size ≤ max S.size X.left.size := by
  classical
  choose V hsize rV using hcharts
  let j (U : X.left.affineOpens) : V U ⟶ W := representedHomMap (rV U).some r
    (Functor.whiskerLeft (prod.functor.obj Z).op
      (yoneda.map (Over.homMk U.1.ι rfl : Over.mk (U.1.ι ≫ X.hom) ⟶ X)))
  have hj (U : X.left.affineOpens) : IsOpenImmersion (j U).left :=
    by
    let jU : Over.mk (U.1.ι ≫ X.hom) ⟶ X := Over.homMk U.1.ι rfl
    have : IsOpenImmersion jU.left := inferInstanceAs (IsOpenImmersion U.1.ι)
    exact representedHomMap_property (rV U).some r _
      (MorphismProperty.inverseImage (@IsOpenImmersion.{u}) (Over.forget S))
      (presheaf_isOpenImmersion_relativeHomPostcomp Z
        (Over.mk (U.1.ι ≫ X.hom)) X (Over.homMk U.1.ι rfl))
  have hcov : ⨆ U, (j U).left.opensRange = ⊤ := by
    apply top_unique
    intro w hw
    obtain ⟨A, ha, hwA, -⟩ := exists_isAffineOpen_mem_and_subset (X := W.left)
      (x := w) (U := ⊤) (by trivial)
    let T : Over S := Over.mk (A.ι ≫ W.hom)
    let t : T ⟶ W := Over.homMk A.ι rfl
    obtain ⟨U, c, hc⟩ := hfactor T ha (r.homEquiv t)
    let l : T ⟶ V U := (rV U).some.homEquiv.symm c
    have hl : l ≫ j U = t := by
      apply r.homEquiv.injective
      rw [representedHomMap_homEquiv]
      change (rV U).some.homEquiv l ≫
        (Over.homMk U.1.ι rfl : Over.mk (U.1.ι ≫ X.hom) ⟶ X) = r.homEquiv t
      rw [show (rV U).some.homEquiv l = c from Equiv.apply_symm_apply _ _]
      exact hc
    have hw' : w ∈ Set.range (j U).left :=
      ⟨l.left ⟨w, hwA⟩, congrArg (fun f : T ⟶ W => f.left ⟨w, hwA⟩) hl⟩
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨U, hw'⟩
  have : Nonempty X.left.affineOpens := ⟨⟨⊥, isAffineOpen_bot X.left⟩⟩
  refine (Scheme.size_le_of_iSup_eq_top (fun U => (j U).left.opensRange) hcov).trans
    (max_le ((Scheme.mk_affineOpens_le_size X.left).trans (le_max_right _ _))
      (ciSup_le' fun U => ?_))
  rw [← Scheme.size_congr (j U).left.isoOpensRange]
  exact hsize U

private lemma relativeHom_exists_factor_affineOpen_coproduct
    {S : Scheme.{u}} (Z : Over S) [QuasiCompact Z.hom]
    {I : Type u} (X : I → Scheme.{u}) [∀ i, IsAffine (X i)]
    (x : (∐ X) ⟶ S) (T : Over S) [IsAffine T.left]
    (b : Z ⨯ T ⟶ Over.mk x) :
    ∃ (U : (∐ X).affineOpens)
      (c : Z ⨯ T ⟶ Over.mk (U.1.ι ≫ x)),
      c ≫ (Over.homMk U.1.ι rfl : Over.mk (U.1.ι ≫ x) ⟶ Over.mk x) = b := by
  have : QuasiCompact (prod.snd : Z ⨯ T ⟶ T).left :=
    prod_snd_left_of_hom @QuasiCompact Z T inferInstance
  have : CompactSpace (Z ⨯ T).left :=
    QuasiCompact.compactSpace_of_compactSpace (prod.snd : Z ⨯ T ⟶ T).left
  obtain ⟨U, hU, hb⟩ := exists_affineOpen_of_isCompact_in_coproduct X
    (Set.range b.left) (isCompact_range b.left.continuous)
  have hj : IsOpenImmersion
      (Over.homMk U.ι rfl : Over.mk (U.ι ≫ x) ⟶ Over.mk x).left :=
    inferInstanceAs (IsOpenImmersion U.ι)
  obtain ⟨c, hc⟩ := (over_exists_lift_iff_range_subset
    (Over.homMk U.ι rfl : Over.mk (U.ι ≫ x) ⟶ Over.mk x) b).mpr (by
      change Set.range b.left ⊆ Set.range U.ι
      rwa [Scheme.Opens.range_ι])
  exact ⟨⟨U, hU⟩, c, hc⟩

open TopologicalSpace

private noncomputable def finiteFreeSectionsIso
    {C : Type v} [Category C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (I : Type u) [Finite I] (U : C) :
    (SheafOfModules.free.{u} (R := R) I).val.obj (op U) ≅
      ModuleCat.of (R.obj.obj (op U)) (I → R.obj.obj (op U)) := by
  classical
  let F := SheafOfModules.evaluation.{u} R (op U)
  have : HasBiproduct (fun _ : I => SheafOfModules.unit.{u} R) :=
    HasBiproduct.of_hasProduct _
  exact F.mapIso (biproductIso (fun _ : I => SheafOfModules.unit.{u} R)).symm ≪≫
    PreservesProduct.iso F _ ≪≫ ModuleCat.piIsoPi _

private lemma exists_affine_free_sections
    {S : Scheme.{u}} (M : S.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M]
    (s : S) : ∃ U : S.affineOpens, s ∈ U.1 ∧
      Module.Free Γ(S, U.1) Γ(M, U.1) ∧
      Module.Finite Γ(S, U.1) Γ(M, U.1) := by
  classical
  have hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M := inferInstance
  obtain ⟨q, hq, hqfin⟩ := hM.exists_isFiniteLocallyFreeData
  have hcover := q.coversTop (⊤ : S.Opens)
  obtain ⟨V, f, hf, hsV⟩ := (Opens.mem_grothendieckTopology (T := S)).mp hcover s (by simp)
  obtain ⟨i, ⟨g⟩⟩ := (Sieve.mem_ofObjects_iff q.X f).mp hf
  obtain ⟨U, hU, hsU, hUi⟩ := exists_isAffineOpen_mem_and_subset (g.le hsV)
  let T : Over (q.X i) := Over.mk (homOfLE hUi)
  let F := SheafOfModules.evaluation (S.ringCatSheaf.over (q.X i)) (op T)
  have : IsIso (q.generators i).π := hq.isIso i
  have : (q.generators i).IsFiniteType := hqfin.isFiniteType i
  have : Finite (q.generators i).I := inferInstance
  let e : M.val.obj (op U) ≅ ModuleCat.of Γ(S, U)
      ((q.generators i).I → Γ(S, U)) := (F.mapIso (asIso (q.generators i).π)).symm ≪≫
    finiteFreeSectionsIso (S.ringCatSheaf.over (q.X i)) (q.generators i).I T
  exact ⟨⟨U, hU⟩, hsU, Module.Free.of_equiv e.symm.toLinearEquiv,
    Module.Finite.equiv e.symm.toLinearEquiv⟩

private lemma finiteFree_comp_ringEquiv
    {R A D : Type u} [CommRing R] [CommRing A] [CommRing D]
    (f : R →+* A) (e : A ≃+* D)
    (hfree : letI := f.toAlgebra; Module.Free R A)
    (hfinite : letI := f.toAlgebra; Module.Finite R A) :
    letI := (e.toRingHom.comp f).toAlgebra
    Module.Free R D ∧ Module.Finite R D := by
  let := f.toAlgebra
  let := (e.toRingHom.comp f).toAlgebra
  let a : A ≃ₐ[R] D := { __ := e, commutes' := fun r => rfl }
  exact ⟨Module.Free.of_equiv a.toLinearEquiv, Module.Finite.equiv a.toLinearEquiv⟩

private lemma exists_affine_finiteFree_restrict
    {Z S : Scheme.{u}} (z : Z ⟶ S) [Stacks.Morphisms.IsFiniteLocallyFree z]
    (s : S) : ∃ U : S.affineOpens, s ∈ U.1 ∧
      (letI := (z ∣_ U.1).appTop.hom.toAlgebra
       Module.Free Γ(U.1.toScheme, ⊤) Γ((z ⁻¹ᵁ U.1).toScheme, ⊤) ∧
       Module.Finite Γ(U.1.toScheme, ⊤) Γ((z ⁻¹ᵁ U.1).toScheme, ⊤)) := by
  obtain ⟨U, hs, hfree, hfinite⟩ := exists_affine_free_sections
    (Stacks.Morphisms.pushforwardStructureSheaf z) s
  refine ⟨U, hs, ?_⟩
  rw [morphismRestrict_appTop]
  apply finiteFree_comp_ringEquiv _
    (Iso.commRingCatIsoToRingEquiv (asIso (Z.presheaf.map
      (eqToHom (image_morphismRestrict_preimage z U.1 ⊤)).op)))
  · change let := (z.app (U.1.ι ''ᵁ ⊤)).hom.toAlgebra
           Module.Free Γ(S, U.1.ι ''ᵁ ⊤) Γ(Z, z ⁻¹ᵁ (U.1.ι ''ᵁ ⊤))
    rw [Scheme.Opens.ι_image_top]
    exact hfree
  · change let := (z.app (U.1.ι ''ᵁ ⊤)).hom.toAlgebra
           Module.Finite Γ(S, U.1.ι ''ᵁ ⊤) Γ(Z, z ⁻¹ᵁ (U.1.ι ''ᵁ ⊤))
    rw [Scheme.Opens.ι_image_top]
    exact hfinite


private noncomputable def overMapProdPullbackIso
    {C : Type v} [Category.{u} C] [HasPullbacks C]
    {S U : C} [HasBinaryProducts (Over S)] [HasBinaryProducts (Over U)]
    (q : U ⟶ S) (Z : Over S) (T : Over U) :
    (Over.map q).obj ((Over.pullback q).obj Z ⨯ T) ≅
      Z ⨯ (Over.map q).obj T := by
  let e := Over.prodLeftIsoPullback ((Over.pullback q).obj Z) T ≪≫
    pullbackLeftPullbackSndIso Z.hom q T.hom ≪≫
    (Over.prodLeftIsoPullback Z ((Over.map q).obj T)).symm
  refine Over.isoMk e ?_
  have h := Over.w (prod.snd : Z ⨯ (Over.map q).obj T ⟶ (Over.map q).obj T)
  rw [← h]
  dsimp [e]
  simp only [Over.map_obj_hom, Category.assoc, Over.prodLeftIsoPullback_inv_snd_assoc,
    pullbackLeftPullbackSndIso_hom_snd_assoc]
  exact (Over.prodLeftIsoPullback_hom_snd_assoc ((Over.pullback q).obj Z) T
    (T.hom ≫ q)).trans (by rw [← Category.assoc, Over.w])

private lemma overMapProdPullbackIso_hom_fst
    {C : Type v} [Category.{u} C] [HasPullbacks C]
    {S U : C} [HasBinaryProducts (Over S)] [HasBinaryProducts (Over U)]
    (q : U ⟶ S) (Z : Over S) (T : Over U) :
    (overMapProdPullbackIso q Z T).hom ≫ prod.fst =
      (Over.map q).map prod.fst ≫ (Over.mapPullbackAdj q).counit.app Z := by
  ext
  simpa [overMapProdPullbackIso, Category.assoc] using
    Over.prodLeftIsoPullback_hom_fst_assoc ((Over.pullback q).obj Z) T (pullback.fst Z.hom q)

private lemma overMapProdPullbackIso_hom_snd
    {C : Type v} [Category.{u} C] [HasPullbacks C]
    {S U : C} [HasBinaryProducts (Over S)] [HasBinaryProducts (Over U)]
    (q : U ⟶ S) (Z : Over S) (T : Over U) :
    (overMapProdPullbackIso q Z T).hom ≫ prod.snd =
      (Over.map q).map prod.snd := by
  ext
  simpa [overMapProdPullbackIso, Category.assoc] using
    Over.prodLeftIsoPullback_hom_snd ((Over.pullback q).obj Z) T

private lemma overMapProdPullbackIso_natural
    {C : Type v} [Category.{u} C] [HasPullbacks C]
    {S U : C} [HasBinaryProducts (Over S)] [HasBinaryProducts (Over U)]
    (q : U ⟶ S) (Z : Over S) {T T' : Over U} (f : T ⟶ T') :
    (Over.map q).map (prod.map (𝟙 _) f) ≫ (overMapProdPullbackIso q Z T').hom =
      (overMapProdPullbackIso q Z T).hom ≫ prod.map (𝟙 _) ((Over.map q).map f) := by
  apply prod.hom_ext
  · simp only [Category.assoc, overMapProdPullbackIso_hom_fst, prod.map_fst,
      Category.comp_id]
    rw [← Category.assoc, ← Functor.map_comp, prod.map_fst, Category.comp_id]
  · simp only [Category.assoc, overMapProdPullbackIso_hom_snd, prod.map_snd]
    rw [← Functor.map_comp, prod.map_snd, Functor.map_comp,
      ← Category.assoc, overMapProdPullbackIso_hom_snd]

attribute [local implicit_reducible] CategoryTheory.Limits.prod.functor in
private noncomputable def relativeHomRepresentableBy_baseChange
    {C : Type v} [Category.{u} C] [HasPullbacks C]
    {S U : C} [HasBinaryProducts (Over S)] [HasBinaryProducts (Over U)]
    (q : U ⟶ S) (Z X W : Over S)
    (r : ((prod.functor.obj Z).op ⋙ yoneda.obj X).RepresentableBy W) :
    ((prod.functor.obj ((Over.pullback q).obj Z)).op ⋙
      yoneda.obj ((Over.pullback q).obj X)).RepresentableBy ((Over.pullback q).obj W) where
  homEquiv {T} := ((Over.mapPullbackAdj q).homEquiv T W).symm.trans
    (r.homEquiv.trans ((overMapProdPullbackIso q Z T).symm.homFromEquiv.trans
      ((Over.mapPullbackAdj q).homEquiv _ X)))
  homEquiv_comp {T T'} f g := by
    dsimp only [Equiv.trans_apply]
    rw [Adjunction.homEquiv_naturality_left_symm, r.homEquiv_comp]
    change (Over.mapPullbackAdj q).homEquiv _ X
      ((overMapProdPullbackIso q Z T).hom ≫
        prod.map (𝟙 Z) ((Over.map q).map f) ≫ _) = _
    rw [← Category.assoc, ← overMapProdPullbackIso_natural, Category.assoc,
      Adjunction.homEquiv_naturality_left]
    rfl

private noncomputable def relativeHomRepresentableBy_iso
    {C : Type v} [Category.{u} C] [HasBinaryProducts C]
    {Z Z' X X' W W' : C} (eZ : Z' ≅ Z) (eX : X ≅ X') (eW : W' ≅ W)
    (r : ((prod.functor.obj Z).op ⋙ yoneda.obj X).RepresentableBy W) :
    ((prod.functor.obj Z').op ⋙ yoneda.obj X').RepresentableBy W' :=
  (r.ofIso (Functor.isoWhiskerRight (NatIso.op (prod.functor.mapIso eZ)) (yoneda.obj X) ≪≫
    Functor.isoWhiskerLeft (prod.functor.obj Z').op (yoneda.mapIso eX))).ofIsoObj eW
private noncomputable def overRestrictIsoPullback {S : Scheme.{u}}
    (Z : Over S) (U : S.Opens) :
    Over.mk (Z.hom ∣_ U) ≅ (Over.pullback U.ι).obj Z :=
  Over.isoMk (isPullback_morphismRestrict Z.hom U).flip.isoPullback
    (isPullback_morphismRestrict Z.hom U).flip.isoPullback_hom_snd

private noncomputable def relativeHomRepresentableBy_restrictOpen {S : Scheme.{u}}
    (Z X W : Over S) (U : S.Opens)
    (r : ((prod.functor.obj Z).op ⋙ yoneda.obj X).RepresentableBy W) :
    ((prod.functor.obj (Over.mk (Z.hom ∣_ U))).op ⋙
      yoneda.obj (Over.mk (X.hom ∣_ U))).RepresentableBy (Over.mk (W.hom ∣_ U)) :=
  relativeHomRepresentableBy_iso (overRestrictIsoPullback Z U)
    (overRestrictIsoPullback X U).symm (overRestrictIsoPullback W U)
    (relativeHomRepresentableBy_baseChange U.ι Z X W r)


private lemma relativeHom_size_le_of_isAffineHom {S : Scheme.{u}}
    (Z X W : Over S) [Stacks.Morphisms.IsFiniteLocallyFree Z.hom] [IsAffineHom X.hom]
    (r : ((prod.functor.obj Z).op ⋙ yoneda.obj X).RepresentableBy W) :
    W.left.size ≤ max S.size X.left.size := by
  classical
  let P (U : S.affineOpens) : Prop :=
    let := (Z.hom ∣_ U.1).appTop.hom.toAlgebra
    Module.Free Γ(U.1.toScheme, ⊤) Γ((Z.hom ⁻¹ᵁ U.1).toScheme, ⊤) ∧
    Module.Finite Γ(U.1.toScheme, ⊤) Γ((Z.hom ⁻¹ᵁ U.1).toScheme, ⊤)
  let V (U : S.affineOpens) : W.left.Opens := if P U then W.hom ⁻¹ᵁ U.1 else ⊥
  have hcover : ⨆ U, V U = ⊤ := by
    apply top_unique
    intro w _
    obtain ⟨U, hw, hU⟩ := exists_affine_finiteFree_restrict Z.hom (W.hom w)
    have hUP : P U := hU
    refine Opens.mem_iSup.mpr ⟨U, ?_⟩
    rw [show V U = W.hom ⁻¹ᵁ U.1 by simp only [V, ite_eq_left hUP]]
    exact hw
  have : Nonempty S.affineOpens := ⟨⟨⊥, isAffineOpen_bot S⟩⟩
  refine (Scheme.size_le_of_iSup_eq_top V hcover).trans
    (max_le ((Scheme.mk_affineOpens_le_size S).trans (le_max_left _ _))
      (ciSup_le' fun U => ?_))
  by_cases hU : P U
  · dsimp [V]
    rw [ite_eq_left hU]
    have : IsAffine U.1.toScheme := U.2
    have : IsAffine (Z.hom ⁻¹ᵁ U.1).toScheme :=
      IsAffineHom.isAffine_preimage (f := Z.hom) U.1 U.2
    have : IsAffine (X.hom ⁻¹ᵁ U.1).toScheme :=
      IsAffineHom.isAffine_preimage (f := X.hom) U.1 U.2
    obtain ⟨A, hA, hsize, ⟨rA⟩⟩ := relativeHom_representableBy_affine_size_le
      U.1.toScheme (Z.hom ⁻¹ᵁ U.1).toScheme (X.hom ⁻¹ᵁ U.1).toScheme
      (Z.hom ∣_ U.1) (X.hom ∣_ U.1) hU.2 hU.1
    let e := (relativeHomRepresentableBy_restrictOpen Z X W U.1 r).uniqueUpToIso rA
    exact (Scheme.size_congr ((Over.forget U.1.toScheme).mapIso e)).le.trans
      (hsize.trans (max_le_max (Scheme.size_coe_opens_le S U.1)
      (Scheme.size_coe_opens_le X.left (X.hom ⁻¹ᵁ U.1))))
  · dsimp [V]
    rw [ite_eq_right hU]
    have : IsEmpty (⊥ : W.left.Opens).toScheme := ⟨fun x => x.2.elim⟩
    exact (size_le_aleph0_of_isEmpty _ inferInstance).trans ((Scheme.aleph0_le_size S).trans
      (le_max_left _ _))

lemma relativeHom_representableBy_coproduct_size_le
    {I : Type u} (X : I → Scheme.{u}) [∀ i, IsAffine (X i)]
    {S Z : Scheme.{u}} [S.IsSeparated]
    (z : Z ⟶ S) (x : (∐ X) ⟶ S) [Stacks.Morphisms.IsFiniteLocallyFree z] :
    ∃ W : Over S, W.left.size ≤ max S.size (∐ X).size ∧ Nonempty
      (((prod.functor.obj (Over.mk z)).op ⋙ yoneda.obj (Over.mk x)).RepresentableBy W) := by
  have : IsFinite z :=
    ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      z).mp inferInstance).1
  have : UniversallyClosed (Over.mk z).hom := inferInstanceAs (UniversallyClosed z)
  have : QuasiCompact (Over.mk z).hom := inferInstanceAs (QuasiCompact z)
  let H := (prod.functor.obj (Over.mk z)).op ⋙ yoneda.obj (Over.mk x)
  have : H.IsRepresentable := relativeHom_isRepresentable_coproduct X z x
  refine ⟨H.reprX, ?_, ⟨H.representableBy⟩⟩
  apply relativeHom_size_le_of_affine_charts (Over.mk z) (Over.mk x) H.reprX
    H.representableBy
  · intro U
    have : IsAffine U.1.toScheme := U.2
    let xU := U.1.ι ≫ x
    have : IsAffineHom (xU ≫ terminal.from S) := inferInstance
    have : IsAffineHom xU := IsAffineHom.of_comp xU (terminal.from S)
    let HU := (prod.functor.obj (Over.mk z)).op ⋙ yoneda.obj (Over.mk xU)
    have : HU.IsRepresentable := Stacks.Morphisms.homFromFiniteLocallyFree_isRepresentable z xU
      (fun _ t _ _ => ⟨⊤, isAffineOpen_top _, Set.subset_univ t⟩)
    have : IsAffineHom (Over.mk xU).hom := inferInstanceAs (IsAffineHom xU)
    have : Stacks.Morphisms.IsFiniteLocallyFree (Over.mk z).hom := inferInstanceAs
      (Stacks.Morphisms.IsFiniteLocallyFree z)
    exact ⟨HU.reprX, (relativeHom_size_le_of_isAffineHom (Over.mk z) (Over.mk xU)
      HU.reprX HU.representableBy).trans
        (max_le_max le_rfl (Scheme.size_coe_opens_le _ _)), ⟨HU.representableBy⟩⟩
  · intro T hT b
    exact relativeHom_exists_factor_affineOpen_coproduct (Over.mk z) X x T b

end AlgebraicGeometry.RelativeHomAffineTarget

end
