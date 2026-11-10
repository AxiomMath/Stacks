module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.StandardAffineDescentReduction
public import StacksFrontier.CategoryTheory.Sites.DisjointCoverSections
public import Mathlib.RingTheory.TensorProduct.Pi

/-!
# The affine-section functor at the product algebra of a standard affine covering

`Stacks.Adequate.standardAffineDescent_of_productAdequacy` reduced
`Stacks.Adequate.StandardAffineDescent`, the one hypothesis of [Stacks, Tag 06VI] that the
library did not supply, to the single statement
`Stacks.Adequate.StandardAffineProductAdequacy`: adequacy of the affine-section functor of `F`
at the product `A' = A'₁ × ⋯ × A'ₘ` of a finite standard affine `τ`-covering. This module
proves that statement, and hence `Stacks.Adequate.StandardAffineDescent` itself.

## Main results

* `Stacks.Adequate.standardAffineProductAdequacy` —
  **`Stacks.Adequate.StandardAffineProductAdequacy` holds.**
* `Stacks.Adequate.standardAffineDescent` — **`Stacks.Adequate.StandardAffineDescent` holds**,
  with no hypothesis, by feeding the previous result to
  `Stacks.Adequate.standardAffineDescent_of_productAdequacy`.

## Implementation notes

**The whole content is one identification.** Adequacy of each `F_{F, A'ⱼ}` is given;
`AdequateFunctor.isAdequate_pushforwardOn` — [Stacks, Tag 06VA] on the site's domain of
algebras — makes `C ↦ F_{F, A'ⱼ}(C ⊗_{A'} A'ⱼ)` adequate on the `A'`-algebras of the site, and
`Stacks.Adequate.affineAdequateFiniteProducts` makes a finite product of adequate functors
adequate. What remains is to exhibit `F_{F, A'}` as that product, which is the Zariski sheaf
condition for the decomposition `Spec A' = ⨆ⱼ Spec A'ⱼ` together with the ring-level
decomposition `C ≅ ∏ⱼ (C ⊗_{A'} A'ⱼ)` of an algebra over a product ring.

**The legs of the product cone are the Čech augmentations.** The degree-one Čech term
`AdequateFunctor.cechOnceOn` of `F_{F, A'}` along the projection `A' ⟶ A'ⱼ` is, by
`AdequateFunctor.cechOnceOn_eq_pushforwardOn`, the pushforward of the restriction of
`F_{F, A'}` to the `A'ⱼ`-algebras of the site, which
`Stacks.Adequate.affineSectionRestriction` identifies with `F_{F, A'ⱼ}`; so the Čech term is
adequate, and the augmentation `AdequateFunctor.cechAugmentationOn` is a natural map from
`F_{F, A'}` to it. No cone has to be built by hand.

**The ring-level decomposition.** `AdequateFunctor.bijective_pi_cechUnit` says that for a base
ring `A' = ∏ⱼ A'ⱼ` the canonical maps `C ⟶ C ⊗_{A'} A'ⱼ` exhibit `C` as the product of its base
changes. The base change of `AdequateFunctor.cechBaseChange` is a pushout of commutative rings
rather than a tensor product, so `Algebra.IsPushout.equiv` identifies the two — this is
`AdequateFunctor.exists_ringEquiv_cechBaseChange` — and then
`Algebra.TensorProduct.piRight` together with `Algebra.TensorProduct.rid` gives the
decomposition. It is stated at an abstract `ε : A' ≃ₐ[A'] ∀ j, A'ⱼ` rather than using that the
two algebra structures on `∏ⱼ A'ⱼ` are definitionally equal.

**The sheaf condition is applied at a pairwise disjoint family, not at a general covering.**
`CategoryTheory.Presieve.IsSheaf.existsUnique_section_of_disjoint_arrows` glues sections over a
covering family of monomorphisms whose pairwise overlaps are covered by the empty sieve, with no
compatibility condition at all. The three inputs are supplied from the product ring directly,
with no coproduct of schemes formed: `Spec` of the `j`-th projection of a product ring is an
open immersion, so it is a `τ`-covering morphism for every one of the five topologies by
`Stacks.Adequate.coveringMorphismProperty_of_isOpenImmersion` and a monomorphism; the
projections are jointly surjective by `AlgebraicGeometry.iUnion_range_specMap_evalRingHom`; and
two distinct projections have no common source by
`AlgebraicGeometry.isEmpty_of_commSq_specMap_evalRingHom`, both read off
`PrimeSpectrum.sigmaToPi_bijective`. An empty object of the site is covered by the empty family,
whose generated sieve is `⊥`.

**From a pointwise bijection to a limit.** `Stacks.Adequate.isLimitOfBijectiveDiscreteCone`
turns a cone of modules over a discrete diagram into a limit cone as soon as the map from its
apex to the product of its legs is bijective, and
`CategoryTheory.PresheafOfModules.evaluationJointlyReflectsLimits` lifts that to the
module-valued functors.

## References

* [Stacks Project, Tag 06VI](https://stacks.math.columbia.edu/tag/06VI)
* [Stacks Project, Tag 06VB](https://stacks.math.columbia.edu/tag/06VB)
* [Stacks Project, Tag 06VA](https://stacks.math.columbia.edu/tag/06VA)
* [Stacks Project, Tag 06VH](https://stacks.math.columbia.edu/tag/06VH)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe v u m

/-! ### A product cone of modules from a bijection -/

namespace Stacks.Adequate

/-- **A cone over a discrete diagram of modules is a limit as soon as the map from its apex to
the product of its legs is bijective.** The inverse of that map is linear, so it provides the
lift, and the legs determine it. -/
public noncomputable def isLimitOfBijectiveDiscreteCone {R : Type u} [Ring R] {ι : Type*}
    {K : Discrete ι ⥤ ModuleCat.{v} R} (c : Cone K)
    (h : Function.Bijective fun x : c.pt ↦ fun j ↦ (c.π.app ⟨j⟩).hom x) : IsLimit c := by
  let φ : c.pt →ₗ[R] (∀ j, K.obj ⟨j⟩) := LinearMap.pi fun j ↦ (c.π.app ⟨j⟩).hom
  have hb : Function.Bijective φ := h
  let e : c.pt ≃ₗ[R] (∀ j, K.obj ⟨j⟩) := LinearEquiv.ofBijective φ hb
  refine { lift := fun s ↦ ModuleCat.ofHom (e.symm.toLinearMap.comp
      (LinearMap.pi fun j ↦ (s.π.app ⟨j⟩).hom)), fac := ?_, uniq := ?_ }
  · rintro s ⟨j⟩
    ext y
    exact congrFun (e.apply_symm_apply fun k ↦ (s.π.app ⟨k⟩).hom y) j
  · intro s m hm
    ext y
    have h₁ : ∀ k, φ ((ConcreteCategory.hom m) y) k = (s.π.app ⟨k⟩).hom y := fun k ↦ by
      rw [← hm ⟨k⟩]
      rfl
    have h₂ : ∀ k, φ ((ConcreteCategory.hom (ModuleCat.ofHom (e.symm.toLinearMap.comp
        (LinearMap.pi fun j ↦ (s.π.app ⟨j⟩).hom)))) y) k = (s.π.app ⟨k⟩).hom y := fun k ↦
      congrFun (e.apply_symm_apply fun l ↦ (s.π.app ⟨l⟩).hom y) k
    exact hb.injective (funext fun k ↦ (h₁ k).trans (h₂ k).symm)

end Stacks.Adequate

/-! ### The spectrum of a finite product of rings -/

namespace AlgebraicGeometry

/-- **The spectra of the factors of a finite product of rings cover the spectrum of the
product.** This is surjectivity of `PrimeSpectrum.sigmaToPi`. -/
public theorem iUnion_range_specMap_evalRingHom {ι : Type} [Finite ι] (R : ι → Type u)
    [∀ i, CommRing (R i)] :
    (⋃ i, Set.range (Spec.map (CommRingCat.ofHom (Pi.evalRingHom R i)))) = Set.univ := by
  refine Set.eq_univ_of_forall fun x ↦ ?_
  obtain ⟨⟨i, p⟩, hp⟩ := (PrimeSpectrum.sigmaToPi_bijective R).surjective x
  exact Set.mem_iUnion.mpr ⟨i, p, hp⟩

/-- **A scheme mapping compatibly into two distinct factors of a finite product of rings is
empty**: distinct factors of a product ring have disjoint spectra inside the spectrum of the
product. This is injectivity of `PrimeSpectrum.sigmaToPi`. -/
public theorem isEmpty_of_commSq_specMap_evalRingHom {ι : Type} (R : ι → Type u)
    [∀ i, CommRing (R i)] {i j : ι} (hij : i ≠ j) {Z : Scheme.{u}}
    {a : Z ⟶ Spec (CommRingCat.of (R i))} {b : Z ⟶ Spec (CommRingCat.of (R j))}
    (h : a ≫ Spec.map (CommRingCat.ofHom (Pi.evalRingHom R i)) =
      b ≫ Spec.map (CommRingCat.ofHom (Pi.evalRingHom R j))) :
    IsEmpty Z := by
  refine ⟨fun z ↦ hij ?_⟩
  have hz : PrimeSpectrum.sigmaToPi R ⟨i, a z⟩ = PrimeSpectrum.sigmaToPi R ⟨j, b z⟩ :=
    congrArg (fun k : Z ⟶ Spec (CommRingCat.of (∀ i, R i)) ↦ k z) h
  exact congrArg Sigma.fst (PrimeSpectrum.sigmaToPi_injective R hz)

end AlgebraicGeometry

/-! ### Algebras over a product ring -/

namespace AdequateFunctor

/-- **The base change of an algebra along `A ⟶ A'` is its tensor product with `A'`**,
compatibly with the canonical map from the algebra. `AdequateFunctor.cechBaseChange` is built
from a pushout of commutative rings, and `Algebra.IsPushout.equiv` identifies that pushout with
the tensor product. -/
public theorem exists_ringEquiv_cechBaseChange {A A' : Type u} [CommRing A] [CommRing A']
    [Algebra A A'] (B : CommAlgCat.{u} A) (f : A →+* A') (hf : algebraMap A A' = f) :
    ∃ e : (↥B ⊗[A] A') ≃+* ↥((cechBaseChange f).obj B),
      ∀ b : ↥B, e (b ⊗ₜ (1 : A')) = ((cechUnit f).app B).hom b := by
  subst hf
  set f := algebraMap A A'
  set B' : Type u := ↥((baseChangeFunctor f).obj B)
  let : Algebra ↥B B' := (((baseChangeRingHom f).app (op (op B))).hom).toAlgebra
  let : Algebra A B' := ((algebraMap A' B').comp f).toAlgebra
  let : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq' rfl
  set U := (commAlgCatEquivUnder (CommRingCat.of A)).functor.obj B
  have hcomm : U.hom ≫ pushout.inl U.hom (CommRingCat.ofHom f) =
      CommRingCat.ofHom f ≫ pushout.inr U.hom (CommRingCat.ofHom f) := pushout.condition
  have hcomp : algebraMap A B' = (algebraMap ↥B B').comp (algebraMap A ↥B) := by
    ext a
    change (pushout.inr U.hom (CommRingCat.ofHom f)).hom (f a) =
      (pushout.inl U.hom (CommRingCat.ofHom f)).hom (U.hom.hom a)
    exact congrArg (fun k : CommRingCat.Hom _ _ => k.hom a) hcomm.symm
  let : IsScalarTower A ↥B B' := IsScalarTower.of_algebraMap_eq' hcomp
  have hbase : Algebra.IsPushout A ↥B A' B' :=
    (CommRingCat.isPushout_iff_isPushout (R := A) (R' := ↥B) (S := A') (S' := B')).mp
      ⟨⟨hcomm⟩, ⟨pushoutIsPushout U.hom (CommRingCat.ofHom f)⟩⟩
  refine ⟨(Algebra.IsPushout.equiv A ↥B A' B').toRingEquiv, fun b ↦ ?_⟩
  change Algebra.IsPushout.equiv A ↥B A' B' (b ⊗ₜ (1 : A')) = _
  rw [Algebra.IsPushout.equiv_tmul, map_one, mul_one]
  rfl

/-- **An algebra over a ring presented as a finite product is the product of its base changes
to the factors**, in the form the tensor product gives it. The presentation is taken as an
algebra isomorphism `ε` rather than read off the two algebra structures on a product type. -/
public theorem bijective_tmul_one_pi {R : Type u} [CommRing R] {ι : Type*} [Finite ι]
    (R' : ι → Type u) [∀ j, CommRing (R' j)] [∀ j, Algebra R (R' j)]
    (C : Type u) [CommRing C] [Algebra R C] (ε : R ≃ₐ[R] (∀ j, R' j)) :
    Function.Bijective (fun c : C ↦ fun j ↦ (c ⊗ₜ[R] (1 : R' j))) := by
  classical
  have := Fintype.ofFinite ι
  have key : (fun c : C ↦ fun j ↦ (c ⊗ₜ[R] (1 : R' j))) =
      ⇑(((Algebra.TensorProduct.rid R R C).symm.trans
        (Algebra.TensorProduct.congr (AlgEquiv.refl (R := R) (A₁ := C)) ε)).trans
        ((Algebra.TensorProduct.piRight R C C R').restrictScalars R)) := by
    funext c
    have hc : (Algebra.TensorProduct.rid R R C).symm c = c ⊗ₜ[R] (1 : R) := by
      rw [AlgEquiv.symm_apply_eq]
      simp
    funext j
    simp [hc]
  rw [key]
  exact AlgEquiv.bijective _

/-- **An algebra over a finite product ring is the product of its base changes along the
projections**, through the canonical maps of `AdequateFunctor.cechUnit`. -/
public theorem bijective_pi_cechUnit {ι : Type} [Finite ι]
    (D : ι → Type u) [∀ j, CommRing (D j)] (C : CommAlgCat.{u} (∀ j, D j)) :
    Function.Bijective (fun (c : ↥C) (j : ι) ↦
      ((cechUnit (Pi.evalRingHom D j)).app C).hom c) := by
  let : ∀ j, Algebra (∀ k, D k) (D j) := fun j ↦ (Pi.evalRingHom D j).toAlgebra
  let ε : (∀ k, D k) ≃ₐ[∀ k, D k] (∀ j, D j) :=
    { RingEquiv.refl (∀ k, D k) with commutes' := fun _ ↦ rfl }
  choose e he using fun j ↦ exists_ringEquiv_cechBaseChange (A := ∀ k, D k) (A' := D j) C
    (Pi.evalRingHom D j) rfl
  have key : (fun (c : ↥C) (j : ι) ↦ ((cechUnit (Pi.evalRingHom D j)).app C).hom c) =
      (fun (z : ∀ j, ↥C ⊗[∀ k, D k] D j) (j : ι) ↦ e j (z j)) ∘
        (fun (c : ↥C) (j : ι) ↦ c ⊗ₜ[∀ k, D k] (1 : D j)) :=
    funext fun c ↦ funext fun j ↦ (he j c).symm
  rw [key]
  exact (Equiv.piCongrRight fun j ↦ (e j).toEquiv).bijective.comp
    (bijective_tmul_one_pi (R := ∀ k, D k) D ↥C ε)

/-- The isomorphism of `AdequateFunctor.bijective_pi_cechUnit`: an algebra over a finite
product ring is the product of its base changes along the projections. -/
public noncomputable def cechUnitPiEquiv {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : ι → Type u) [∀ j, CommRing (D j)] (C : CommAlgCat.{u} (∀ j, D j)) :
    ↥C ≃+* (∀ j, ↥((cechBaseChange (Pi.evalRingHom D j)).obj C)) :=
  RingEquiv.ofBijective
    (RingHom.pi fun j ↦ ((cechUnit (Pi.evalRingHom D j)).app C).hom.toRingHom)
    (bijective_pi_cechUnit D C)

/-- **The spectrum of an algebra over a finite product ring is the disjoint union of the
spectra of its base changes along the projections.** The isomorphism is produced existentially
so that it is an opaque constant where it is used: typeclass synthesis does not see through a
local definition whose body is `AdequateFunctor.cechUnitPiEquiv`. -/
public theorem exists_isIso_specMap_cechUnitPi {ι : Type} [Finite ι]
    (D : ι → Type u) [∀ j, CommRing (D j)] (C : CommAlgCat.{u} (∀ j, D j)) :
    ∃ k : Spec (CommRingCat.of (∀ j, ↥((cechBaseChange (Pi.evalRingHom D j)).obj C))) ⟶
        Spec (CommRingCat.of ↥C),
      IsIso k ∧ ∀ j, Spec.map (CommRingCat.ofHom
          ((cechUnit (Pi.evalRingHom D j)).app C).hom.toRingHom) =
        Spec.map (CommRingCat.ofHom (Pi.evalRingHom
          (fun j ↦ ↥((cechBaseChange (Pi.evalRingHom D j)).obj C)) j)) ≫ k := by
  classical
  have := Fintype.ofFinite ι
  let kiso : CommRingCat.of ↥C ≅
      CommRingCat.of (∀ j, ↥((cechBaseChange (Pi.evalRingHom D j)).obj C)) :=
    (cechUnitPiEquiv D C).toCommRingCatIso
  refine ⟨Spec.map kiso.hom, ⟨Spec.map kiso.inv, ?_, ?_⟩, fun j ↦ ?_⟩
  · rw [← Spec.map_comp, kiso.inv_hom_id, Spec.map_id]
  · rw [← Spec.map_comp, kiso.hom_inv_id, Spec.map_id]
  · rw [← Spec.map_comp]
    rfl

section PiCover

variable {ι : Type} [Finite ι] (D : ι → Type u) [∀ j, CommRing (D j)]
  (C : CommAlgCat.{u} (∀ j, D j))

/-- **The spectrum of a base change of an algebra over a product ring along a projection is an
open subscheme of its spectrum.** -/
public theorem isOpenImmersion_specMap_cechUnit (j : ι) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      ((cechUnit (Pi.evalRingHom D j)).app C).hom.toRingHom)) := by
  obtain ⟨k, hk, hkeq⟩ := exists_isIso_specMap_cechUnitPi D C
  have := hk
  rw [hkeq j]
  exact @IsOpenImmersion.comp _ _ _ _ _
    (inferInstance : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Pi.evalRingHom (fun i ↦ ↥((cechBaseChange (Pi.evalRingHom D i)).obj C)) j))))
    inferInstance

/-- **The spectra of the base changes of an algebra over a product ring along the projections
cover its spectrum.** -/
public theorem iUnion_range_specMap_cechUnit :
    (⋃ j, Set.range (Spec.map (CommRingCat.ofHom
      ((cechUnit (Pi.evalRingHom D j)).app C).hom.toRingHom))) = Set.univ := by
  obtain ⟨k, hk, hkeq⟩ := exists_isIso_specMap_cechUnitPi D C
  have := hk
  have hcancel : ∀ y : ↥(Spec (CommRingCat.of ↥C)), k ((inv k) y) = y := fun y ↦ by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl
  refine Set.eq_univ_of_forall fun x ↦ ?_
  obtain ⟨j, p, hp⟩ := Set.mem_iUnion.mp (by
    rw [AlgebraicGeometry.iUnion_range_specMap_evalRingHom
      (fun j ↦ ↥((cechBaseChange (Pi.evalRingHom D j)).obj C))]
    exact Set.mem_univ ((inv k) x))
  refine Set.mem_iUnion.mpr ⟨j, p, ?_⟩
  rw [hkeq j]
  change k ((Spec.map (CommRingCat.ofHom (Pi.evalRingHom
    (fun j ↦ ↥((cechBaseChange (Pi.evalRingHom D j)).obj C)) j))) p) = x
  rw [hp]
  exact hcancel x

/-- **Two distinct base changes of an algebra over a product ring have no common source over
its spectrum.** -/
public theorem isEmpty_of_commSq_specMap_cechUnit {i j : ι} (hij : i ≠ j) {Z : Scheme.{u}}
    {a : Z ⟶ Spec (CommRingCat.of ↥((cechBaseChange (Pi.evalRingHom D i)).obj C))}
    {b : Z ⟶ Spec (CommRingCat.of ↥((cechBaseChange (Pi.evalRingHom D j)).obj C))}
    (h : a ≫ Spec.map (CommRingCat.ofHom
          ((cechUnit (Pi.evalRingHom D i)).app C).hom.toRingHom) =
      b ≫ Spec.map (CommRingCat.ofHom
          ((cechUnit (Pi.evalRingHom D j)).app C).hom.toRingHom)) :
    IsEmpty Z := by
  obtain ⟨k, hk, hkeq⟩ := exists_isIso_specMap_cechUnitPi D C
  have := hk
  rw [hkeq i, hkeq j] at h
  simp only [← Category.assoc] at h
  exact AlgebraicGeometry.isEmpty_of_commSq_specMap_evalRingHom
    (fun j ↦ ↥((cechBaseChange (Pi.evalRingHom D j)).obj C)) hij ((cancel_mono k).mp h)

end PiCover

end AdequateFunctor

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S : Scheme.{u}}

/-! ### The empty sieve covers an empty object of the site -/

/-- **An object of a chosen big site with empty underlying scheme is covered by the empty
sieve.** The empty family of morphisms is jointly surjective there, and the sieve it generates
is `⊥`. -/
public theorem bot_mem_topology_of_isEmpty (B : BigSite τ S) (Z : B.category)
    (hZ : IsEmpty Z.left.obj) : (⊥ : Sieve Z) ∈ B.topology Z := by
  have hgen : (⊥ : Sieve Z) =
      Sieve.generate (Presieve.ofArrows (fun _ : PEmpty.{1} ↦ Z) fun i ↦ i.elim) := by
    refine le_antisymm bot_le ?_
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    exact fun i ↦ i.elim
  rw [hgen]
  exact sieve_generate_mem_topology_of_coveringMorphismProperty B
    (fun _ : PEmpty.{1} ↦ Z) (fun i ↦ i.elim) (fun i ↦ i.elim) fun x ↦ (hZ.false x).elim

/-! ### The affine sections at a product base ring -/

section Product

variable (B : BigSite τ S) (F : SheafOfModules.{max u m} B.structureSheaf)
  {ι : Type} [Finite ι] (D : ι → Type u) [∀ j, CommRing (D j)]
  (hD : ∀ j, schemeSizeBelow B.cutoff (Spec (CommRingCat.of (D j))))
  (hmap : Spec (CommRingCat.of (∀ j, D j)) ⟶ S)

/-- **The sections of `F` over the spectrum of an algebra of the site over a product base ring
are the product of its sections over the spectra of the base changes to the factors.**

The base changes are the degree-one Čech terms of the projections, their spectra are the pieces
of the decomposition `Spec C = ⨆ⱼ Spec (C ⊗_{A'} A'ⱼ)`, and the restriction maps are the Čech
augmentations. -/
public theorem bijective_cechAugmentationOn_pi
    (C : AdequateFunctor.AlgebrasInSite (∀ j, D j) (schemeSizeBelow B.cutoff)) :
    Function.Bijective (fun (x : (affineSectionFunctor B F
        (CommRingCat.of (∀ j, D j)) hmap).obj (op (op C))) (j : ι) ↦
      ((AdequateFunctor.cechAugmentationOn (Pi.evalRingHom D j) (schemeSizeBelow B.cutoff)
        (siteBaseChangeClosed (Pi.evalRingHom D j) (hD j))
        (affineSectionFunctor B F (CommRingCat.of (∀ j, D j)) hmap)).app (op (op C))) x) := by
  -- the covering family, in the site and in schemes
  set V : ι → B.category := fun j ↦
    (affineSpecOver B (CommRingCat.of (∀ j, D j)) hmap).obj (op
      ((AdequateFunctor.cechBaseChangeOn (Pi.evalRingHom D j) (schemeSizeBelow B.cutoff)
        (siteBaseChangeClosed (Pi.evalRingHom D j) (hD j))).obj C)) with hV
  set w : ∀ j, V j ⟶ (affineSpecOver B (CommRingCat.of (∀ j, D j)) hmap).obj (op C) := fun j ↦
    (affineSpecOver B (CommRingCat.of (∀ j, D j)) hmap).map
      ((AdequateFunctor.cechUnitOn (Pi.evalRingHom D j) (schemeSizeBelow B.cutoff)
        (siteBaseChangeClosed (Pi.evalRingHom D j) (hD j))).app C).op with hw
  have hleft : ∀ j, (B.toOver.map (w j)).left = Spec.map (CommRingCat.ofHom
      ((AdequateFunctor.cechUnit (Pi.evalRingHom D j)).app C.obj).hom.toRingHom) :=
    fun j ↦ rfl
  -- the three inputs of the disjoint gluing lemma
  have hoi : ∀ j, IsOpenImmersion ((B.toOver.map (w j)).left) := fun j ↦ by
    rw [hleft j]
    exact AdequateFunctor.isOpenImmersion_specMap_cechUnit D C.obj j
  have hmono : ∀ j, Mono (w j) := fun j ↦
    (B.toOver ⋙ Over.forget S).mono_of_mono_map (@IsOpenImmersion.mono _ _ _ (hoi j))
  have hcov : Sieve.ofArrows V w ∈
      B.topology ((affineSpecOver B (CommRingCat.of (∀ j, D j)) hmap).obj (op C)) := by
    refine sieve_generate_mem_topology_of_coveringMorphismProperty B V w
      (fun j ↦ @coveringMorphismProperty_of_isOpenImmersion τ _ _ _ (hoi j)) fun x ↦ ?_
    obtain ⟨j, p, hp⟩ := Set.mem_iUnion.mp (by
      rw [AdequateFunctor.iUnion_range_specMap_cechUnit D C.obj]
      exact Set.mem_univ x)
    exact ⟨j, p, by rwa [hleft j]⟩
  have hdisj : ∀ i j, i ≠ j → ∀ {Z : B.category} (gi : Z ⟶ V i) (gj : Z ⟶ V j),
      gi ≫ w i = gj ≫ w j → (⊥ : Sieve Z) ∈ B.topology Z := by
    intro i j hij Z gi gj hg
    refine bot_mem_topology_of_isEmpty B Z ?_
    refine AdequateFunctor.isEmpty_of_commSq_specMap_cechUnit D C.obj hij
      (a := (B.toOver.map gi).left) (b := (B.toOver.map gj).left) ?_
    have hgl : (B.toOver.map gi).left ≫ (B.toOver.map (w i)).left =
        (B.toOver.map gj).left ≫ (B.toOver.map (w j)).left := by
      rw [← Over.comp_left, ← Over.comp_left, ← Functor.map_comp, ← Functor.map_comp, hg]
    rwa [hleft i, hleft j] at hgl
  -- the sheaf condition at that family
  rw [Function.bijective_iff_existsUnique]
  intro x
  obtain ⟨t, ht, huniq⟩ :=
    (isSheaf_forget_presheaf.{u, m} B F).existsUnique_section_of_disjoint_arrows
      w hcov hmono hdisj x
  exact ⟨t, funext ht, fun y hy ↦ huniq y fun j ↦ congrFun hy j⟩

/-- **The affine-section functor at a product base ring is the product of the degree-one Čech
terms of the projections.** The legs of the product cone are the Čech augmentations, and the
limit is detected objectwise by `Stacks.Adequate.bijective_cechAugmentationOn_pi`. -/
public noncomputable def isLimitFanCechOnceOn_pi :
    IsLimit (Fan.mk (affineSectionFunctor B F (CommRingCat.of (∀ j, D j)) hmap)
      (fun j ↦ AdequateFunctor.cechAugmentationOn (Pi.evalRingHom D j)
        (schemeSizeBelow B.cutoff) (siteBaseChangeClosed (Pi.evalRingHom D j) (hD j))
        (affineSectionFunctor B F (CommRingCat.of (∀ j, D j)) hmap))) :=
  PresheafOfModules.evaluationJointlyReflectsLimits _ _ fun X ↦
    isLimitOfBijectiveDiscreteCone _
      (bijective_cechAugmentationOn_pi B F D hD hmap X.unop.unop)

end Product

/-! ### The two statements -/

/-- **`Stacks.Adequate.StandardAffineProductAdequacy` holds.** For a finite standard affine
`τ`-covering `{Spec A'ⱼ ⟶ Spec A}` by affine schemes of the site, with each `F_{F, A'ⱼ}`
adequate, the affine-section functor at the product `A'₁ × ⋯ × A'ₘ` is adequate.

The affine-section functor at the product is the product of the degree-one Čech terms along
the projections, by `Stacks.Adequate.isLimitFanCechOnceOn_pi`; each of those is adequate by
[Stacks, Tag 06VA] on the site's domain of algebras,
`AdequateFunctor.isAdequate_pushforwardOn`, applied to `F_{F, A'ⱼ}` read through
`Stacks.Adequate.affineSectionRestriction`; and a finite product of adequate functors is
adequate by `Stacks.Adequate.affineAdequateFiniteProducts`. -/
public theorem standardAffineProductAdequacy {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) (F : SheafOfModules.{max u m} B.structureSheaf) :
    StandardAffineProductAdequacy.{u, m} B F := by
  classical
  intro A f hA n A' g hstd hsize hadq
  set D : Fin n → Type u := fun j ↦ ↥(coveringAlgebra A' g j)
  have hD : ∀ j, schemeSizeBelow B.cutoff (Spec (CommRingCat.of (D j))) := hsize
  set hmap : Spec (CommRingCat.of (∀ j, D j)) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap ↥A ↥(coveringPi A' g))) ≫ f with hmap0
  have hPi : schemeSizeBelow B.cutoff (Spec (CommRingCat.of (∀ j, D j))) :=
    schemeSizeBelow_Spec_pi B A' hsize
  -- the structure morphism of the `j`-th factor, read through the product
  have hgj : ∀ j, Spec.map (CommRingCat.ofHom (Pi.evalRingHom D j)) ≫ hmap = g j ≫ f :=
    fun j ↦ by
      rw [hmap0, ← Category.assoc, ← Spec.map_comp]
      refine congrArg (fun z ↦ z ≫ f) ?_
      change Spec.map (CommRingCat.ofHom (Spec.preimage (g j)).hom) = g j
      rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  refine affineAdequateFiniteProducts B (CommRingCat.of (∀ j, D j)) hPi (Fin n) inferInstance
    _ _ (isLimitFanCechOnceOn_pi B F D hD hmap) ?_
  rintro ⟨j⟩
  change AdequateFunctor.IsAdequate _ (AdequateFunctor.cechOnceOn (Pi.evalRingHom D j)
    (schemeSizeBelow B.cutoff) (siteBaseChangeClosed (Pi.evalRingHom D j) (hD j))
    (affineSectionFunctor B F (CommRingCat.of (∀ j, D j)) hmap))
  rw [AdequateFunctor.cechOnceOn_eq_pushforwardOn]
  refine AdequateFunctor.isAdequate_pushforwardOn.{m} (Pi.evalRingHom D j)
    (schemeSizeBelow B.cutoff) (siteBaseChangeClosed (Pi.evalRingHom D j) (hD j)) _ ?_
  obtain ⟨e⟩ := affineSectionRestriction.{u, m} B F (CommRingCat.of (∀ j, D j))
    (CommRingCat.of (D j)) (CommRingCat.ofHom (Pi.evalRingHom D j)) hmap
  have hadq' : AdequateFunctor.IsAdequate
      (AdequateFunctor.siteAlgebraInclusion (D j) (schemeSizeBelow B.cutoff))
      (affineSectionFunctor B F (CommRingCat.of (D j))
        (Spec.map (CommRingCat.ofHom (Pi.evalRingHom D j)) ≫ hmap)) := by
    rw [hgj j]
    exact hadq j
  exact hadq'.of_iso (e ≪≫ (AdequateFunctor.restrictFunctorOn.{max u m, u}
      (Pi.evalRingHom D j) (schemeSizeBelow B.cutoff)).mapIso
        (AdequateFunctor.presheafOfModulesUliftIso.{u, max u m} _ _) ≪≫
    (AdequateFunctor.restrictZeroOnIso.{max u m} (Pi.evalRingHom D j)
      (schemeSizeBelow B.cutoff) _).symm).symm

/-- **`Stacks.Adequate.StandardAffineDescent` holds, with no hypothesis.** This is the last
input of [Stacks, Tag 06VI] that the library did not supply:
`Stacks.Adequate.standardAffineDescent_of_productAdequacy` reduced it to
`Stacks.Adequate.StandardAffineProductAdequacy`, and
`Stacks.Adequate.standardAffineProductAdequacy` proves that. -/
public theorem standardAffineDescent {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) (F : SheafOfModules.{max u m} B.structureSheaf) :
    StandardAffineDescent.{u, m} B F :=
  standardAffineDescent_of_productAdequacy.{u, m} B F (standardAffineProductAdequacy.{u, m} B F)

end Stacks.Adequate

end
