module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableOverAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SiteQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SheafConditionAffine
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ObjectsAndColimits

/-!
# A colimit of affine schemes along thickenings that is not a formal algebraic space

Stacks 0AIU states that a directed colimit of algebraic spaces along thickenings, taken among
fppf sheaves, is a formal algebraic space. A formal algebraic space (Stacks 0AIM) includes the
set-theoretic condition of Stacks 0AIS: a representable sheaf surjects onto it. This file shows
that this condition can fail, so that Stacks 0AIU is false as written once the index set is
large compared with the chosen big fppf site.

Let `k` be a field, with `Spec k` in the site and over `S`, and let `σ` be a set of cardinality
at least the cutoff of the site. For a finite subset `μ ⊆ σ` put `A_μ = k ⊕ k^μ`, the
square-zero extension of `k` by `k^μ`. For `μ ⊆ ν` restriction of functions `k^ν → k^μ` gives a
surjection `A_ν → A_μ` whose kernel squares to zero, hence a thickening
`Spec A_μ ⟶ Spec A_ν`. So `μ ↦ Spec A_μ` is a directed system of affine schemes, in particular
of algebraic spaces, along thickenings.

Its colimit, formed among fppf sheaves, does not satisfy the set-theoretic condition when `σ`
has cardinality at least the cutoff of the site: no sheaf represented by an object of the site
surjects onto it.

## Main results

* `AlgebraicGeometry.FormalSpace.not_satisfiesSetTheoreticCondition_colimit_sqZeroSheafDiagram`:
  the colimit of the square-zero system does not satisfy the set-theoretic condition.
* `AlgebraicGeometry.FormalSpace.not_forall_isFormalAlgebraicSpace_colimit_thickenings`: over a
  nonempty scheme `S` of the site, the statement of Stacks 0AIU without a set-theoretic
  hypothesis is false.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AIU](https://stacks.math.columbia.edu/tag/0AIU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.FormalSpace

section Algebra

variable (k : Type u) [Field k] {σ : Type u}

/-- Restriction of `k`-valued functions along an inclusion of finite sets. -/
def sqZeroRes {μ ν : Finset σ} (h : μ ⊆ ν) : (ν → k) →ₗ[k] (μ → k) :=
  LinearMap.funLeft k k (fun t : μ ↦ (⟨t.1, h t.2⟩ : ν))

open scoped Classical in
/-- Extension by zero of `k`-valued functions on a finite set to a larger one. -/
def sqZeroExtend {μ ν : Finset σ} : (μ → k) →ₗ[k] (ν → k) where
  toFun m t := if ht : t.1 ∈ μ then m ⟨t.1, ht⟩ else 0
  map_add' m n := by
    funext t
    by_cases ht : t.1 ∈ μ <;> simp [ht]
  map_smul' c m := by
    funext t
    by_cases ht : t.1 ∈ μ <;> simp [ht]

/-- Restricting an extension by zero along the same inclusion gives back the original function. -/
theorem sqZeroRes_comp_sqZeroExtend {μ ν : Finset σ} (h : μ ⊆ ν) :
    (sqZeroRes k h).comp (sqZeroExtend k) = LinearMap.id := by
  classical
  ext m t
  simp [sqZeroRes, sqZeroExtend, LinearMap.funLeft_apply, t.2]

/-- Extending a function on `{s}` by zero and restricting it to a subset of `ν` avoiding `s`
gives zero. -/
theorem sqZeroRes_comp_sqZeroExtend_eq_zero {μ ν : Finset σ} {s : σ} (hs : s ∉ μ) (h : μ ⊆ ν) :
    (sqZeroRes k h).comp (sqZeroExtend k (μ := {s})) = 0 := by
  classical
  ext m t
  have ht : t.1 ≠ s := fun hts ↦ hs (hts ▸ t.2)
  simp [sqZeroRes, sqZeroExtend, LinearMap.funLeft_apply, ht]

/-- Restriction along the identity inclusion is the identity. -/
theorem sqZeroRes_refl (μ : Finset σ) :
    sqZeroRes k (subset_refl μ) = LinearMap.id := by
  ext m t
  rfl

/-- Restriction along a composite inclusion is the composite of the restrictions. -/
theorem sqZeroRes_comp {μ ν ρ : Finset σ} (h₁ : μ ⊆ ν) (h₂ : ν ⊆ ρ) :
    (sqZeroRes k h₁).comp (sqZeroRes k h₂) = sqZeroRes k (h₁.trans h₂) := by
  ext m t
  rfl

/-- The kernel of the restriction map of square-zero extensions consists of elements of square
zero. -/
theorem mul_self_eq_zero_of_map_sqZeroRes_eq_zero {μ ν : Finset σ} (h : μ ⊆ ν)
    (x : TrivSqZeroExt k (ν → k)) (hx : TrivSqZeroExt.map (sqZeroRes k h) x = 0) :
    x * x = 0 := by
  have hx' : x = TrivSqZeroExt.inr x.snd :=
    TrivSqZeroExt.ext (by simpa using congrArg TrivSqZeroExt.fst hx) rfl
  rw [hx']
  simp

/-- The restriction map `k ⊕ k^ν → k ⊕ k^μ` of square-zero extensions is surjective. -/
theorem surjective_map_sqZeroRes {μ ν : Finset σ} (h : μ ⊆ ν) :
    Function.Surjective (TrivSqZeroExt.map (sqZeroRes k h)) := by
  intro y
  refine ⟨TrivSqZeroExt.map (sqZeroExtend k) y, ?_⟩
  rw [← AlgHom.comp_apply, ← TrivSqZeroExt.map_comp_map, sqZeroRes_comp_sqZeroExtend,
    TrivSqZeroExt.map_id]
  rfl

/-- The spectrum of the restriction map of square-zero extensions is a thickening. -/
theorem isThickening_specMap_sqZeroRes {μ ν : Finset σ} (h : μ ⊆ ν) :
    Stacks.Thickenings.IsThickening
      (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (sqZeroRes k h)).toRingHom)) := by
  have hsurj : Function.Surjective (TrivSqZeroExt.map (sqZeroRes k h)).toRingHom :=
    surjective_map_sqZeroRes k h
  refine ⟨IsClosedImmersion.spec_of_surjective _ hsurj, ?_⟩
  change Function.Surjective (PrimeSpectrum.comap (TrivSqZeroExt.map (sqZeroRes k h)).toRingHom)
  rw [← Set.range_eq_univ, range_comap_of_surjective _ _ hsurj, Set.eq_univ_iff_forall]
  refine fun p ↦ (PrimeSpectrum.mem_zeroLocus _ _).2 fun x hx ↦ p.isPrime.mem_of_pow_mem 2 ?_
  rw [pow_two, mul_self_eq_zero_of_map_sqZeroRes_eq_zero k h x hx]
  exact p.asIdeal.zero_mem

omit [Field k] in
/-- The ring `k ⊕ k^μ` has cardinality at most `max ℵ₀ #k`. -/
theorem mk_sqZero_le (μ : Finset σ) :
    #(TrivSqZeroExt k (μ → k)) ≤ max ℵ₀ #k := by
  have hm : ℵ₀ ≤ max ℵ₀ #k := le_max_left _ _
  have h2 : #(μ → k) ≤ max ℵ₀ #k := by
    rw [← Cardinal.power_def, Cardinal.mk_coe_finset]
    exact (Cardinal.power_le_power_right (le_max_right _ _)).trans (Cardinal.power_nat_le hm)
  change #(k × (μ → k)) ≤ _
  rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
  exact (mul_le_mul' (le_max_right _ _) h2).trans (Cardinal.mul_eq_self hm).le

end Algebra

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (t : Spec (.of k) ⟶ S) (σ : Type u)

attribute [local instance] bigFppfOver_subcanonical

include hk in
/-- The affine scheme `Spec (k ⊕ k^μ)` is an object of the site. -/
theorem contains_spec_sqZero (μ : Finset σ) :
    B.Contains (Spec (.of (TrivSqZeroExt k (μ → k)))) :=
  Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hk
    (mk_sqZero_le k μ)

/-- The affine scheme `Spec (k ⊕ k^μ)` over `S`, as an object of the site. -/
def sqZeroStage (μ : Finset σ) : BigAffineFppf B S hS :=
  ⟨Over.mk (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom (algebraMap k (TrivSqZeroExt k (μ → k)))) ≫ t) :
        B.obj (contains_spec_sqZero B k hk σ μ) ⟶ B.obj hS), by
    change IsAffine (Spec _)
    infer_instance⟩

/-- The morphism of stages induced by a morphism of `k`-algebras. -/
def sqZeroStageHom {μ ν : Finset σ}
    (φ : TrivSqZeroExt k (ν → k) →ₐ[k] TrivSqZeroExt k (μ → k)) :
    sqZeroStage B S hS k hk t σ μ ⟶ sqZeroStage B S hS k hk t σ ν :=
  ObjectProperty.homMk <| Over.homMk
    (U := (sqZeroStage B S hS k hk t σ μ).1) (V := (sqZeroStage B S hS k hk t σ ν).1)
    (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom))) (by
      apply ObjectProperty.hom_ext
      change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k (TrivSqZeroExt k (ν → k)))) ≫ t =
        Spec.map (CommRingCat.ofHom (algebraMap k (TrivSqZeroExt k (μ → k)))) ≫ t
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 3
      exact φ.comp_algebraMap)

/-- The underlying morphism of schemes of `sqZeroStageHom` is the spectrum of the given map. -/
theorem toScheme_map_sqZeroStageHom {μ ν : Finset σ}
    (φ : TrivSqZeroExt k (ν → k) →ₐ[k] TrivSqZeroExt k (μ → k)) :
    (BigAffineFppf.toScheme B S hS).map (sqZeroStageHom B S hS k hk t σ φ) =
      Spec.map (CommRingCat.ofHom φ.toRingHom) :=
  rfl

/-- `sqZeroStageHom` turns composition of `k`-algebra maps into composition of morphisms. -/
theorem sqZeroStageHom_comp {μ ν ρ : Finset σ}
    (φ : TrivSqZeroExt k (ν → k) →ₐ[k] TrivSqZeroExt k (μ → k))
    (ψ : TrivSqZeroExt k (ρ → k) →ₐ[k] TrivSqZeroExt k (ν → k)) :
    sqZeroStageHom B S hS k hk t σ φ ≫ sqZeroStageHom B S hS k hk t σ ψ =
      sqZeroStageHom B S hS k hk t σ (φ.comp ψ) := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom) =
    Spec.map (CommRingCat.ofHom (φ.comp ψ).toRingHom)
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- `sqZeroStageHom` sends the identity of `k ⊕ k^μ` to the identity. -/
theorem sqZeroStageHom_id (μ : Finset σ) :
    sqZeroStageHom B S hS k hk t σ (AlgHom.id k (TrivSqZeroExt k (μ → k))) = 𝟙 _ := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom (AlgHom.id k (TrivSqZeroExt k (μ → k))).toRingHom) =
    𝟙 (Spec (.of (TrivSqZeroExt k (μ → k))))
  rw [← Spec.map_id]
  rfl

/-- `sqZeroStageHom` turns composition of maps of square-zero extensions into composition. -/
private theorem sqZeroStageHom_map_comp {μ ν ρ : Finset σ} (f : (ν → k) →ₗ[k] (μ → k))
    (g : (ρ → k) →ₗ[k] (ν → k)) :
    sqZeroStageHom B S hS k hk t σ (TrivSqZeroExt.map f) ≫
        sqZeroStageHom B S hS k hk t σ (TrivSqZeroExt.map g) =
      sqZeroStageHom B S hS k hk t σ (TrivSqZeroExt.map (f.comp g)) := by
  rw [sqZeroStageHom_comp, TrivSqZeroExt.map_comp_map]

/-- A morphism of lifted finite subsets of `σ` is an inclusion of the underlying subsets. -/
theorem sqZero_subset {μ ν : ULift.{u + 1} (Finset σ)} (h : μ ⟶ ν) : μ.down ⊆ ν.down :=
  (leOfHom h : μ ≤ ν)

open scoped Classical in
/-- The lifted finite subsets of `σ` are directed under inclusion. -/
instance : IsDirected (ULift.{u + 1} (Finset σ)) (· ≤ ·) :=
  ⟨fun a b ↦ ⟨⟨a.down ∪ b.down⟩, Finset.subset_union_left, Finset.subset_union_right⟩⟩

/-- The directed system `μ ↦ Spec (k ⊕ k^μ)` of affine schemes over `S`, indexed by the finite
subsets of `σ`. -/
def sqZeroDiagram : ULift.{u + 1} (Finset σ) ⥤ BigAffineFppf B S hS where
  obj μ := sqZeroStage B S hS k hk t σ μ.down
  map {μ ν} h := sqZeroStageHom B S hS k hk t σ
    (TrivSqZeroExt.map (sqZeroRes k (sqZero_subset σ h)))
  map_id μ := by
    rw [sqZeroRes_refl, TrivSqZeroExt.map_id]
    exact sqZeroStageHom_id B S hS k hk t σ μ.down
  map_comp {μ ν ρ} g h := by
    rw [sqZeroStageHom_comp, ← TrivSqZeroExt.map_comp_map, sqZeroRes_comp]

/-- The transition morphisms of the square-zero system are thickenings. -/
theorem isThickening_sqZeroDiagram_map {μ ν : ULift.{u + 1} (Finset σ)} (h : μ ⟶ ν) :
    Stacks.Thickenings.IsThickening
      ((BigAffineFppf.toScheme B S hS).map ((sqZeroDiagram B S hS k hk t σ).map h)) :=
  isThickening_specMap_sqZeroRes k (sqZero_subset σ h)

/-- The square-zero system, as a diagram of represented fppf sheaves. -/
def sqZeroSheafDiagram : ULift.{u + 1} (Finset σ) ⥤ FppfSheaf B S hS :=
  sqZeroDiagram B S hS k hk t σ ⋙ BigAffineFppf.inclusion B S hS ⋙
    (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}

/-- The stages of the square-zero system are algebraic spaces. -/
theorem isAlgebraicSpaceULift_sqZeroSheafDiagram_obj (μ : ULift.{u + 1} (Finset σ)) :
    Space.IsAlgebraicSpaceULift.{u + 1} B S hS ((sqZeroSheafDiagram B S hS k hk t σ).obj μ).obj :=
  Space.isAlgebraicSpaceULift_uliftYoneda B S hS _

/-- The transition morphisms of the square-zero system are representable thickenings. -/
theorem isRepresentableThickeningULift_sqZeroSheafDiagram_map
    {μ ν : ULift.{u + 1} (Finset σ)} (h : μ ⟶ ν) :
    Space.IsRepresentableThickeningULift.{u + 1} B S hS
      ((sqZeroSheafDiagram B S hS k hk t σ).map h).hom :=
  MorphismProperty.relative_map
    (P := MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
    (isThickening_sqZeroDiagram_map B S hS k hk t σ h)

/-- The transition morphisms of the square-zero system are monomorphisms of sheaves. -/
theorem mono_sqZeroSheafDiagram_map {μ ν : ULift.{u + 1} (Finset σ)} (h : μ ⟶ ν) :
    Mono ((sqZeroSheafDiagram B S hS k hk t σ).map h) := by
  let m := (BigAffineFppf.inclusion B S hS).map ((sqZeroDiagram B S hS k hk t σ).map h)
  have : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map m) :=
    (isThickening_sqZeroDiagram_map B S hS k hk t σ h).1
  refine (Sheaf.Hom.mono_iff_presheaf_mono _ _ _).2
    ((NatTrans.mono_iff_mono_app _).2 fun Y ↦ (mono_iff_injective _).2 ?_)
  rintro ⟨a⟩ ⟨b⟩ hab
  have hab' : a ≫ m = b ≫ m := congrArg ULift.down hab
  congr 1
  apply (BigFppfOver.toScheme B S hS).map_injective
  rw [← cancel_mono ((BigFppfOver.toScheme B S hS).map m), ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp, hab']

/-- **The colimit of the square-zero system does not satisfy the set-theoretic condition** of
Stacks 0AIS, as soon as the index set `σ` has cardinality at least the cutoff of the site: no
sheaf represented by an object of the site surjects onto it. -/
theorem not_satisfiesSetTheoreticCondition_colimit_sqZeroSheafDiagram (hσ : B.cutoff ≤ #σ) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    ¬ SatisfiesSetTheoreticCondition B S hS (colimit (sqZeroSheafDiagram B S hS k hk t σ)) := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  rintro ⟨U, R, hU, hR, ⟨eU⟩, -, f, hf, -⟩
  let J := BigFppfOver.topology B S hS
  let Λ := ULift.{u + 1} (Finset σ)
  let D := sqZeroDiagram B S hS k hk t σ
  let E := sqZeroSheafDiagram B S hS k hk t σ
  let X := colimit E
  have htrans : ∀ (i j : Λ) (g : i ⟶ j), Mono (E.map g) :=
    fun _ _ g ↦ mono_sqZeroSheafDiagram_map B S hS k hk t σ g
  let ξ : X.obj.obj (op U) := f.hom.app (op U) (eU.inv.app (op U) ⟨𝟙 U⟩)
  have hξ : ∀ {T : BigFppfOver B S hS} (u : T ⟶ U),
      f.hom.app (op T) (eU.inv.app (op T) ⟨u⟩) = X.obj.map u.op ξ := by
    intro T u
    have h1 := NatTrans.naturality_apply eU.inv u.op ⟨𝟙 U⟩
    have h2 := NatTrans.naturality_apply f.hom u.op (eU.inv.app (op U) ⟨𝟙 U⟩)
    refine Eq.trans ?_ (h2.trans rfl)
    rw [← h1]
    congr 2
  have hf' : ∀ {T : BigFppfOver B S hS} (a : hU.obj.obj (op T)),
      ∃ u : T ⟶ U, f.hom.app (op T) a = f.hom.app (op T) (eU.inv.app (op T) ⟨u⟩) := by
    intro T a
    obtain ⟨u, hu⟩ : ∃ u : T ⟶ U, eU.hom.app (op T) a = ULift.up u := ⟨_, rfl⟩
    refine ⟨u, ?_⟩
    rw [← hu, Iso.hom_inv_id_app_apply]
  let Uo := (BigFppfOver.toScheme B S hS).obj U
  let VW : Uo.affineOpens → BigFppfOver B S hS := fun W ↦ Over.mk
    (Y := (⟨(W.1 : Scheme.{u}), Scheme.size_lt_of_isOpenImmersion W.1.ι U.left.2⟩ : B.Schemes))
    (ObjectProperty.homMk (W.1.ι ≫ U.hom.hom))
  let πW : ∀ W, VW W ⟶ U := fun W ↦ Over.homMk (ObjectProperty.homMk W.1.ι)
    (by apply ObjectProperty.hom_ext; rfl)
  have hcovU : Sieve.generate (Presieve.ofArrows VW πW) ∈ J U :=
    BigFppfOver.sieve_generate_ofArrows_mem_topology VW πW
      (Scheme.zariskiPrecoverage_le_fppfPrecoverage _
        (Uo.openCoverOfIsOpenCover (fun W : Uo.affineOpens ↦ W.1)
          (iSup_affineOpens_eq_top Uo)).mem₀)
  have hstage : ∀ W, ∃ (μ : Λ) (y : (E.obj μ).obj.obj (op (VW W))),
      (colimit.ι E μ).hom.app (op (VW W)) y = X.obj.map (πW W).op ξ := by
    intro W
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj (VW W)) := W.2
    have hqc := isQuasiCompactObject_over_of_compact_scheme B S hS (VW W)
    have hbij := (Sheaf.injective_and_bijective_colimit_post_sheafSections J E (VW W)).2.2.1
      hqc htrans
    let G := (sheafSections J (Type (u + 1))).obj (op (VW W))
    obtain ⟨z, hz⟩ := hbij.2 (X.obj.map (πW W).op ξ)
    obtain ⟨μ, y, rfl⟩ := Types.jointly_surjective_of_isColimit (colimit.isColimit (E ⋙ G)) z
    refine ⟨μ, y, ?_⟩
    rw [← hz]
    exact (ConcreteCategory.congr_hom (colimit.ι_post E G μ) y).symm
  choose μW yW hyW using hstage
  let Sig : Set σ := ⋃ W, ((μW W).down : Set σ)
  have hSig : #Sig < B.cutoff := by
    calc #Sig ≤ #Uo.affineOpens * ⨆ W, #((μW W).down : Set σ) := Cardinal.mk_iUnion_le _
      _ < B.cutoff := Cardinal.mul_lt_of_lt B.aleph0_lt_cutoff.le
        ((Uo.mk_affineOpens_le_size).trans_lt U.left.2)
        ((ciSup_le' fun W ↦ (Finset.finite_toSet _).lt_aleph0.le).trans_lt B.aleph0_lt_cutoff)
  obtain ⟨s, hs⟩ : ∃ s, s ∉ Sig := by
    by_contra! hcon
    rw [Set.eq_univ_of_forall hcon, Cardinal.mk_univ] at hSig
    exact absurd hσ (not_le.mpr hSig)
  have hsW : ∀ W, s ∉ (μW W).down := fun W hmem ↦ hs (Set.mem_iUnion.2 ⟨W, hmem⟩)
  let s₁ : Λ := ⟨{s}⟩
  let T : BigFppfOver B S hS := (BigAffineFppf.inclusion B S hS).obj (D.obj s₁)
  let p : X.obj.obj (op T) := (colimit.ι E s₁).hom.app (op T) (ULift.up (𝟙 T))
  have : Presheaf.IsLocallySurjective J f.hom := (Sheaf.isLocallySurjective_iff_epi f).2 hf
  have himg : Presheaf.imageSieve f.hom p ∈ J T := Presheaf.imageSieve_mem J f.hom p
  let R' : Sieve T :=
    { arrows := fun Y g ↦ ∃ (μ : Λ) (_ : s ∉ μ.down) (z : (E.obj μ).obj.obj (op Y)),
        (colimit.ι E μ).hom.app (op Y) z = X.obj.map g.op p
      downward_closed := by
        rintro Y Z g ⟨μ, hμ, z, hz⟩ h
        refine ⟨μ, hμ, (E.obj μ).obj.map h.op z, ?_⟩
        rw [NatTrans.naturality_apply, hz, op_comp, CategoryTheory.Functor.map_comp_apply] }
  have hR' : R' ∈ J T := by
    refine J.transitive himg R' ?_
    rintro Y g ⟨a, ha⟩
    obtain ⟨u, hu⟩ := hf' a
    refine J.superset_covering ?_ (J.pullback_stable u hcovU)
    rintro Z h ⟨_, a', _, ⟨W⟩, hfac⟩
    refine ⟨μW W, hsW W, (E.obj (μW W)).obj.map a'.op (yW W), ?_⟩
    rw [NatTrans.naturality_apply, hyW, ← CategoryTheory.Functor.map_comp_apply, ← op_comp,
      hfac, op_comp, CategoryTheory.Functor.map_comp_apply, ← hξ u, ← hu, ha,
      ← CategoryTheory.Functor.map_comp_apply, ← op_comp]
  let ρ₀ : D.obj s₁ ⟶ D.obj s₁ :=
    sqZeroStageHom B S hS k hk t σ (TrivSqZeroExt.map (0 : (({s} : Finset σ) → k) →ₗ[k] _))
  let ρ : T ⟶ T := (BigAffineFppf.inclusion B S hS).map ρ₀
  have hkey : ∀ {Y : BigFppfOver B S hS} (g : Y ⟶ T), R' g → g ≫ ρ = g := by
    rintro Y g ⟨μ, hμ, z, hz⟩
    let ν : Λ := ⟨μ.down ∪ {s}⟩
    let hμν : μ ⟶ ν := homOfLE (Finset.subset_union_left : μ.down ⊆ μ.down ∪ {s})
    let hsν : s₁ ⟶ ν := homOfLE (Finset.subset_union_right : ({s} : Finset σ) ⊆ μ.down ∪ {s})
    have hw : ∀ {a b : Λ} (h : a ⟶ b) (w : (E.obj a).obj.obj (op Y)),
        (colimit.ι E a).hom.app (op Y) w =
          (colimit.ι E b).hom.app (op Y) ((E.map h).hom.app (op Y) w) := by
      intro a b h w
      rw [← colimit.w E h]
      rfl
    have hp : X.obj.map g.op p = (colimit.ι E s₁).hom.app (op Y) (ULift.up g) := by
      refine (NatTrans.naturality_apply (colimit.ι E s₁).hom g.op _).symm.trans ?_
      congr 1
    have hinj : Function.Injective ((colimit.ι E ν).hom.app (op Y)) :=
      (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1
        ((Sheaf.Hom.mono_iff_presheaf_mono J _ _).1
          (Sheaf.mono_colimit_ι_of_mono_transition E htrans ν)) (op Y))
    have heq' : g ≫ (BigAffineFppf.inclusion B S hS).map (D.map hsν) =
        z.down ≫ (BigAffineFppf.inclusion B S hS).map (D.map hμν) :=
      congrArg ULift.down
        (hinj ((hw hsν (ULift.up g)).symm.trans (hp.symm.trans (hz.symm.trans (hw hμν z)))))
    let ε₀ : D.obj ν ⟶ D.obj s₁ := sqZeroStageHom B S hS k hk t σ
      (TrivSqZeroExt.map (sqZeroExtend k (μ := ({s} : Finset σ)) (ν := μ.down ∪ {s})))
    let ε : (BigAffineFppf.inclusion B S hS).obj (D.obj ν) ⟶ T :=
      (BigAffineFppf.inclusion B S hS).map ε₀
    have hε₁₀ : D.map hsν ≫ ε₀ = 𝟙 _ := by
      refine (sqZeroStageHom_map_comp B S hS k hk t σ _ _).trans ?_
      rw [sqZeroRes_comp_sqZeroExtend, TrivSqZeroExt.map_id]
      exact sqZeroStageHom_id B S hS k hk t σ _
    have hε₁ : (BigAffineFppf.inclusion B S hS).map (D.map hsν) ≫ ε = 𝟙 T := by
      rw [← CategoryTheory.Functor.map_comp, hε₁₀, CategoryTheory.Functor.map_id]
    have hε₂₀ : D.map hμν ≫ ε₀ ≫ ρ₀ = D.map hμν ≫ ε₀ := by
      change sqZeroStageHom B S hS k hk t σ _ ≫ sqZeroStageHom B S hS k hk t σ _ ≫
          sqZeroStageHom B S hS k hk t σ _ =
        sqZeroStageHom B S hS k hk t σ _ ≫ sqZeroStageHom B S hS k hk t σ _
      rw [sqZeroStageHom_map_comp, sqZeroStageHom_map_comp, sqZeroStageHom_map_comp,
        LinearMap.comp_zero, sqZeroRes_comp_sqZeroExtend_eq_zero k hμ, LinearMap.comp_zero]
    calc g ≫ ρ = (g ≫ (BigAffineFppf.inclusion B S hS).map (D.map hsν) ≫ ε) ≫ ρ := by
          rw [hε₁, Category.comp_id]
      _ = z.down ≫ (BigAffineFppf.inclusion B S hS).map (D.map hμν) ≫ ε ≫ ρ := by
          rw [← Category.assoc g, heq']
          simp only [Category.assoc]
      _ = z.down ≫ (BigAffineFppf.inclusion B S hS).map (D.map hμν) ≫ ε := by
          simp only [ε, ρ, ← CategoryTheory.Functor.map_comp, hε₂₀]
      _ = g := by
          rw [← Category.assoc, ← heq', Category.assoc, hε₁, Category.comp_id]
  have hρ : ρ = 𝟙 T := by
    have hsh := ((isSheaf_iff_isSheaf_of_type J _).1 (J.uliftYoneda.{u + 1}.obj T).property) R' hR'
    have h := hsh.isSeparatedFor.ext (t₁ := (ULift.up ρ : ULift.{u + 1} (T ⟶ T)))
      (t₂ := ULift.up (𝟙 T)) (fun Y g hg ↦ by
        change ULift.up (g ≫ ρ) = ULift.up (g ≫ 𝟙 T)
        rw [hkey g hg, Category.comp_id])
    exact congrArg ULift.down h
  have hρ' := congrArg (BigFppfOver.toScheme B S hS).map hρ
  rw [CategoryTheory.Functor.map_id] at hρ'
  change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map
    (0 : (({s} : Finset σ) → k) →ₗ[k] _)).toRingHom) = 𝟙 (Spec (.of _)) at hρ'
  rw [← Spec.map_id] at hρ'
  have hring := Spec.map_injective hρ'
  have happ := congrArg (fun φ : CommRingCat.of (TrivSqZeroExt k (({s} : Finset σ) → k)) ⟶
      CommRingCat.of (TrivSqZeroExt k (({s} : Finset σ) → k)) ↦
      φ.hom (TrivSqZeroExt.inr (fun _ ↦ (1 : k)))) hring
  change TrivSqZeroExt.map (0 : (({s} : Finset σ) → k) →ₗ[k] _)
      (TrivSqZeroExt.inr (fun _ ↦ (1 : k))) = TrivSqZeroExt.inr (fun _ ↦ (1 : k)) at happ
  rw [TrivSqZeroExt.map_inr, LinearMap.zero_apply] at happ
  have h1 := congrArg (fun x ↦ x.snd ⟨s, Finset.mem_singleton_self s⟩) happ
  simp at h1

/-- **Stacks 0AIU is false as written.** Let `S` be a nonempty scheme of a big fppf site. It is
not the case that the colimit, formed among fppf sheaves, of every directed system of algebraic
spaces over `S` along representable thickenings is a formal algebraic space over `S`. -/
theorem not_forall_isFormalAlgebraicSpace_colimit_thickenings [Nonempty S] :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    ¬ ∀ (Λ : Type (u + 1)) [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
      (E : Λ ⥤ FppfSheaf B S hS),
      (∀ i : Λ, Space.IsAlgebraicSpaceULift.{u + 1} B S hS (E.obj i).obj) →
      (∀ ⦃i j : Λ⦄ (g : i ⟶ j),
        Space.IsRepresentableThickeningULift.{u + 1} B S hS (E.map g).hom) →
      IsFormalAlgebraicSpace B S hS (colimit E) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  intro h
  let x : S := Classical.arbitrary S
  have hk := B.residueField_spec_contains hS x
  let σ : Type u := B.cutoff.out
  exact not_satisfiesSetTheoreticCondition_colimit_sqZeroSheafDiagram B S hS (S.residueField x)
    hk (S.fromSpecResidueField x) σ (Cardinal.mk_out B.cutoff).ge
    (h (ULift.{u + 1} (Finset σ)) (sqZeroSheafDiagram B S hS (S.residueField x) hk
      (S.fromSpecResidueField x) σ)
      (isAlgebraicSpaceULift_sqZeroSheafDiagram_obj B S hS _ hk _ σ)
      (fun _ _ g ↦ isRepresentableThickeningULift_sqZeroSheafDiagram_map B S hS _ hk _ σ g)).1

end AlgebraicGeometry.FormalSpace

end
