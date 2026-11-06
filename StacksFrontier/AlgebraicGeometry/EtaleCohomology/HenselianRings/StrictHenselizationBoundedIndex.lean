module

public import Mathlib.Algebra.Category.CommAlgCat.FiniteType
public import Mathlib.Algebra.MvPolynomial.Cardinal
public import Mathlib.CategoryTheory.InducedCategory
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationLimit
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective

/-!
# A bounded cofinal family of affine étale neighbourhoods of a geometric point

Let `s` be a geometric point of a scheme `S`, and let `ι₀ : Spec R ⟶ S` be an affine open
through which `s` factors. This file produces a small cofiltered category `I` and an initial
functor from it to the étale neighbourhoods of `s` all of whose stages are affine, together with
two explicit cardinal bounds: the stages have size at most `size S`, and the objects of `I` are
at most `2 ^ max ℵ₀ #R * #k ^ max ℵ₀ #R` in number, `k` being the field of `s`.

Restricting the strict henselization cone along it, `Spec 𝒪_{S, s}^{sh}` is the limit of this
bounded system (`AlgebraicGeometry.strictHenselizationBoundedConeIsLimit`).

## Main definitions

* `AlgebraicGeometry.EtaleNeighborhoodBoundedIndex`: presentations of a finitely generated
  `R`-algebra `A`, with a lift of `s` to `Spec A`, such that `Spec A ⟶ Spec R ⟶ S` is étale.
* `AlgebraicGeometry.etaleNeighborhoodBoundedFunctor`: the functor to the étale neighbourhoods,
  fully faithful on the category induced on the index.

## Main results

* `AlgebraicGeometry.etaleNeighborhoodBoundedIndex_weaklyInitial`: every étale neighbourhood of
  `s` is refined by a member of the family.
* `AlgebraicGeometry.mk_etaleNeighborhoodBoundedIndex_le` and
  `AlgebraicGeometry.size_etaleNeighborhoodBoundedStage_le`: the two cardinal bounds.
* `AlgebraicGeometry.strictHenselizationBoundedConeIsLimit`: the strict henselization is the
  limit of the bounded family.

## Implementation notes

The family `AlgebraicGeometry.etaleNeighborhoodAffineIndex` already presents the strict
henselization over a small index, but it is extracted from essential smallness of the category
of neighbourhoods and so carries no cardinality information. The bounds here are what a
cofinality-free limit argument inside a size-bounded site consumes: a uniform bound on the
stages and a bound on the number of them, each below the cutoff. This is the scheme-level analogue
of `StacksFrontier/AlgebraicGeometry/Spaces/Decent/BoundedElementaryEtaleNeighborhoodModel.lean`,
for étale rather than elementary étale neighbourhoods and for a geometric rather than an
ordinary point.

## References

* [Stacks Project, Tag 04HX](https://stacks.math.columbia.edu/tag/04HX)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry

variable (E : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : E.Contains S) (s : GeometricPoint S)
  {R : CommRingCat.{u}}

/-! ### Presented algebras over the affine base -/

/-- The ring presented by a presentation datum over `R`. -/
abbrev boundedPresRing (T : FGAlgCatSkeleton (R : Type u)) : CommRingCat.{u} :=
  CommRingCat.of (T.eval.obj : Type u)

variable {S} (ι₀ : Spec R ⟶ S) [IsOpenImmersion ι₀]

/-- The morphism `Spec A ⟶ Spec R ⟶ S` from the spectrum of a presented algebra. -/
def boundedPresMap (T : FGAlgCatSkeleton (R : Type u)) : Spec (boundedPresRing T) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap (R : Type u) (T.eval.obj : Type u))) ≫ ι₀

/-- The cardinality of a presented algebra is at most `max ℵ₀ #R`. -/
theorem mk_boundedPresRing_le (T : FGAlgCatSkeleton (R : Type u)) :
    #(boundedPresRing T) ≤ max ℵ₀ #R :=
  (Cardinal.mk_le_of_surjective (f := Ideal.Quotient.mk T.I)
    Ideal.Quotient.mk_surjective).trans (Cardinal.mk_mvPolynomial_fin_le R T.n)

include ι₀ in
/-- The spectrum of a presented algebra is no larger than `S`. -/
theorem size_spec_boundedPresRing_le (T : FGAlgCatSkeleton (R : Type u)) :
    (Spec (boundedPresRing T)).size ≤ S.size := by
  refine le_trans ?_ (Scheme.size_le_of_isOpenImmersion ι₀)
  rw [Scheme.size_Spec, Scheme.size_Spec]
  exact max_le (le_max_left _ _) (mk_boundedPresRing_le T)

omit [IsOpenImmersion ι₀] in
/-- There are at most `2 ^ max ℵ₀ #R` presentations of finitely generated `R`-algebras. -/
theorem mk_fgAlgCatSkeleton_le' (R : CommRingCat.{u}) :
    #(FGAlgCatSkeleton (R : Type u)) ≤ 2 ^ max ℵ₀ #R := by
  have hpow : ℵ₀ ≤ (2 : Cardinal.{u}) ^ max ℵ₀ #R :=
    (le_max_left _ _).trans (Cardinal.cantor _).le
  have hinj : Function.Injective
      (fun A : FGAlgCatSkeleton (R : Type u) => (⟨ULift.up A.n, A.I⟩ :
        Σ m : ULift.{u} ℕ, Ideal (MvPolynomial (Fin m.down) R))) := by
    rintro ⟨n, I⟩ ⟨n', I'⟩ h
    simp only [Sigma.mk.injEq, ULift.up.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    simpa using h2
  calc #(FGAlgCatSkeleton (R : Type u))
      ≤ #(Σ m : ULift.{u} ℕ, Ideal (MvPolynomial (Fin m.down) R)) :=
        Cardinal.mk_le_of_injective hinj
    _ = Cardinal.sum (fun m : ULift.{u} ℕ => #(Ideal (MvPolynomial (Fin m.down) R))) :=
        Cardinal.mk_sigma _
    _ ≤ Cardinal.sum (fun _ : ULift.{u} ℕ => (2 : Cardinal.{u}) ^ max ℵ₀ #R) := by
        refine Cardinal.sum_le_sum _ _ (fun m => ?_)
        calc #(Ideal (MvPolynomial (Fin m.down) R))
            ≤ #(Set (MvPolynomial (Fin m.down) R)) :=
              Cardinal.mk_le_of_injective SetLike.coe_injective
          _ = 2 ^ #(MvPolynomial (Fin m.down) R) := Cardinal.mk_set
          _ ≤ 2 ^ max ℵ₀ #R :=
              Cardinal.power_le_power_left two_ne_zero
                (Cardinal.mk_mvPolynomial_fin_le R m.down)
    _ = #(ULift.{u} ℕ) * (2 : Cardinal.{u}) ^ max ℵ₀ #R := Cardinal.sum_const' _ _
    _ ≤ 2 ^ max ℵ₀ #R := by
        rw [Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0]
        exact (Cardinal.mul_le_max _ _).trans (by simp [hpow])

/-- There are at most `#B ^ #A` ring homomorphisms from `A` to `B`. -/
private theorem mk_commRingCat_hom_le (A B : CommRingCat.{u}) : #(A ⟶ B) ≤ #B ^ #A :=
  (Cardinal.mk_le_of_injective (f := fun φ x => φ.hom x)
    (fun _ _ h => CommRingCat.hom_ext (RingHom.ext (congrFun h)))).trans_eq
    (Cardinal.power_def _ _).symm

/-! ### The bounded index -/

/-- **The bounded index.** A presentation of a finitely generated `R`-algebra `A` and a lift of
the geometric point to `Spec A`, such that `Spec A ⟶ Spec R ⟶ S` is étale and carries the lift
to the geometric point. -/
def EtaleNeighborhoodBoundedIndex : Type u :=
  {d : Σ T : FGAlgCatSkeleton (R : Type u), (s.source ⟶ Spec (boundedPresRing T)) //
    Etale (boundedPresMap ι₀ d.1) ∧ d.2 ≫ boundedPresMap ι₀ d.1 = s.hom}

/-- The étale neighbourhood of the geometric point presented by a member of the bounded
index. -/
def etaleNeighborhoodBoundedStage (d : EtaleNeighborhoodBoundedIndex s ι₀) :
    (geometricPointFiber E S hS s).Elements :=
  have hc : E.Contains (Spec (boundedPresRing d.1.1)) :=
    (size_spec_boundedPresRing_le ι₀ d.1.1).trans_lt hS
  have := d.2.1
  (geometricPointFiber E S hS s).elementsMk
    ⟨Over.mk (ObjectProperty.homMk (boundedPresMap ι₀ d.1.1) :
      E.obj (Spec (boundedPresRing d.1.1)) hc ⟶ E.obj S hS),
    (inferInstanceAs (Etale (boundedPresMap ι₀ d.1.1)))⟩ ⟨d.1.2, d.2.2⟩

/-- The scheme underlying a stage of the bounded family is the spectrum of the presented
algebra. -/
theorem etaleNeighborhoodDiagram_obj_boundedStage (d : EtaleNeighborhoodBoundedIndex s ι₀) :
    (etaleNeighborhoodDiagram E S hS s).obj (etaleNeighborhoodBoundedStage E hS s ι₀ d) =
      Spec (boundedPresRing d.1.1) := rfl

/-- The stages of the bounded family are affine. -/
instance isAffine_etaleNeighborhoodBoundedStage (d : EtaleNeighborhoodBoundedIndex s ι₀) :
    IsAffine ((etaleNeighborhoodDiagram E S hS s).obj
      (etaleNeighborhoodBoundedStage E hS s ι₀ d)) :=
  inferInstanceAs (IsAffine (Spec (boundedPresRing d.1.1)))

/-- **The stages of the bounded family have size at most `size S`.** -/
theorem size_etaleNeighborhoodBoundedStage_le (d : EtaleNeighborhoodBoundedIndex s ι₀) :
    ((etaleNeighborhoodDiagram E S hS s).obj
      (etaleNeighborhoodBoundedStage E hS s ι₀ d)).size ≤ S.size :=
  size_spec_boundedPresRing_le ι₀ d.1.1

omit [IsOpenImmersion ι₀] in
/-- **The bounded index has at most `2 ^ max ℵ₀ #R * #k ^ max ℵ₀ #R` members**, `k` being the
field of the geometric point: there are at most `2 ^ max ℵ₀ #R` presentations, and a lift of the
geometric point to `Spec A` is a ring homomorphism `A ⟶ k`. -/
theorem mk_etaleNeighborhoodBoundedIndex_le :
    #(EtaleNeighborhoodBoundedIndex s ι₀) ≤
      2 ^ max ℵ₀ #R * #s.residueField ^ max ℵ₀ #R := by
  calc #(EtaleNeighborhoodBoundedIndex s ι₀)
      ≤ #(Σ T : FGAlgCatSkeleton (R : Type u), (s.source ⟶ Spec (boundedPresRing T))) :=
        Cardinal.mk_subtype_le _
    _ = Cardinal.sum (fun T : FGAlgCatSkeleton (R : Type u) =>
          #(s.source ⟶ Spec (boundedPresRing T))) := Cardinal.mk_sigma _
    _ ≤ Cardinal.sum (fun _ : FGAlgCatSkeleton (R : Type u) =>
          #s.residueField ^ max ℵ₀ #R) := by
        refine Cardinal.sum_le_sum _ _ (fun T => ?_)
        calc #(s.source ⟶ Spec (boundedPresRing T))
            = #(boundedPresRing T ⟶ CommRingCat.of s.residueField) :=
              Cardinal.mk_congr Spec.homEquiv
          _ ≤ #s.residueField ^ #(boundedPresRing T) := mk_commRingCat_hom_le _ _
          _ ≤ #s.residueField ^ max ℵ₀ #R :=
              Cardinal.power_le_power_left (Cardinal.mk_ne_zero _) (mk_boundedPresRing_le T)
    _ = #(FGAlgCatSkeleton (R : Type u)) * #s.residueField ^ max ℵ₀ #R :=
        Cardinal.sum_const' _ _
    _ ≤ 2 ^ max ℵ₀ #R * #s.residueField ^ max ℵ₀ #R :=
        mul_le_mul' (mk_fgAlgCatSkeleton_le' R) le_rfl

/-- **Every étale neighbourhood of the geometric point is refined by a member of the bounded
family.** Choose an affine open of the neighbourhood through which the point factors and which
maps into `Spec R`. The morphism from it to `Spec R` is étale, hence of finite type on rings, and
a presentation of its ring identifies it with a stage of the family. -/
theorem etaleNeighborhoodBoundedIndex_weaklyInitial (s₀ : s.source ⟶ Spec R)
    (hs₀ : s₀ ≫ ι₀ = s.hom) (U : (geometricPointFiber E S hS s).Elements) :
    ∃ d : EtaleNeighborhoodBoundedIndex s ι₀,
      Nonempty (etaleNeighborhoodBoundedStage E hS s ι₀ d ⟶ U) := by
  classical
  let f : (SmallEtale.toScheme E S hS).obj U.1 ⟶ S := E.inclusion.map U.1.obj.hom
  let p : s.source ⟶ (SmallEtale.toScheme E S hS).obj U.1 := U.2.1
  have hp : p ≫ f = s.hom := U.2.2
  -- an affine open of the neighbourhood through which the point factors, inside `f⁻¹(Spec R)`
  have hmem : p (default : s.source) ∈ f ⁻¹ᵁ ι₀.opensRange := by
    show f (p default) ∈ Set.range ι₀
    refine ⟨s₀ default, ?_⟩
    rw [← Scheme.Hom.comp_apply, hs₀, ← hp, Scheme.Hom.comp_apply]
  obtain ⟨R', j, hj, hjmem, hjsub⟩ := Scheme.exists_affine_mem_range_and_range_subset hmem
  have hpj : Set.range p ⊆ Set.range j := by
    rintro _ ⟨a, rfl⟩
    rwa [Subsingleton.elim a default]
  let p' : s.source ⟶ Spec R' := IsOpenImmersion.lift j p hpj
  have hp' : p' ≫ j = p := IsOpenImmersion.lift_fac j p hpj
  have hgsub : Set.range (j ≫ f) ⊆ Set.range ι₀ := by
    rintro _ ⟨a, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hjsub ⟨a, rfl⟩
  let g : Spec R' ⟶ Spec R := IsOpenImmersion.lift ι₀ (j ≫ f) hgsub
  have hg : g ≫ ι₀ = j ≫ f := IsOpenImmersion.lift_fac ι₀ (j ≫ f) hgsub
  have hjfEt : Etale (j ≫ f) := inferInstance
  have hgEt : Etale (g ≫ ι₀) := by rw [hg]; exact hjfEt
  have hgEt' : Etale g := Etale.of_comp g ι₀
  -- a presentation of the ring of the affine open over `R`
  let φ : R ⟶ R' := Spec.preimage g
  have hφ : Spec.map φ = g := Spec.map_preimage g
  have hft : φ.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  obtain ⟨T, e, hcompat⟩ := hft.exists_smallRepr
  -- the identification of the presented spectrum with the affine open, over `Spec R`
  let α : Spec (boundedPresRing T) ⟶ Spec R' := Spec.map (CommRingCat.ofHom e.symm.toRingHom)
  have hαiso : IsIso α :=
    (Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso e.symm).op).isIso_hom
  have hring : φ ≫ CommRingCat.ofHom e.symm.toRingHom =
      CommRingCat.ofHom (algebraMap (R : Type u) (T.eval.obj : Type u)) := by
    ext z
    show e.symm (φ.hom z) = _
    rw [hcompat]
    exact e.symm_apply_apply _
  have hαg : α ≫ g = Spec.map (CommRingCat.ofHom (algebraMap (R : Type u)
      (T.eval.obj : Type u))) := by
    rw [← hφ, ← Spec.map_comp, hring]
  have hmap : α ≫ j ≫ f = boundedPresMap ι₀ T := by
    rw [← hg, ← Category.assoc, hαg]
    rfl
  let q : s.source ⟶ Spec (boundedPresRing T) := p' ≫ inv α
  have hq : q ≫ α ≫ j = p := by
    simp only [q, Category.assoc, IsIso.inv_hom_id_assoc, hp']
  have hEt : Etale (boundedPresMap ι₀ T) := by
    rw [← hmap]
    infer_instance
  have hqS : q ≫ boundedPresMap ι₀ T = s.hom := by
    rw [← hmap, ← Category.assoc, ← Category.assoc, Category.assoc q, hq, hp]
  refine ⟨⟨⟨T, q⟩, hEt, hqS⟩, ⟨⟨ObjectProperty.homMk
    (Over.homMk (ObjectProperty.homMk (α ≫ j)) ?_), ?_⟩⟩⟩
  · apply ObjectProperty.hom_ext
    exact (Category.assoc _ _ _).trans hmap
  · apply Subtype.ext
    exact hq

/-! ### The bounded family as an index category -/

/-- The category induced on the bounded index by the étale neighbourhoods. -/
abbrev EtaleNeighborhoodBounded : Type u :=
  InducedCategory (geometricPointFiber E S hS s).Elements
    (etaleNeighborhoodBoundedStage E hS s ι₀)

/-- The inclusion of the bounded family into the étale neighbourhoods. -/
abbrev etaleNeighborhoodBoundedFunctor :
    EtaleNeighborhoodBounded E hS s ι₀ ⥤ (geometricPointFiber E S hS s).Elements :=
  inducedFunctor (etaleNeighborhoodBoundedStage E hS s ι₀)

/-- **The morphism types of the bounded family are at most `max ℵ₀ #R ^ max ℵ₀ #R`.** A morphism
of étale neighbourhoods is determined by its underlying morphism of schemes `Spec A ⟶ Spec A'`,
that is by a ring homomorphism `A' ⟶ A`. -/
theorem mk_hom_etaleNeighborhoodBounded_le (d d' : EtaleNeighborhoodBounded E hS s ι₀) :
    #(d ⟶ d') ≤ max ℵ₀ #R ^ max ℵ₀ #R := by
  have hinj : Function.Injective (fun f : d ⟶ d' =>
      (SmallEtale.toScheme E S hS).map ((etaleNeighborhoodBoundedFunctor E hS s ι₀).map f).hom) := by
    intro f g h
    apply InducedCategory.hom_ext
    apply Functor.Elements.hom_ext
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact h
  refine (Cardinal.mk_le_of_injective hinj).trans ?_
  calc #(Spec (boundedPresRing d.1.1) ⟶ Spec (boundedPresRing d'.1.1))
      = #(boundedPresRing d'.1.1 ⟶ boundedPresRing d.1.1) := Cardinal.mk_congr Spec.homEquiv
    _ ≤ #(boundedPresRing d.1.1) ^ #(boundedPresRing d'.1.1) := mk_commRingCat_hom_le _ _
    _ ≤ max ℵ₀ #R ^ max ℵ₀ #R := by
        refine (Cardinal.power_le_power_right (mk_boundedPresRing_le d.1.1)).trans ?_
        exact Cardinal.power_le_power_left (ne_of_gt (lt_of_lt_of_le Cardinal.aleph0_pos
          (le_max_left _ _))) (mk_boundedPresRing_le d'.1.1)

variable {s ι₀} (s₀ : s.source ⟶ Spec R) (hs₀ : s₀ ≫ ι₀ = s.hom)

include hs₀ in
/-- The bounded family is cofiltered. -/
theorem isCofiltered_etaleNeighborhoodBounded :
    IsCofiltered (EtaleNeighborhoodBounded E hS s ι₀) :=
  IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful
    (etaleNeighborhoodBoundedFunctor E hS s ι₀)
    (etaleNeighborhoodBoundedIndex_weaklyInitial E hS s ι₀ s₀ hs₀)

include hs₀ in
/-- The inclusion of the bounded family into the étale neighbourhoods is initial. -/
theorem initial_etaleNeighborhoodBoundedFunctor :
    (etaleNeighborhoodBoundedFunctor E hS s ι₀).Initial :=
  Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful
    (etaleNeighborhoodBoundedFunctor E hS s ι₀)
    (etaleNeighborhoodBoundedIndex_weaklyInitial E hS s ι₀ s₀ hs₀)

variable (s ι₀) in
/-- The restriction of the strict henselization cone to the bounded family. -/
def strictHenselizationBoundedCone :
    Cone (etaleNeighborhoodBoundedFunctor E hS s ι₀ ⋙ etaleNeighborhoodDiagram E S hS s) :=
  (strictHenselizationCone E S hS s).whisker (etaleNeighborhoodBoundedFunctor E hS s ι₀)

/-- **The strict henselization is the limit of the bounded family of affine étale
neighbourhoods.** -/
def strictHenselizationBoundedConeIsLimit :
    IsLimit (strictHenselizationBoundedCone E hS s ι₀) :=
  have := isCofiltered_etaleNeighborhoodBounded E hS s₀ hs₀
  have := initial_etaleNeighborhoodBoundedFunctor E hS s₀ hs₀
  (Functor.Initial.isLimitWhiskerEquiv (etaleNeighborhoodBoundedFunctor E hS s ι₀)
    (strictHenselizationCone E S hS s)).symm (strictHenselizationConeIsLimit E S hS s)

end AlgebraicGeometry

end
