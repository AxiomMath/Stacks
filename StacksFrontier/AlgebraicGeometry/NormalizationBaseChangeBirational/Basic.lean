module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Stability
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Reduction
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Variety.FindingAffineOpens.OpenImmersionCriterion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Generic points, birational morphisms and the reduction functor

Three pieces of elementary machinery about generic points of irreducible components, used in
the proof that the normalization of a scheme commutes with extension of the ground field up to
a universal homeomorphism (Tag 0C3N).

The first is the behaviour of generic points under open immersions, together with the
specialization characterization of a generic point that drives it: a point is the generic point
of an irreducible component exactly when nothing specializes to it but itself.

The second is the calculus of `AlgebraicGeometry.IsBirational` which that behaviour supports:
birational morphisms compose, isomorphisms are birational, birationality can be cancelled on
the right against a birational morphism whose generic-point preimage is exact, and
birationality restricts to an open of the target.

The third is the functoriality of the reduction `X ↦ X_red`. The reduction is the closed
subscheme cut out by the nilradical, and every morphism from a reduced scheme factors uniquely
through it (Tag 0356); applying that to `X_red ⟶ X ⟶ Y` produces `X_red ⟶ Y_red`, and
uniqueness of the factorization gives functoriality, preservation of isomorphisms and of open
immersions, and the range formula.

## Main results

* `AlgebraicGeometry.mem_genericPoints_iff_forall_specializes_eq` characterizes generic points
  of irreducible components by specialization, and
  `AlgebraicGeometry.eq_of_specializes_of_mem_genericPoints` is its forward half, which needs
  no sobriety.
* `AlgebraicGeometry.mem_genericPoints_target_of_isOpenImmersion` and
  `AlgebraicGeometry.mem_genericPoints_source_of_isOpenImmersion`: an open immersion carries
  generic points to generic points, and reflects them.
* `AlgebraicGeometry.mapsTo_genericPoints_of_surjective_comp` cancels a surjection on the left
  of a generic-point-preserving composite.
* `AlgebraicGeometry.isBirational_of_iso`,
  `AlgebraicGeometry.isBirational_of_comp_of_isBirational` and
  `AlgebraicGeometry.IsBirational.restrict` are the calculus of birational morphisms.
* `AlgebraicGeometry.Scheme.reductionMap'_comp_subschemeι` is the defining square of the
  reduction functor, `AlgebraicGeometry.Scheme.reductionMap'_comp` its functoriality,
  and `AlgebraicGeometry.Scheme.reductionMap'_range_of_isOpenImmersion` the range formula.

## Implementation notes

`AlgebraicGeometry.Scheme.reductionMap'` is chosen from the unique factorization of Tag 0356
rather than built by a construction, so every statement about it is proved from
`AlgebraicGeometry.Scheme.reductionMap'_comp_subschemeι` and the monicity of
`AlgebraicGeometry.Scheme.IdealSheafData.subschemeι`; nothing below unfolds the definition.

`AlgebraicGeometry.Scheme.reductionMap'` is the morphism of reductions read on
`X.nilradical.subscheme`; `AlgebraicGeometry.Scheme.reductionMap` is the same morphism read on
`AlgebraicGeometry.Scheme.reduction`. The two spellings are definitionally but not
syntactically equal, so the statements here are kept in the nilradical spelling.

`AlgebraicGeometry.mem_genericPoints_iff_forall_specializes_eq` and its corollaries are stated
for an arbitrary topological space, since neither direction uses anything about schemes; the
scheme instances `T0Space` and `QuasiSober` supply the hypotheses.

No `@[stacks 0C3N]` attribute is attached in this file. Both of that tag's unformalized assertions,
labelled "universal homeomorphism" and "separable extension", are statements about the
comparison morphism itself; what is proved here is machinery their proofs consume, so the tag is
not attached.

## References

* [Stacks Project, Tag 0C3N](https://stacks.math.columbia.edu/tag/0C3N)
* [Stacks Project, Tag 01RO](https://stacks.math.columbia.edu/tag/01RO)
* [Stacks Project, Tag 0356](https://stacks.math.columbia.edu/tag/0356)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

section GenericPoints

variable {α : Type*} [TopologicalSpace α]

/-- A point of an irreducible component's generic point specializes only to itself: the closure
of a specializing point is contained in the component, which is minimal. -/
public theorem eq_of_specializes_of_mem_genericPoints [T0Space α] {x y : α}
    (hy : y ∈ genericPoints α) (hxy : x ⤳ y) : x = y := by
  have hback : closure ({x} : Set α) ⊆ closure ({y} : Set α) :=
    (genericPoints.component ⟨y, hy⟩).2.2 isIrreducible_singleton.closure
      (specializes_iff_closure_subset.mp hxy)
  exact (hxy.antisymm (specializes_iff_closure_subset.mpr hback)).eq

/-- Every point is a specialization of the generic point of an irreducible component. -/
private theorem exists_mem_genericPoints_specializes [QuasiSober α] (a : α) :
    ∃ η ∈ genericPoints α, η ⤳ a :=
  let Z : irreducibleComponents α :=
    ⟨irreducibleComponent a, irreducibleComponent_mem_irreducibleComponents a⟩
  ⟨_, (genericPoints.ofComponent Z).2,
    (genericPoints.isGenericPoint_ofComponent Z).specializes mem_irreducibleComponent⟩

/-- A point is the generic point of an irreducible component exactly when the only point
specializing to it is itself. -/
public theorem mem_genericPoints_iff_forall_specializes_eq [T0Space α] [QuasiSober α] (a : α) :
    a ∈ genericPoints α ↔ ∀ b : α, b ⤳ a → b = a := by
  refine ⟨fun ha b hba ↦ eq_of_specializes_of_mem_genericPoints ha hba, fun h ↦ ?_⟩
  obtain ⟨η, hη, hηa⟩ := exists_mem_genericPoints_specializes a
  rwa [← h η hηa]

variable {A B : Scheme.{u}}

/-- An open immersion reflects generic points: the preimage of an irreducible component
containing the image of a point is an irreducible component containing that point. -/
public alias mem_genericPoints_source_of_isOpenImmersion :=
  AlgebraicGeometry.mem_genericPoints_of_isOpenImmersion_apply

/-- An open immersion carries generic points to generic points: a point specializing to the
image of a generic point lifts through the open immersion. -/
public theorem mem_genericPoints_target_of_isOpenImmersion (f : A ⟶ B) [IsOpenImmersion f]
    {x : A} (hx : x ∈ genericPoints A) : f x ∈ genericPoints B := by
  refine (mem_genericPoints_iff_forall_specializes_eq _).2 fun y hy ↦ ?_
  obtain ⟨x', hx', rfl⟩ := f.isOpenEmbedding.generalizingMap hy
  exact congrArg f ((mem_genericPoints_iff_forall_specializes_eq x).1 hx x' hx')

/-- An isomorphism of schemes bijects the generic points of irreducible components. -/
public theorem bijOn_genericPoints_of_iso (e : A ≅ B) :
    Set.BijOn e.hom (genericPoints A) (genericPoints B) :=
  ⟨fun _ hx ↦ mem_genericPoints_target_of_isOpenImmersion e.hom hx,
    fun _ _ _ _ hxy ↦ e.hom.homeomorph.injective hxy,
    fun y hy ↦ ⟨e.inv y, mem_genericPoints_target_of_isOpenImmersion e.inv hy, by simp⟩⟩

/-- A surjection can be cancelled on the left of a generic-point-preserving composite: every
point of the middle scheme that is generic is hit by a generic point of the source. -/
public theorem mapsTo_genericPoints_of_surjective_comp {C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    [Surjective f] (h : Set.MapsTo (f ≫ g) (genericPoints A) (genericPoints C)) :
    Set.MapsTo g (genericPoints B) (genericPoints C) := by
  intro b hb
  obtain ⟨a, ha⟩ := f.surjective b
  obtain ⟨η, hη, hηa⟩ := exists_mem_genericPoints_specializes a
  have heq : f η = b :=
    eq_of_specializes_of_mem_genericPoints hb (by simpa only [ha] using hηa.map f.continuous)
  simpa only [Scheme.Hom.comp_apply, heq] using h hη

/-- A generic point of an irreducible component of a Noetherian space lies in every dense
open: a dense open meets an open subset of that component, and the generic point specializes
into it. -/
public theorem mem_of_mem_genericPoints_of_dense {T : Type u} [TopologicalSpace T]
    [NoetherianSpace T] (U : Opens T) (hU : Dense (U : Set T)) {x : T}
    (hx : x ∈ genericPoints T) : x ∈ U := by
  obtain ⟨V, hV, hVne, hVC⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hx
  obtain ⟨y, hyV, hyU⟩ := (dense_iff_inter_open.mp hU) V hV hVne
  exact ((genericPoints.isGenericPoint ⟨x, hx⟩).specializes (hVC hyV)).mem_open U.isOpen hyU

end GenericPoints

section Birational

variable {A B C : Scheme.{u}}

/-- An isomorphism of schemes is birational. -/
public theorem isBirational_of_iso (e : A ≅ B) : IsBirational e.hom :=
  ⟨bijOn_genericPoints_of_iso e,
    fun x _ ↦ ((isIso_iff_isIso_stalkMap e.hom).mp inferInstance).2 x⟩

/-- Birationality cancels on the right against a birational morphism whose preimage of the
generic points is exactly the generic points. -/
public theorem isBirational_of_comp_of_isBirational (f : A ⟶ B) (g : B ⟶ C)
    (hfg : IsBirational (f ≫ g)) (hg : IsBirational g)
    (hpre : g ⁻¹' genericPoints C = genericPoints B) : IsBirational f := by
  have hmap : Set.MapsTo f (genericPoints A) (genericPoints B) := fun x hx ↦
    (Set.ext_iff.mp hpre (f x)).mp (hfg.bijOn.mapsTo hx)
  refine ⟨⟨hmap, fun x hx y hy hxy ↦ hfg.bijOn.injOn hx hy
      (by simpa only [Scheme.Hom.comp_apply] using congrArg g hxy), fun y hy ↦ ?_⟩,
    fun x hx ↦ ?_⟩
  · obtain ⟨x, hx, hxy⟩ := hfg.bijOn.surjOn (hg.bijOn.mapsTo hy)
    exact ⟨x, hx, hg.bijOn.injOn (hmap hx) hy
      (by simpa only [Scheme.Hom.comp_apply] using hxy)⟩
  · have : IsIso (g.stalkMap (f x)) := hg.2 (f x) (hmap hx)
    have : IsIso (g.stalkMap (f x) ≫ f.stalkMap x) := by
      rw [← Scheme.Hom.stalkMap_comp]
      exact hfg.2 x hx
    exact IsIso.of_isIso_comp_left (g.stalkMap (f x)) (f.stalkMap x)

/-- Birationality is inherited by the restriction to an open of the target: the open immersions
on both sides preserve and reflect generic points, and the stalk maps of the restriction are
the stalk maps of the morphism. -/
public theorem IsBirational.restrict {f : A ⟶ B} (hf : IsBirational f) (U : B.Opens) :
    IsBirational (f ∣_ U) := by
  have hmap (z : (f ⁻¹ᵁ U).toScheme) : U.ι ((f ∣_ U) z) = f ((f ⁻¹ᵁ U).ι z) :=
    congrArg (fun g : (f ⁻¹ᵁ U).toScheme ⟶ B ↦ g z) (morphismRestrict_ι f U)
  refine ⟨Set.BijOn.mk ?_ ?_ ?_, ?_⟩
  · intro z hz
    apply mem_genericPoints_source_of_isOpenImmersion U.ι
    rw [hmap z]
    exact hf.1.mapsTo (mem_genericPoints_target_of_isOpenImmersion (f ⁻¹ᵁ U).ι hz)
  · intro z hz z' hz' h
    apply (f ⁻¹ᵁ U).ι.isOpenEmbedding.injective
    apply hf.1.injOn
      (mem_genericPoints_target_of_isOpenImmersion (f ⁻¹ᵁ U).ι hz)
      (mem_genericPoints_target_of_isOpenImmersion (f ⁻¹ᵁ U).ι hz')
    simpa only [← hmap z, ← hmap z'] using congrArg U.ι h
  · intro y hy
    obtain ⟨z, hz, hzy⟩ := hf.1.surjOn (mem_genericPoints_target_of_isOpenImmersion U.ι hy)
    refine ⟨⟨z, show f z ∈ U from hzy ▸ y.2⟩,
      mem_genericPoints_source_of_isOpenImmersion (f ⁻¹ᵁ U).ι hz, ?_⟩
    exact U.ι.isOpenEmbedding.injective ((hmap _).trans hzy)
  · intro z hz
    exact (MorphismProperty.arrow_mk_iso_iff (P := .isomorphisms _)
      (morphismRestrictStalkMap f U z)).mpr
      (hf.2 _ (mem_genericPoints_target_of_isOpenImmersion (f ⁻¹ᵁ U).ι hz))

end Birational

namespace Scheme

section Reduction

variable {A B C : Scheme.{u}}

/-- The closed subscheme cut out by the nilradical is reduced, as a local instance so that
the factorization through it applies. -/
@[ega "I 5.1.2" "partial"]
local instance isReduced_nilradical_subscheme' (X : Scheme.{u}) :
    IsReduced X.nilradical.subscheme :=
  AlgebraicGeometry.isReduced_nilradical_subscheme X

/-- The morphism of reductions induced by a morphism of schemes, read on the closed subscheme
cut out by the nilradical: the composite `A_red ⟶ A ⟶ B` starts at a reduced scheme, so it
factors uniquely through `B_red`.

This is the same morphism as `AlgebraicGeometry.Scheme.reductionMap`, which states it on
`AlgebraicGeometry.Scheme.reduction`; that spelling is definitionally this one but not
syntactically, so the two developments are kept apart and the statements below are those in
the nilradical spelling. -/
@[ega "I 5.1.5"]
public noncomputable def reductionMap' (f : A ⟶ B) :
    A.nilradical.subscheme ⟶ B.nilradical.subscheme :=
  Classical.choose (Scheme.existsUnique_lift_nilradical_subschemeι
    (A.nilradical.subschemeι ≫ f))

/-- The defining square of the reduction map. -/
@[reassoc]
public theorem reductionMap'_comp_subschemeι (f : A ⟶ B) :
    reductionMap' f ≫ B.nilradical.subschemeι = A.nilradical.subschemeι ≫ f :=
  (Classical.choose_spec (Scheme.existsUnique_lift_nilradical_subschemeι
    (A.nilradical.subschemeι ≫ f))).1

/-- The reduction map is functorial. -/
public theorem reductionMap'_comp (f : A ⟶ B) (g : B ⟶ C) :
    reductionMap' (f ≫ g) = reductionMap' f ≫ reductionMap' g := by
  apply (cancel_mono C.nilradical.subschemeι).mp
  simp [reductionMap'_comp_subschemeι, reductionMap'_comp_subschemeι_assoc]

/-- The reduction map of an isomorphism is an isomorphism, with inverse the reduction map of
the inverse. -/
public instance reductionMap'_isIso (f : A ⟶ B) [IsIso f] : IsIso (reductionMap' f) := by
  refine ⟨⟨reductionMap' (inv f), ?_, ?_⟩⟩
  · apply (cancel_mono A.nilradical.subschemeι).mp
    simp [reductionMap'_comp_subschemeι, reductionMap'_comp_subschemeι_assoc]
  · apply (cancel_mono B.nilradical.subschemeι).mp
    simp [reductionMap'_comp_subschemeι, reductionMap'_comp_subschemeι_assoc]

/-- The reduction map of a surjective closed immersion is an isomorphism: the kernel ideal is
contained in the nilradical, so the reduction of the target lifts along the immersion, and that
lift factors through the reduction of the source. -/
public theorem reductionMap'_isIso_of_isClosedImmersion_of_surjective (f : A ⟶ B)
    [IsClosedImmersion f] [Surjective f] : IsIso (reductionMap' f) := by
  have hsup : f.ker.support = ⊤ := by
    apply Closeds.ext
    rw [Scheme.Hom.support_ker]
    simp [Set.range_eq_univ.mpr f.surjective]
  have hker : f.ker ≤ B.nilradical := by
    simpa only [Scheme.IdealSheafData.vanishingIdeal_top] using
      (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal
        (I := f.ker) (Z := ⊤)).mp (by simp [hsup])
  let s : B.nilradical.subscheme ⟶ A :=
    IsClosedImmersion.lift f B.nilradical.subschemeι (by
      simpa only [Scheme.IdealSheafData.ker_subschemeι] using hker)
  have hs : s ≫ f = B.nilradical.subschemeι :=
    IsClosedImmersion.lift_fac f B.nilradical.subschemeι _
  obtain ⟨t, ht, -⟩ := Scheme.existsUnique_lift_nilradical_subschemeι s
  refine ⟨⟨t, ?_, ?_⟩⟩
  · apply (cancel_mono A.nilradical.subschemeι).mp
    apply (cancel_mono f).mp
    calc ((reductionMap' f ≫ t) ≫ A.nilradical.subschemeι) ≫ f
        = reductionMap' f ≫ s ≫ f := by simp only [Category.assoc, ht]
      _ = reductionMap' f ≫ B.nilradical.subschemeι := by rw [hs]
      _ = A.nilradical.subschemeι ≫ f := reductionMap'_comp_subschemeι f
      _ = (𝟙 _ ≫ A.nilradical.subschemeι) ≫ f := by simp
  · apply (cancel_mono B.nilradical.subschemeι).mp
    calc (t ≫ reductionMap' f) ≫ B.nilradical.subschemeι
        = t ≫ A.nilradical.subschemeι ≫ f := by
          rw [Category.assoc, reductionMap'_comp_subschemeι]
      _ = s ≫ f := by rw [← Category.assoc, ht]
      _ = B.nilradical.subschemeι := hs
      _ = 𝟙 _ ≫ B.nilradical.subschemeι := by simp

/-- Transport of the canonical closed immersion along an equality of ideal-sheaf data. -/
public theorem subschemeι_eqToHom {I J : A.IdealSheafData} (h : I = J) :
    eqToHom (congrArg Scheme.IdealSheafData.subscheme h) ≫ J.subschemeι = I.subschemeι := by
  subst J
  simp

/-- The reduction of an open subscheme is the corresponding open subscheme of the reduction:
the pullback of the reduction of the ambient scheme along an open immersion is reduced, and a
reduced closed subscheme structure on a closed subset is its vanishing-ideal structure
(Tag 01J3), which identifies it with the reduction of the source. -/
@[ega "I 5.1.6"]
public theorem exists_isOpenImmersion_reduction {U A : Scheme.{u}} (j : U ⟶ A)
    [IsOpenImmersion j] :
    ∃ jr : U.nilradical.subscheme ⟶ A.nilradical.subscheme, IsOpenImmersion jr ∧
      jr ≫ A.nilradical.subschemeι = U.nilradical.subschemeι ≫ j := by
  let I := A.nilradical.comap j
  let q := (A.nilradical.comapIso j).hom ≫ pullback.snd j A.nilradical.subschemeι
  have : IsOpenImmersion q := inferInstance
  have : IsReduced I.subscheme := isReduced_of_isOpenImmersion q
  have heq : I = U.nilradical := by
    rw [← Scheme.IdealSheafData.vanishingIdeal_top]
    apply Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme I ⊤
    simp only [I, Scheme.IdealSheafData.support_comap, Scheme.support_nilradical]
    ext x
    rfl
  refine ⟨eqToHom (congrArg Scheme.IdealSheafData.subscheme heq.symm) ≫ q, inferInstance, ?_⟩
  have hq : q ≫ A.nilradical.subschemeι = I.subschemeι ≫ j := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc,
      Scheme.IdealSheafData.comapIso_hom_fst]
  rw [Category.assoc, hq, ← Category.assoc, subschemeι_eqToHom heq.symm]

/-- The reduction map of an open immersion is an open immersion. -/
@[ega "I 5.1.6"]
public instance reductionMap'_isOpenImmersion {U A : Scheme.{u}} (j : U ⟶ A)
    [IsOpenImmersion j] : IsOpenImmersion (reductionMap' j) := by
  obtain ⟨jr, hjr, heq⟩ := exists_isOpenImmersion_reduction j
  have h : jr = reductionMap' j := by
    apply (cancel_mono A.nilradical.subschemeι).mp
    rw [heq, reductionMap'_comp_subschemeι]
  exact h ▸ hjr

/-- The range of the reduction map of an open immersion is the preimage of its range: the
canonical morphisms from the reductions are homeomorphisms. -/
public theorem reductionMap'_range_of_isOpenImmersion {U A : Scheme.{u}} (j : U ⟶ A)
    [IsOpenImmersion j] :
    Set.range (reductionMap' j) = A.nilradical.subschemeι ⁻¹' Set.range j := by
  have hr (X : Scheme.{u}) : IsHomeomorph X.nilradical.subschemeι :=
    (inferInstance : UniversalHomeomorphism X.nilradical.subschemeι).universally_isHomeomorph
      _ _ _ IsPullback.of_id_snd
  ext a
  refine ⟨?_, ?_⟩
  · rintro ⟨v, rfl⟩
    exact ⟨U.nilradical.subschemeι v, by
      simp only [← Scheme.Hom.comp_apply, reductionMap'_comp_subschemeι]⟩
  · rintro ⟨v, hv⟩
    obtain ⟨v', rfl⟩ := (hr U).surjective v
    refine ⟨v', (hr A).injective ?_⟩
    simpa only [← Scheme.Hom.comp_apply, reductionMap'_comp_subschemeι] using hv

end Reduction

end Scheme

end AlgebraicGeometry

end
