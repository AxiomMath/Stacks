module

public import StacksFrontier.RingTheory.Cech.PresheafComplex
public import StacksFrontier.RingTheory.Cech.Reindex

/-!
# The summands of the presheaf of extended alternating Čech complexes

`Stacks.CechPresheaf.cechPresheafTerm R f hf p` is the degree-`p` term of the presheaf of
extended alternating Čech complexes of a family of sections: over an object `V` it is the direct
sum, over the `p`-element subsets `S ⊆ {1, …, r}`, of the localizations `R(V)_{f_S}`. This file
supplies those localizations as presheaves of modules in their own right, the inclusions and
projections exhibiting the degree-`p` term as their biproduct, and the component formula for the
differential.

Downstream, [Stacks, Tag 099E] needs the same complex written with *products* of the individual
localizations instead of direct sums, because the extended alternating Čech complex of sheaves of
modules on a ringed site is built that way. Everything a comparison with the product-indexed
complex needs is collected here, and nothing about products is, which is why this file can sit
beside `PresheafComplex.lean` with a small import closure.

## Main definitions

* `Stacks.CechPresheaf.cechLocAddPresheaf`: a single localization `V ↦ R(V)_{f_S}` as a presheaf
  of abelian groups.
* `Stacks.CechPresheaf.cechLocPresheaf`: **the same localization as a presheaf of `R`-modules**,
  one summand of the degree-`p` term.
* `Stacks.CechPresheaf.cechLocTransition` and `Stacks.CechPresheaf.cechLocFunctor`: the
  transition map `R(-)_{f_S} ⟶ R(-)_{f_T}` for `S ⊆ T`, and the system of all of them on the
  poset of subsets.
* `Stacks.CechPresheaf.cechLocInclusion` and `Stacks.CechPresheaf.cechLocProjection`: **the
  inclusion of a summand into the degree-`p` term and the projection onto it.**
* `Stacks.CechPresheaf.cechLocAugmentationEmpty`: the augmentation of the summand indexed by the
  empty set onto `R`.

## Main results

* `Stacks.CechPresheaf.cechLocInclusion_comp_cechLocProjection_self`,
  `Stacks.CechPresheaf.cechLocInclusion_comp_cechLocProjection_of_ne` and
  `Stacks.CechPresheaf.sum_cechLocProjection_comp_cechLocInclusion`: **the degree-`p` term is the
  biproduct of its summands** — the inclusions and projections are mutually orthogonal and their
  idempotents sum to the identity.
* `Stacks.CechPresheaf.cechPresheafDifferential_comp_cechLocProjection`: **the component formula
  for the differential** — its `T`-component is the alternating sum, over the elements `k` of
  `T`, of the transition maps out of the summands indexed by `T ∖ k`.
* `Stacks.CechPresheaf.cechPresheafAugmentationZero_eq`: the augmentation in degree zero is the
  projection onto the single summand of the degree-zero term followed by that summand's
  augmentation.

## Implementation notes

The presheaf laws of a single summand are the laws of `Stacks.CechSemilinear.locMap` exactly as
those of the degree-`p` term are the laws of `Stacks.CechSemilinear.termMap`, so each of them has
to be preceded by `Stacks.CechSemilinear.locMap_congr`, proved here for the same reason
`Stacks.CechSemilinear.termMap_congr` exists: the comparison attached to an arrow is the one for
`(R.map a).hom`, and the functor laws of `R` identify `R.map (a ≫ b)` with `R.map a ≫ R.map b`
only propositionally.

The ring-level content of the component formula is `Cech.cechD_component`; the work here is only
to pass from that identity of elements to an identity of maps of presheaves of modules. The
passage is `PresheafOfModules.hom_ext` to a single object, then `ModuleCat.hom_ext` and
`LinearMap.ext` to a single element; the right-hand side's `Finset` sum of maps is evaluated on
the way by `Stacks.CechPresheaf.app_sum`, which is additivity of
`PresheafOfModules.evaluation`, together with `PresheafOfModules.zsmul_app`,
`ModuleCat.hom_sum` and `LinearMap.sum_apply`.

## References

* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
* [Stacks Project, Tag 099E](https://stacks.math.columbia.edu/tag/099E)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v w

namespace Stacks.CechSemilinear

/-- **The comparison of two localizations depends on the ring map only through its value.** This
is the analogue for a single localization of `Stacks.CechSemilinear.termMap_congr`. -/
theorem locMap_congr {A B : Type*} [CommRing A] [CommRing B] {φ ψ : A →+* B} (e : φ = ψ)
    (S : Submonoid A) (T : Submonoid B) (hφ : S ≤ T.comap φ) (hψ : S ≤ T.comap ψ)
    (x : LocalizedModule S A) : locMap φ S T hφ x = locMap ψ S T hψ x := by
  subst e
  rfl

end Stacks.CechSemilinear

namespace Stacks.CechPresheaf

variable {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ CommRingCat.{w}) {r : ℕ}
  (f : ∀ V : Cᵒᵖ, Fin r → R.obj V)
  (hf : ∀ {V W : Cᵒᵖ} (a : V ⟶ W) (i : Fin r), (R.map a).hom (f V i) = f W i)

/-- The sections of a finite sum of maps of presheaves of modules are the sum of the sections:
evaluation at an object is an additive functor. -/
theorem app_sum {M N : PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat)} {ι : Type*}
    (φ : ι → (M ⟶ N)) (s : Finset ι) (V : Cᵒᵖ) :
    (∑ i ∈ s, φ i).app V = ∑ i ∈ s, (φ i).app V :=
  (PresheafOfModules.evaluation (R ⋙ forget₂ CommRingCat RingCat) V).map_sum φ s

/-- The sections of a finite sum of maps of presheaves of modules, evaluated at an element. -/
private theorem app_sum_apply {M N : PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat)}
    {ι : Type*} (φ : ι → (M ⟶ N)) (s : Finset ι) (V : Cᵒᵖ) (x : M.obj V) :
    ((∑ i ∈ s, φ i).app V).hom x = ∑ i ∈ s, ((φ i).app V).hom x := by
  rw [app_sum, ModuleCat.hom_sum, LinearMap.sum_apply]

/-- Maps of presheaves of modules are equal when they agree on every element of every section. -/
private theorem hom_ext_apply {R' : Cᵒᵖ ⥤ RingCat.{w}} {M N : PresheafOfModules.{w} R'}
    {φ ψ : M ⟶ N} (h : ∀ V x, (φ.app V).hom x = (ψ.app V).hom x) : φ = ψ :=
  PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext (LinearMap.ext (h V))

/-- One summand of the degree-`p` Čech term, as a presheaf of abelian groups: over `V` it is the
localization `R(V)_{f_S}`, and restriction is the semilinear change of rings
`Stacks.CechSemilinear.locMap`. -/
def cechLocAddPresheaf (S : Finset (Fin r)) : Cᵒᵖ ⥤ AddCommGrpCat.{w} where
  obj V := AddCommGrpCat.of (Cech.cechMod (f V) (R.obj V) S)
  map {V W} a := AddCommGrpCat.ofHom
    (CechSemilinear.locMap (R.map a).hom _ _
      (CechSemilinear.cechSub_le_comap (R.map a).hom (f V) (f W) (hf a) S)).toAddMonoidHom
  map_id V := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_)
    change CechSemilinear.locMap (R.map (𝟙 V)).hom _ _
      (CechSemilinear.cechSub_le_comap (R.map (𝟙 V)).hom (f V) (f V) (hf (𝟙 V)) S) x = x
    exact (CechSemilinear.locMap_congr (congrArg CommRingCat.Hom.hom (R.map_id V))
      (Cech.cechSub (f V) S) (Cech.cechSub (f V) S)
      (CechSemilinear.cechSub_le_comap (R.map (𝟙 V)).hom (f V) (f V) (hf (𝟙 V)) S)
      (CechSemilinear.cechSub_le_comap (RingHom.id (R.obj V)) (f V) (f V) (fun _ => rfl) S)
      x).trans
      (CechSemilinear.locMap_id (Cech.cechSub (f V) S) _ x)
  map_comp {V W Z} a b := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_)
    change CechSemilinear.locMap (R.map (a ≫ b)).hom _ _
        (CechSemilinear.cechSub_le_comap (R.map (a ≫ b)).hom (f V) (f Z) (hf (a ≫ b)) S) x =
      CechSemilinear.locMap (R.map b).hom _ _
        (CechSemilinear.cechSub_le_comap (R.map b).hom (f W) (f Z) (hf b) S)
        (CechSemilinear.locMap (R.map a).hom _ _
          (CechSemilinear.cechSub_le_comap (R.map a).hom (f V) (f W) (hf a) S) x)
    have hcomp (i : Fin r) : ((R.map b).hom.comp (R.map a).hom) (f V i) = f Z i :=
      (congrArg (R.map b).hom (hf a i)).trans (hf b i)
    exact (CechSemilinear.locMap_congr (congrArg CommRingCat.Hom.hom (R.map_comp a b))
        (Cech.cechSub (f V) S) (Cech.cechSub (f Z) S)
        (CechSemilinear.cechSub_le_comap (R.map (a ≫ b)).hom (f V) (f Z) (hf (a ≫ b)) S)
        (CechSemilinear.cechSub_le_comap _ (f V) (f Z) hcomp S) x).trans
      (CechSemilinear.locMap_comp (R.map a).hom (R.map b).hom _ _ _
        (CechSemilinear.cechSub_le_comap (R.map a).hom (f V) (f W) (hf a) S)
        (CechSemilinear.cechSub_le_comap (R.map b).hom (f W) (f Z) (hf b) S)
        (CechSemilinear.cechSub_le_comap _ (f V) (f Z) hcomp S) x).symm

/-- **One summand of the degree-`p` Čech term, as a presheaf of `R`-modules.** The semilinear
change of rings is exactly the semilinearity `PresheafOfModules.ofPresheaf` asks for. -/
def cechLocPresheaf (S : Finset (Fin r)) :
    PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat) := by
  letI : ∀ V, Module ((R ⋙ forget₂ CommRingCat RingCat).obj V)
      ((cechLocAddPresheaf R f hf S).obj V) := fun V =>
    inferInstanceAs (Module (R.obj V) (Cech.cechMod (f V) (R.obj V) S))
  exact PresheafOfModules.ofPresheaf (cechLocAddPresheaf R f hf S)
    (fun {_V _W} a c x =>
      (CechSemilinear.locMap (R.map a).hom _ _
        (CechSemilinear.cechSub_le_comap (R.map a).hom (f _) (f _) (hf a) S)).map_smulₛₗ c x)

/-- The transition map `R(-)_{f_S} ⟶ R(-)_{f_T}` of two summands, for `S ⊆ T`: over each object
it is the transition map `Cech.cechι` of the Čech complex of the ring of sections. -/
def cechLocTransition {S T : Finset (Fin r)} (hST : S ⊆ T) :
    cechLocPresheaf R f hf S ⟶ cechLocPresheaf R f hf T where
  app V := by
    change ModuleCat.of (R.obj V) (Cech.cechMod (f V) (R.obj V) S) ⟶
      ModuleCat.of (R.obj V) (Cech.cechMod (f V) (R.obj V) T)
    exact ModuleCat.ofHom (Cech.cechι (f V) (R.obj V) hST)
  naturality {V W} a := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    exact (CechSemilinear.locMap_cechι (R.map a).hom (f V) (f W) (hf a) hST x).symm

/-- The transition map of a summand to itself is the identity. -/
theorem cechLocTransition_refl (S : Finset (Fin r)) :
    cechLocTransition R f hf (Finset.Subset.refl S) = 𝟙 _ := by
  refine hom_ext_apply fun V x => ?_
  exact congr($(Cech.cechι_rfl (f V) (R.obj V) S) x)

/-- The transition maps compose. -/
theorem cechLocTransition_comp {S T W : Finset (Fin r)} (hST : S ⊆ T) (hTW : T ⊆ W)
    (hSW : S ⊆ W) :
    cechLocTransition R f hf hST ≫ cechLocTransition R f hf hTW =
      cechLocTransition R f hf hSW := by
  refine hom_ext_apply fun V x => ?_
  exact Cech.cechι_cechι (f V) (R.obj V) hST hTW x

/-- **The system of all the summands**, as a functor on the poset of subsets of `{1, …, r}` with
values in presheaves of `R`-modules. -/
def cechLocFunctor :
    Finset (Fin r) ⥤ PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat) where
  obj S := cechLocPresheaf R f hf S
  map h := cechLocTransition R f hf (leOfHom h)
  map_id S := cechLocTransition_refl R f hf S
  map_comp h h' := (cechLocTransition_comp R f hf (leOfHom h) (leOfHom h') _).symm

/-- The value of `cechLocFunctor` at `S` is the summand `cechLocPresheaf R f hf S`. -/
@[simp]
theorem cechLocFunctor_obj (S : Finset (Fin r)) :
    (cechLocFunctor R f hf).obj S = cechLocPresheaf R f hf S :=
  rfl

/-- The image under `cechLocFunctor` of `S ⟶ T` is the transition map `cechLocTransition`. -/
@[simp]
theorem cechLocFunctor_map {S T : Finset (Fin r)} (h : S ⟶ T) :
    (cechLocFunctor R f hf).map h = cechLocTransition R f hf (leOfHom h) :=
  rfl

/-- **The inclusion of a summand into the degree-`p` term**: over each object it is the
inclusion of the summand indexed by `S` into the direct sum. -/
def cechLocInclusion (p : ℕ) (S : ExtendedAlternatingCech.Idx r p) :
    cechLocPresheaf R f hf S.1 ⟶ cechPresheafTerm R f hf p where
  app V := by
    change ModuleCat.of (R.obj V) (Cech.cechMod (f V) (R.obj V) S.1) ⟶
      ModuleCat.of (R.obj V) (Cech.cechTerm (f V) (R.obj V) p)
    exact ModuleCat.ofHom (DirectSum.lof (R.obj V) (ExtendedAlternatingCech.Idx r p)
      (fun s => Cech.cechMod (f V) (R.obj V) s.1) S)
  naturality {V W} a := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    exact (CechSemilinear.termMap_lof (R.map a).hom (f V) (f W) (hf a) p S x).symm

/-- **The projection of the degree-`p` term onto a summand**: over each object it is the
component of the direct sum indexed by `S`. -/
def cechLocProjection (p : ℕ) (S : ExtendedAlternatingCech.Idx r p) :
    cechPresheafTerm R f hf p ⟶ cechLocPresheaf R f hf S.1 where
  app V := by
    change ModuleCat.of (R.obj V) (Cech.cechTerm (f V) (R.obj V) p) ⟶
      ModuleCat.of (R.obj V) (Cech.cechMod (f V) (R.obj V) S.1)
    exact ModuleCat.ofHom (DirectSum.component (R.obj V) (ExtendedAlternatingCech.Idx r p)
      (fun s => Cech.cechMod (f V) (R.obj V) s.1) S)
  naturality {V W} a := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    exact CechSemilinear.termMap_apply (R.map a).hom (f V) (f W) (hf a) p x S

/-- **The projection onto a summand undoes its inclusion.** -/
@[simp]
theorem cechLocInclusion_comp_cechLocProjection_self (p : ℕ)
    (S : ExtendedAlternatingCech.Idx r p) :
    cechLocInclusion R f hf p S ≫ cechLocProjection R f hf p S = 𝟙 _ := by
  refine hom_ext_apply fun V x => ?_
  exact DirectSum.component.lof_self (R.obj V)
    (M := fun s : ExtendedAlternatingCech.Idx r p => Cech.cechMod (f V) (R.obj V) s.1) S x

/-- **Distinct summands are orthogonal.** -/
theorem cechLocInclusion_comp_cechLocProjection_of_ne (p : ℕ)
    {S T : ExtendedAlternatingCech.Idx r p} (h : S ≠ T) :
    cechLocInclusion R f hf p S ≫ cechLocProjection R f hf p T = 0 := by
  refine hom_ext_apply fun V x => ?_
  exact (DirectSum.component.of (R.obj V)
    (M := fun s : ExtendedAlternatingCech.Idx r p => Cech.cechMod (f V) (R.obj V) s.1) T S
    x).trans (dite_eq_right h)

/-- **The degree-`p` term is the biproduct of its summands**: the idempotents cut out by the
projections and the inclusions sum to the identity. -/
theorem sum_cechLocProjection_comp_cechLocInclusion (p : ℕ) :
    ∑ S : ExtendedAlternatingCech.Idx r p,
        cechLocProjection R f hf p S ≫ cechLocInclusion R f hf p S =
      𝟙 (cechPresheafTerm R f hf p) := by
  refine hom_ext_apply fun V x => ?_
  rw [app_sum_apply]
  exact DirectSum.sum_univ_of x

/-- **The component formula for the differential of the presheaf of Čech complexes.** Its
component at a `(p+1)`-element index set `T` is the alternating sum, over the elements `k` of
`T`, of the transition maps out of the summands indexed by `T ∖ k`.

The ring-level content is `Cech.cechD_component`. -/
theorem cechPresheafDifferential_comp_cechLocProjection (p : ℕ)
    (T : ExtendedAlternatingCech.Idx r (p + 1)) :
    cechPresheafDifferential R f hf p ≫ cechLocProjection R f hf (p + 1) T =
      ∑ k : T.1, Cech.cechSign T.1 k.1 •
        (cechLocProjection R f hf p (Cech.idxErase T k) ≫
          cechLocTransition R f hf (Finset.erase_subset k.1 T.1)) := by
  refine hom_ext_apply fun V x => ?_
  simp only [app_sum_apply, PresheafOfModules.zsmul_app]
  exact Cech.cechD_component (f V) (R.obj V) p x T

/-- The augmentation of the summand indexed by the empty set onto `R`: inverting the empty
subproduct `f_∅ = 1` changes nothing, so that summand is `R` itself. -/
def cechLocAugmentationEmpty :
    cechLocPresheaf R f hf (∅ : Finset (Fin r)) ⟶
      PresheafOfModules.unit (R ⋙ forget₂ CommRingCat RingCat) :=
  cechLocInclusion R f hf 0 ⟨∅, Finset.card_empty⟩ ≫ cechPresheafAugmentationZero R f hf

/-- **The augmentation in degree zero is the projection onto the single summand of the
degree-zero term followed by that summand's augmentation.** The only index set of cardinality
zero is the empty one, so the biproduct decomposition of the degree-zero term has a single
term. -/
theorem cechPresheafAugmentationZero_eq :
    cechPresheafAugmentationZero R f hf =
      cechLocProjection R f hf 0 ⟨∅, Finset.card_empty⟩ ≫ cechLocAugmentationEmpty R f hf := by
  have h : cechLocProjection R f hf 0 ⟨∅, Finset.card_empty⟩ ≫
      cechLocInclusion R f hf 0 ⟨∅, Finset.card_empty⟩ = 𝟙 _ := by
    have h0 := sum_cechLocProjection_comp_cechLocInclusion R f hf 0
    rwa [Finset.univ_unique, Finset.sum_singleton] at h0
  rw [cechLocAugmentationEmpty, ← Category.assoc, h, Category.id_comp]

end Stacks.CechPresheaf

end
