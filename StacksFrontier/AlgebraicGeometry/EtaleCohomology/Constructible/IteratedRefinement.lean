module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.NoetherianStratification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.SmallEtaleInverseImage

/-!
# Finitely many stratified sheaves on one stratification

`AlgebraicGeometry.exists_stratification_isStratifiedSheaf_pair` puts *two* sheaves stratified by
a condition `P` on a single constructible stratification of an affine open. Stacks 03RZ compares
*five* sheaves at once: its criterion for a weak Serre subcategory,
`CategoryTheory.ObjectProperty.isWeakSerreClass_iff_prop_obj₂_of_exact`, is applied to a five term
exact sequence and asks for the middle term knowing the four outer ones. So four stratifications
have to be refined against each other, not two.

This file does that, for any number of sheaves. The refinement relation between stratifications of
one open subscheme is isolated as `AlgebraicGeometry.ConstructibleStratification.Refines`; it is
reflexive and transitive, the common refinement
`AlgebraicGeometry.ConstructibleStratification.inf` refines both of its arguments, and therefore a
finite family of stratifications has a common refinement. Transporting `P` from a stratum to the
refined strata inside it is a single step,
`AlgebraicGeometry.prop_strata_of_refines`, which is the content of the pair statement's proof
pulled out of it.

## Main results

* `AlgebraicGeometry.ConstructibleStratification.Refines`: one stratification refines another when
  each of its strata is immersed in a stratum of the other over the ambient scheme.
* `AlgebraicGeometry.ConstructibleStratification.exists_refines_forall`: a finite family of
  constructible stratifications of one open subscheme has a common refinement.
* `AlgebraicGeometry.prop_strata_of_refines`: a stratum condition stable under isomorphism and
  under inverse image along an immersion passes from a stratification to any refinement of it.
* `AlgebraicGeometry.exists_stratification_isStratifiedSheaf_forall`: a finite family of sheaves
  stratified by `P` is stratified by `P` on one stratification of each affine open.
* `AlgebraicGeometry.exists_stratification_isFiniteLocallyConstant_forall`: the same for `P` finite
  local constancy, with no further hypothesis.

## Implementation notes

The empty family needs a stratification to return, and
`AlgebraicGeometry.ConstructibleStratification.singleReduced` supplies it, so no nonemptiness
hypothesis is carried. The recursion is on the length of the family: the common refinement of
`s 0, …, s n` is `s 0` refined against a common refinement of the tail, and `Fin.cases` splits the
index.

## References

* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w v wc w'

namespace AlgebraicGeometry

namespace ConstructibleStratification

variable {B : BigEtaleSite.{u}} {X : B.Scheme} {U : X.obj.Opens}

/-- `r.Refines s` says that `r` is a refinement of `s`: every stratum of `r` is immersed in some
stratum of `s`, compatibly with the two inclusions into the ambient scheme.

This is exactly what a stratum condition has to be transported along, and it is the conclusion
`AlgebraicGeometry.ConstructibleStratification.exists_common_refinement` produces for a pair. -/
public def Refines (r s : ConstructibleStratification B X U) : Prop :=
  ∀ k : Fin r.n, ∃ (i : Fin s.n) (a : r.piece k ⟶ s.piece i),
    IsImmersion (B.inclusion.map a) ∧ a ≫ s.inclusion i = r.inclusion k

/-- Every stratification refines itself, by the identity of each stratum. -/
public theorem Refines.rfl (s : ConstructibleStratification B X U) : s.Refines s := fun k =>
  ⟨k, 𝟙 _, by rw [CategoryTheory.Functor.map_id]; infer_instance, by rw [Category.id_comp]⟩

/-- Refinement is transitive: an immersed stratum of an immersed stratum is immersed. -/
public theorem Refines.trans {r s t : ConstructibleStratification B X U}
    (hrs : r.Refines s) (hst : s.Refines t) : r.Refines t := by
  intro k
  obtain ⟨i, a, hai, hfa⟩ := hrs k
  obtain ⟨j, b, hbj, hfb⟩ := hst i
  refine ⟨j, a ≫ b, ?_, ?_⟩
  · rw [CategoryTheory.Functor.map_comp]
    have := hai
    have := hbj
    infer_instance
  · rw [Category.assoc, hfb, hfa]

/-- The common refinement of two stratifications refines the first. -/
public theorem inf_refines_fst (s t : ConstructibleStratification B X U) : (s.inf t).Refines s :=
  inf_factorsThrough_fst s t

/-- The common refinement of two stratifications refines the second. -/
public theorem inf_refines_snd (s t : ConstructibleStratification B X U) : (s.inf t).Refines t :=
  inf_factorsThrough_snd s t

/-- **A finite family of constructible stratifications of one open subscheme has a common
refinement.** -/
public theorem exists_refines_forall : ∀ {n : ℕ} (s : Fin n → ConstructibleStratification B X U),
    ∃ r : ConstructibleStratification B X U, ∀ i, r.Refines (s i)
  | 0, _ => ⟨singleReduced B X U, fun i => i.elim0⟩
  | _ + 1, s => by
    obtain ⟨r, hr⟩ := exists_refines_forall (fun i => s i.succ)
    exact ⟨(s 0).inf r, Fin.cases (inf_refines_fst _ _)
      fun j => (inf_refines_snd (s 0) r).trans (hr j)⟩

end ConstructibleStratification

variable (B : BigEtaleSite.{u}) {D : Type w} [Category.{v} D]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous D
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]

/-- **A stratum condition passes to a refinement.** If `P` is invariant under isomorphism of
sheaves and stable under inverse image along an immersion of the big étale site, and the inverse
image of `F` to every stratum of `s` satisfies `P`, then the same holds on every stratum of any
refinement of `s`.

Inverse image along a composite agrees with the composite of the inverse images only up to the
canonical isomorphism `AlgebraicGeometry.smallEtaleSheafPullbackCompIso`, inverse image being a
chosen left adjoint, which is why invariance under isomorphism is needed. -/
public theorem prop_strata_of_refines {X : B.Scheme} {U : X.obj.Opens}
    (P : ∀ T : B.Scheme, Sheaf (SmallEtale.topology B T.obj T.property) D → Prop)
    (hPIso : ∀ (T : B.Scheme) {F G : Sheaf (SmallEtale.topology B T.obj T.property) D},
      (F ≅ G) → P T F → P T G)
    (hPImmersion : ∀ (T T' : B.Scheme) (g : T' ⟶ T), IsImmersion (B.inclusion.map g) →
      ∀ G : Sheaf (SmallEtale.topology B T.obj T.property) D, P T G →
        P T' (((smallEtaleBaseChange B g).sheafPullback D
          (SmallEtale.topology B T.obj T.property)
          (SmallEtale.topology B T'.obj T'.property)).obj G))
    {F : Sheaf (SmallEtale.topology B X.obj X.property) D}
    {r s : ConstructibleStratification B X U} (href : r.Refines s)
    (hs : ∀ i, P (s.piece i) (((smallEtaleBaseChange B (s.inclusion i)).sheafPullback D
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B (s.piece i).obj (s.piece i).property)).obj F))
    (k : Fin r.n) :
    P (r.piece k) (((smallEtaleBaseChange B (r.inclusion k)).sheafPullback D
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B (r.piece k).obj (r.piece k).property)).obj F) := by
  obtain ⟨i, a, hai, hfac⟩ := href k
  rw [← hfac]
  exact hPIso _
    ((smallEtaleSheafPullbackCompIso B (r.piece k) (s.piece i) X a (s.inclusion i) D).app F)
    (hPImmersion _ _ a hai _ (hs i))

/-- **A finite family of sheaves stratified by `P` is stratified by `P` on one stratification.**
This is `AlgebraicGeometry.exists_stratification_isStratifiedSheaf_pair` for an arbitrary finite
number of sheaves, which is what Stacks 03RZ consumes: the weak Serre criterion compares five
terms of an exact sequence, so four of them have to be stratified simultaneously. -/
public theorem exists_stratification_isStratifiedSheaf_forall (X : B.Scheme)
    (P : ∀ T : B.Scheme, Sheaf (SmallEtale.topology B T.obj T.property) D → Prop)
    (hPIso : ∀ (T : B.Scheme) {F G : Sheaf (SmallEtale.topology B T.obj T.property) D},
      (F ≅ G) → P T F → P T G)
    (hPImmersion : ∀ (T T' : B.Scheme) (g : T' ⟶ T), IsImmersion (B.inclusion.map g) →
      ∀ G : Sheaf (SmallEtale.topology B T.obj T.property) D, P T G →
        P T' (((smallEtaleBaseChange B g).sheafPullback D
          (SmallEtale.topology B T.obj T.property)
          (SmallEtale.topology B T'.obj T'.property)).obj G))
    {n : ℕ} {F : Fin n → Sheaf (SmallEtale.topology B X.obj X.property) D}
    (hF : ∀ j, IsStratifiedSheaf B X P (F j)) (V : X.obj.affineOpens) :
    ∃ r : ConstructibleStratification B X V.1, ∀ (k) (j),
      P (r.piece k) (((smallEtaleBaseChange B (r.inclusion k)).sheafPullback D
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B (r.piece k).obj (r.piece k).property)).obj (F j)) := by
  choose s hs using fun j => hF j V
  obtain ⟨r, hr⟩ := ConstructibleStratification.exists_refines_forall s
  exact ⟨r, fun k j => prop_strata_of_refines B P hPIso hPImmersion (hr j) (hs j) k⟩

section Stratification

variable {A : Type w} [Category.{w'} A] {FA : A → A → Type*} {CA : A → Type wc}
  [∀ P Q, FunLike (FA P Q) (CA P) (CA Q)] [ConcreteCategory.{wc} A FA]
  [∀ (S : B.Scheme) (U : SmallEtale B S.obj S.property),
    HasWeakSheafify ((SmallEtale.topology B S.obj S.property).over U) A]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (S T : B.Scheme) (f : T ⟶ S) (X : SmallEtale B S.obj S.property),
    ((Over.post (X := X) (smallEtaleBaseChange B f)).sheafPushforwardContinuous A
      ((SmallEtale.topology B S.obj S.property).over X)
      ((SmallEtale.topology B T.obj T.property).over
        ((smallEtaleBaseChange B f).obj X))).IsRightAdjoint]

/-- **A finite family of finite locally constant stratified sheaves is stratified on one
stratification**, with no further hypothesis.

`AlgebraicGeometry.exists_stratification_isFiniteLocallyConstant_pair` is this for two sheaves;
Stacks 03RZ (2) needs it for the four outer terms of a five term exact sequence. -/
public theorem exists_stratification_isFiniteLocallyConstant_forall (X : B.Scheme) {n : ℕ}
    {F : Fin n → Sheaf (SmallEtale.topology B X.obj X.property) A}
    (hF : ∀ j, IsStratifiedSheaf B X
      (isFiniteLocallyConstantSmallEtale B (FA := FA) (CA := CA)) (F j))
    (V : X.obj.affineOpens) :
    ∃ r : ConstructibleStratification B X V.1, ∀ (k) (j),
      isFiniteLocallyConstantSmallEtale B (FA := FA) (CA := CA) (r.piece k)
        (((smallEtaleBaseChange B (r.inclusion k)).sheafPullback A
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B (r.piece k).obj (r.piece k).property)).obj (F j)) := by
  refine exists_stratification_isStratifiedSheaf_forall B X _ ?_ ?_ hF V
  · intro T F' G' e h
    have := h
    exact Stacks.ConstantSheaf.isFiniteLocallyConstant_congr
      (SmallEtale.topology B T.obj T.property) e
  · intro _ _ g _ G' h
    have := h
    exact isFiniteLocallyConstant_smallEtaleSheafPullback_of_overPost B g G'

end Stratification

end AlgebraicGeometry

end
