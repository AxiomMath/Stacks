module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteFiniteTypeLocality

/-!
# Cokernels of maps of coherent sheaves of modules on a site

Stacks 01BY (3) says that kernels, cokernels and finite direct sums of coherent sheaves of
modules are coherent.  Over a ringed *site* the predicate is
`SheafOfModules.IsCoherentOnSite`, Stacks 03DL(8); the kernel clause is
`Stacks.SheafOfModules.isCoherentOnSite_kerObj`, the direct sum clause is
`Stacks.SheafOfModules.isCoherentOnSite_of_split`, and this file proves the cokernel clause.

## Main results

* `Stacks.SheafOfModules.isFiniteType_relations_of_lift`: **the relations among a finite family
  of sections of a quotient presheaf of modules form a presheaf of finite type, as soon as the
  family lifts to the source, the kernel has finitely many generators, and the source has
  finite-type relations.**  This is the whole content of the cokernel clause, stated for
  presheaves of modules and for an arbitrary map, with its kernel given as a submodule of the
  source.
* `Stacks.SheafOfModules.exists_cover_preimage_of_epi`: an epimorphism of sheaves of modules is
  surjective on sections after restriction to the members of a covering sieve.
* `Stacks.SheafOfModules.isFiniteType_presheaf_cokernel`: the underlying presheaf of modules of
  a cokernel of a map of sheaves of modules whose target is sectionwise of finite type is
  sectionwise of finite type.
* `Stacks.SheafOfModules.isFiniteType_kerObj_cokernelπ`: **the kernel of the projection onto a
  cokernel — that is, the image of the map — is sectionwise of finite type when the source
  is.**
* `Stacks.SheafOfModules.isCoherentOnSite_cokernel`: **the cokernel of a map of coherent sheaves
  of modules on a site is coherent.**  This is Stacks 01BY (3) for cokernels.

## Implementation notes

**The comparison with the relations of a lift is an equality, not a local statement.**  Let
`p : N ⟶ Q` be the projection onto the cokernel and let `t₁, …, t_n` be sections of `Q` over
`U` which lift to sections `t'₁, …, t'_n` of `N`.  A coefficient tuple `a` is a relation among
the `t_j` over `V` exactly when `∑ a_j t'_j|_V` lies in the *sectionwise* kernel `L` of `p`,
and for a map of sheaves of modules the sectionwise kernel is the kernel, so that is an
equality of submodules and not merely a local statement.  The locality that the sheaf cokernel
does introduce sits in two other places, and both are discharged by the lemmas of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteFiniteTypeLocality`.

**First locality: the comparison with the relations of the *enlarged* family.**  Picking finitely
many generators `l₁, …, l_q` of `L` over `U`, a relation among `t'₁, …, t'_n, l₁, …, l_q` in `N`
projects to a relation among the `t_j`; that is `relComparison`, and
`Stacks.SheafOfModules.imageSubmodule` of it is a subpresheaf of the relations among the `t_j`
which is of finite type because `N` is coherent.  The inclusion is *not* an equality: `a` being
a relation among the `t_j` says `∑ a_j t'_j|_V ∈ L(V)`, and the generators of `L` express a
section of `L` as a combination of the `l_k` only *locally*.  So the subpresheaf has locally
trivial quotient, which is exactly the hypothesis of
`Stacks.SheafOfModules.isFiniteType_of_locallyMem`.  That lemma is the keystone, and it is why
no presheaf of coefficient tuples and no direct sum has to be constructed here.

**Second locality: a family of sections of a cokernel lifts only locally.**  The hypotheses of
`isFiniteType_relations_of_lift` ask for a lift over `U` itself and for generators of `L` over
`U`, and a cokernel supplies neither: the projection is only locally surjective, and finite type
of `L` only gives generators on a covering family.  Both are obtained on the intersection of the
`n` image sieves of the `t_j` with the sieve of objects carrying generators of `L`, and
`Stacks.SheafOfModules.isFiniteType_relations_of_cover` assembles the resulting proofs over the
members of that sieve into the statement over `U`.

**Where the image of the map enters.**  The submodule `L` is the sectionwise kernel of the
projection onto the cokernel, so it is the image of `φ`, and all that is needed of it is that it
be sectionwise of finite type.  That is `isFiniteType_kerObj_cokernelπ`: the canonical map from
the source to `ker(coker φ)` is an epimorphism — it is `CategoryTheory.Abelian.factorThruImage`
up to the comparison of the sectionwise kernel with the categorical one — hence locally
surjective, so a generating family of the source maps to a generating family of `L` by
`Stacks.SheafOfModules.isFiniteType_of_locallySurjective`.  **Coherence of `L` is never needed**,
only its finite type.

**Universes.** `PresheafOfModules.relations` always lands at the ring universe `w`, so
`isFiniteType_relations_of_lift` leaves the module universe `m` of `N` and `Q` free; it is the
sheaf-level statements that are restricted to `SheafOfModules.{w} R`, because the abelian
structure and the identification of epimorphisms with locally surjective maps both need the
module universe to be the universe of the abelian groups being sheafified.

**Which cokernel.** The abelian structure used is Mathlib's `SheafOfModules.instAbelian`,
supplied by the `HasSheafify` and `WEqualsLocallyBijective` hypotheses; the lower-priority
`AlgebraicGeometry.SheafOfModules.instAbelianSheafOfModules` is not selected, so this is the
same cokernel as in
`Stacks.SheafOfModules.LocalCokernel.isFinitePresentation_cokernel`, Stacks 0H98.

## References

* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.SheafOfModules

universe u v w m

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {S : Cᵒᵖ ⥤ RingCat.{w}}

/-! ### The relations clause for a quotient, given a lift -/

/-- A map of presheaves of modules commutes with restriction of sections. -/
private theorem app_restrictₛₗ {N Q : PresheafOfModules.{m} S} (p : N ⟶ Q) {X Y : Cᵒᵖ}
    (f : X ⟶ Y) (x : N.obj X) :
    p.app Y (N.restrictₛₗ f x) = Q.restrictₛₗ f (p.app X x) :=
  PresheafOfModules.naturality_apply p f x

/-- A relation among a family of sections of `N` enlarged by sections of the kernel of `p`
projects to a relation among the images of the original sections: the coefficients of the
sections of the kernel contribute nothing after applying `p`. -/
private theorem comb_append_eq {N Q : PresheafOfModules.{m} S} (p : N ⟶ Q) (L : N.Submodule)
    (hL : ∀ (X : Cᵒᵖ) (x : N.obj X), x ∈ L.obj X ↔ p.app X x = 0)
    {U : C} {n q : ℕ} (t : Fin n → Q.obj (op U)) (t' : Fin n → N.obj (op U))
    (ht : ∀ j, p.app (op U) (t' j) = t j) (l : Fin q → L.toPresheafOfModules.obj (op U))
    {Y : C} (f : Y ⟶ U) (c : Fin (n + q) → S.obj (op Y))
    (hc : ∑ i, c i • N.restrictₛₗ f.op (Fin.append t' (fun k ↦ (l k).val) i) = 0) :
    ∑ j, c (Fin.castAdd q j) • Q.restrictₛₗ f.op (t j) = 0 := by
  have hzero : ∀ k : Fin q, p.app (op U) ((l k).val) = 0 :=
    fun k ↦ (hL (op U) ((l k).val)).mp (l k).2
  have h := congrArg (fun z ↦ p.app (op Y) z) hc
  simp only [map_sum, map_smul, app_restrictₛₗ p f.op, map_zero] at h
  rw [Fin.sum_univ_add] at h
  simp only [Fin.append_left, Fin.append_right, ht, hzero, map_zero, smul_zero,
    Finset.sum_const_zero, add_zero] at h
  exact h

/-- Conversely, a coefficient tuple whose combination of the restricted sections `t'` is a
combination of the restricted sections of the kernel extends, by the negatives of the latter
coefficients, to a relation among the enlarged family. -/
private theorem append_comb_eq_zero {N : PresheafOfModules.{m} S} (L : N.Submodule)
    {U : C} {n q : ℕ} (t' : Fin n → N.obj (op U))
    (l : Fin q → L.toPresheafOfModules.obj (op U))
    {Y Z : C} (e : Y ⟶ U) (k : Z ⟶ Y) (xv : Fin n → S.obj (op Y))
    (b : Fin q → S.obj (op Z))
    (hb : ∑ i, b i • N.restrictₛₗ (k ≫ e).op ((l i).val)
      = N.restrictₛₗ k.op (∑ j, xv j • N.restrictₛₗ e.op (t' j))) :
    ∑ i, Fin.append (fun j ↦ ConcreteCategory.hom (S.map k.op) (xv j)) (fun i ↦ -(b i)) i •
        N.restrictₛₗ (k ≫ e).op (Fin.append t' (fun i ↦ (l i).val) i) = 0 := by
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  rw [← restrict_sum_smul N e k xv t']
  have h2 : ∑ i, (-(b i)) • N.restrictₛₗ (k ≫ e).op ((l i).val)
      = -(N.restrictₛₗ k.op (∑ j, xv j • N.restrictₛₗ e.op (t' j))) := by
    rw [← hb, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [neg_smul]
  rw [h2, add_neg_cancel]

/-- The projection of a relation among the lifted family enlarged by finitely many sections of
the kernel of `p` onto its first `n` coefficients, as a map from the relations presheaf of the
enlarged family in `N` to the relations presheaf of the original family in `Q`.  It is the
identity on coefficients, so it is natural on the nose. -/
private noncomputable def relComparison {N Q : PresheafOfModules.{m} S} (p : N ⟶ Q)
    (L : N.Submodule)
    (hL : ∀ (X : Cᵒᵖ) (x : N.obj X), x ∈ L.obj X ↔ p.app X x = 0)
    {U : C} {n q : ℕ} (t : Fin n → Q.obj (op U)) (t' : Fin n → N.obj (op U))
    (ht : ∀ j, p.app (op U) (t' j) = t j) (l : Fin q → L.toPresheafOfModules.obj (op U)) :
    PresheafOfModules.relations N (Fin.append t' (fun k ↦ (l k).val)) ⟶
      PresheafOfModules.relations Q t where
  app X := ModuleCat.ofHom
    { toFun := fun c ↦ ⟨fun j ↦ c.val (Fin.castAdd q j), by
        rw [LinearMap.mem_ker, Fintype.linearCombination_apply]
        refine comb_append_eq p L hL t t' ht l X.unop.hom c.val ?_
        have hc := c.2
        rwa [LinearMap.mem_ker, Fintype.linearCombination_apply] at hc⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  naturality {X Y} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    rfl

/-- **Every relation among the images of the lifted family is locally in the image of
`relComparison`.**  A relation `a` among the `t_j` makes `∑ a_j t'_j` a section of the kernel
`L`, which on a covering sieve is a combination of the generators `l_k` of `L`; the coefficients
of that combination, negated, extend `a` to a relation among the enlarged family.

This is the one place where the locality of the sheaf cokernel appears, and it is why the
comparison is an inclusion with locally trivial quotient rather than an isomorphism. -/
private theorem locallyMem_relComparison {N Q : PresheafOfModules.{m} S} (p : N ⟶ Q)
    (L : N.Submodule)
    (hL : ∀ (X : Cᵒᵖ) (x : N.obj X), x ∈ L.obj X ↔ p.app X x = 0)
    {U : C} {n q : ℕ} (t : Fin n → Q.obj (op U)) (t' : Fin n → N.obj (op U))
    (ht : ∀ j, p.app (op U) (t' j) = t j) (l : Fin q → L.toPresheafOfModules.obj (op U))
    (hl : PresheafOfModules.Generates J L.toPresheafOfModules l)
    (Y : Over U) (x : (PresheafOfModules.relations Q t).obj (op Y)) :
    ∃ T : Sieve Y, T ∈ (J.over U) Y ∧ ∀ (Y'' : Over U) (h : Y'' ⟶ Y), T h →
      (PresheafOfModules.relations Q t).restrictₛₗ h.op x ∈
        (imageSubmodule (relComparison p L hL t t' ht l)).obj (op Y'') := by
  obtain ⟨xv, hxv⟩ := x
  have hx : ∑ j, xv j • Q.restrictₛₗ Y.hom.op (t j) = 0 := by
    rwa [LinearMap.mem_ker, Fintype.linearCombination_apply] at hxv
  have hmem : (∑ j, xv j • N.restrictₛₗ Y.hom.op (t' j)) ∈ L.obj (op Y.left) := by
    rw [hL, map_sum]
    simp only [map_smul, app_restrictₛₗ p Y.hom.op, ht]
    exact hx
  obtain ⟨T₀, hT₀, hT₀gen⟩ := hl Y.left Y.hom ⟨_, hmem⟩
  refine ⟨(Sieve.overEquiv Y).symm T₀, J.overEquiv_symm_mem_over Y T₀ hT₀, ?_⟩
  intro Y'' h hh
  rw [Sieve.overEquiv_symm_iff] at hh
  obtain ⟨b, hb⟩ := hT₀gen Y''.left h.left hh
  have hbval : ∑ i, b i • N.restrictₛₗ (h.left ≫ Y.hom).op ((l i).val)
      = N.restrictₛₗ h.left.op (∑ j, xv j • N.restrictₛₗ Y.hom.op (t' j)) := by
    have h0 := congrArg (fun z ↦ L.ι.app (op Y''.left) z) hb
    rw [map_sum] at h0
    simp only [map_smul] at h0
    refine Eq.trans (Finset.sum_congr rfl fun i _ ↦ ?_) (Eq.trans h0 ?_)
    · exact congrArg (fun y ↦ b i • y)
        (PresheafOfModules.naturality_apply L.ι (h.left ≫ Y.hom).op (l i)).symm
    · exact PresheafOfModules.naturality_apply L.ι h.left.op ⟨_, hmem⟩
  have hhom : h.left ≫ Y.hom = Y''.hom := Over.w h
  refine ⟨⟨Fin.append (fun j ↦ ConcreteCategory.hom (S.map h.left.op) (xv j))
      (fun k ↦ -(b k)), ?_⟩, ?_⟩
  · rw [LinearMap.mem_ker, Fintype.linearCombination_apply, ← hhom]
    exact append_comb_eq_zero L t' l Y.hom h.left xv b hbval
  · exact Subtype.ext (funext fun j ↦
      Eq.trans (Fin.append_left (fun j ↦ ConcreteCategory.hom (S.map h.left.op) (xv j))
        (fun k ↦ -(b k)) j) (relations_coe_restrict t h.op ⟨xv, hxv⟩ j).symm)

/-- **The relations clause of coherence for a quotient, from a lift of the family of sections.**
Let `p : N ⟶ Q` be a map of presheaves of modules whose sectionwise kernel is a submodule `L` of
`N`, let `t₁, …, t_n` be sections of `Q` over `U` lifting to sections `t'₁, …, t'_n` of `N`, and
let `l₁, …, l_q` be a finite generating family of `L` over `U`.  If every finite family of
sections of `N` has a finite-type presheaf of relations — that is, if the relations condition of
coherence holds for `N` — then the relations among the `t_j` form a presheaf of finite type on
the slice site over `U`.

The relations among the `t_j` contain the projections of the relations among
`t'₁, …, t'_n, l₁, …, l_q`, which form a presheaf of finite type by the hypothesis on `N`; and
they contain them with locally trivial quotient, by `locallyMem_relComparison`, which is enough
by `isFiniteType_of_locallyMem`. -/
theorem isFiniteType_relations_of_lift {N Q : PresheafOfModules.{m} S} (p : N ⟶ Q)
    (L : N.Submodule)
    (hL : ∀ (X : Cᵒᵖ) (x : N.obj X), x ∈ L.obj X ↔ p.app X x = 0)
    {U : C} {n q : ℕ} (t : Fin n → Q.obj (op U)) (t' : Fin n → N.obj (op U))
    (ht : ∀ j, p.app (op U) (t' j) = t j) (l : Fin q → L.toPresheafOfModules.obj (op U))
    (hl : PresheafOfModules.Generates J L.toPresheafOfModules l)
    (hN : ∀ (V : C) (k : ℕ) (s : Fin k → N.obj (op V)),
      PresheafOfModules.IsFiniteType (J.over V) (PresheafOfModules.relations N s)) :
    PresheafOfModules.IsFiniteType (J.over U) (PresheafOfModules.relations Q t) :=
  isFiniteType_of_locallyMem (imageSubmodule (relComparison p L hL t t' ht l))
    (locallyMem_relComparison p L hL t t' ht l hl)
    (isFiniteType_imageSubmodule _ (hN U (n + q) _))

/-! ### Stacks 01BY (3) for cokernels -/

section Cokernel

variable {R : Sheaf J RingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]

/-- A section of a presheaf of modules read as a section of the underlying presheaf of abelian
groups. -/
private abbrev abGroupSection {N : PresheafOfModules.{w} R.obj} (X : Cᵒᵖ) (x : N.obj X) :
    ((PresheafOfModules.toPresheaf R.obj).obj N).obj X := x

/-- **An epimorphism of sheaves of modules is surjective on sections after restriction to the
members of a covering sieve.**  This is
`Stacks.SheafOfModules.LocalCokernel.locallySurjective_of_epi` read on sections, which is the
form in which `Stacks.SheafOfModules.isFiniteType_of_locallySurjective` asks for it; the
covering sieve is the image sieve of the section. -/
theorem exists_cover_preimage_of_epi {M N : SheafOfModules.{w} R} (f : M ⟶ N) [Epi f]
    (V : C) (x : N.val.obj (op V)) :
    ∃ T : Sieve V, T ∈ J V ∧ ∀ (W : C) (g : W ⟶ V), T g →
      ∃ y : M.val.obj (op W), f.val.app (op W) y = N.val.restrictₛₗ g.op x := by
  have hls : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map f.val) :=
    LocalCokernel.locallySurjective_of_epi f
  refine ⟨Presheaf.imageSieve ((PresheafOfModules.toPresheaf R.obj).map f.val)
    (abGroupSection (op V) x), Presheaf.imageSieve_mem J _ _, ?_⟩
  intro W g hg
  obtain ⟨y, hy⟩ := hg
  exact ⟨y, hy⟩

/-- **The underlying presheaf of modules of a cokernel is of finite type as soon as that of the
target is.**  The projection onto the cokernel is an epimorphism, hence locally surjective, so a
generating family of the target maps to a generating family of the cokernel.  This is condition
(1) of coherence for a cokernel. -/
theorem isFiniteType_presheaf_cokernel {M N : SheafOfModules.{w} R} (φ : M ⟶ N)
    (hN : PresheafOfModules.IsFiniteType J N.val) :
    PresheafOfModules.IsFiniteType J (cokernel φ).val :=
  isFiniteType_of_locallySurjective (cokernel.π φ).val
    (exists_cover_preimage_of_epi (cokernel.π φ)) hN

/-- **The kernel of the projection onto a cokernel is of finite type as soon as the source
is.**  That kernel is the image of `φ`, and the canonical map to it from the source is an
epimorphism: it agrees with `CategoryTheory.Abelian.factorThruImage` through the comparison of
the sectionwise kernel `SheafOfModules.kerObj` with the categorical one.  So the statement is
`isFiniteType_of_locallySurjective` applied to `SheafOfModules.kerLift`.

This is the only property of the image that the cokernel clause uses; coherence of the image is
never needed. -/
theorem isFiniteType_kerObj_cokernelπ {M N : SheafOfModules.{w} R} (φ : M ⟶ N)
    (hM : PresheafOfModules.IsFiniteType J M.val) :
    PresheafOfModules.IsFiniteType J (SheafOfModules.kerObj (cokernel.π φ)).val := by
  let e : SheafOfModules.kerObj (cokernel.π φ) ≅ kernel (cokernel.π φ) :=
    (SheafOfModules.kerIsLimit (cokernel.π φ)).conePointUniqueUpToIso
      (limit.isLimit (parallelPair (cokernel.π φ) 0))
  have hι : e.hom ≫ kernel.ι (cokernel.π φ) = SheafOfModules.kerIota (cokernel.π φ) :=
    IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero
  have hfac : SheafOfModules.kerLift φ (cokernel.condition φ) ≫ e.hom
      = Abelian.factorThruImage φ := by
    rw [← cancel_mono (kernel.ι (cokernel.π φ)), Category.assoc, hι,
      SheafOfModules.kerLift_comp, kernel.lift_ι]
  have hepi : Epi (SheafOfModules.kerLift φ (cokernel.condition φ)) := by
    have h1 : SheafOfModules.kerLift φ (cokernel.condition φ)
        = Abelian.factorThruImage φ ≫ e.inv := by
      rw [← hfac, Category.assoc, e.hom_inv_id, Category.comp_id]
    rw [h1]
    infer_instance
  exact isFiniteType_of_locallySurjective (SheafOfModules.kerLift φ (cokernel.condition φ)).val
    (exists_cover_preimage_of_epi (SheafOfModules.kerLift φ (cokernel.condition φ))) hM

/-- **Stacks Project, Tag 01BY (3), for cokernels, on a site.**  The cokernel of a map of
coherent sheaves of modules on a site is coherent.

Condition (1) is `isFiniteType_presheaf_cokernel`.  For condition (2), fix a finite family `t`
of sections of the cokernel over `U`.  Each `t_j` lifts to the target of `φ` on its image sieve,
because the projection onto the cokernel is locally surjective; and the kernel of that
projection — the image of `φ` — is of finite type by `isFiniteType_kerObj_cokernelπ`, so it has
finitely many generators over the members of a covering family.  On the intersection of those
`n + 1` covering sieves both pieces of data are available, and
`isFiniteType_relations_of_lift` gives the relations condition there; the intersection is
covering, so `isFiniteType_relations_of_cover` lifts the conclusion to `U`. -/
theorem isCoherentOnSite_cokernel {M N : SheafOfModules.{w} R} (φ : M ⟶ N)
    (hM : SheafOfModules.IsCoherentOnSite M) (hN : SheafOfModules.IsCoherentOnSite N) :
    SheafOfModules.IsCoherentOnSite (cokernel φ) := by
  classical
  refine ⟨isFiniteType_presheaf_cokernel φ hN.isFiniteType, ?_⟩
  intro U n t
  choose Tl hTl hTlift using fun j : Fin n ↦
    exists_cover_preimage_of_epi (cokernel.π φ) U (t j)
  obtain ⟨I, A, hA, hgenL⟩ :=
    (isFiniteType_kerObj_cokernelπ φ hM.isFiniteType).exists_generators
  have hS1 : (Finset.univ.inf Tl) ∈ J U := by
    have hfin : ∀ s : Finset (Fin n), s.inf Tl ∈ J U := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih =>
        simpa [Finset.inf_insert, hi] using J.intersection_covering (hTl i) ih
    exact hfin Finset.univ
  refine isFiniteType_relations_of_cover _ t (J.intersection_covering hS1 (hA U)) ?_
  intro V g hg
  have hlift : ∀ j : Fin n, ∃ y : N.val.obj (op V),
      (cokernel.π φ).val.app (op V) y = (cokernel φ).val.restrictₛₗ g.op (t j) := by
    intro j
    have hle : Finset.univ.inf Tl ≤ Tl j := Finset.inf_le (Finset.mem_univ j)
    exact hTlift j V g (hle _ hg.1)
  choose t' ht' using hlift
  obtain ⟨i, ⟨a⟩⟩ := (Sieve.mem_ofObjects_iff A g).mp hg.2
  obtain ⟨q, l, hl⟩ := hgenL i
  exact isFiniteType_relations_of_lift (cokernel.π φ).val
    (SheafOfModules.kerSubmodule (cokernel.π φ)).toSubmodule
    (SheafOfModules.mem_kerSubmodule (cokernel.π φ))
    _ t' ht' (fun k ↦ (SheafOfModules.kerObj (cokernel.π φ)).val.restrictₛₗ a.op (l k))
    (generates_restrict a l hl) hN.kernel_isFiniteType

end Cokernel

end Stacks.SheafOfModules

end
