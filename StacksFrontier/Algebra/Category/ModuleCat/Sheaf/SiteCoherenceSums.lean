module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteFiniteTypeBridge
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Direct sums of coherent sheaves of modules on a site

Stacks 01BY (3) says that kernels, cokernels and finite direct sums of coherent sheaves of
modules are coherent.  Over a ringed *site* the predicate is
`SheafOfModules.IsCoherentOnSite`, Stacks 03DL(8); the kernel clause is
`Stacks.SheafOfModules.isCoherentOnSite_kerObj`, and this file proves the direct sum clause.

## Main results

* `Stacks.SheafOfModules.generates_restrict`: a finite generating family restricts to a finite
  generating family over the source of any arrow.
* `Stacks.SheafOfModules.isFiniteType_presheaf_of_split`: **a presheaf of modules split as a sum
  of two presheaves of modules of finite type is of finite type.**
* `Stacks.SheafOfModules.isCoherentOnSite_of_split`: **a sheaf of modules split as a sum of two
  coherent sheaves of modules on a site is coherent.**  This is Stacks 01BY (3) for a direct
  sum.
* `Stacks.SheafOfModules.isCoherentOnSite_biprod`,
  `Stacks.SheafOfModules.isCoherentOnSite_coprod` and
  `Stacks.SheafOfModules.isCoherentOnSite_prod`: the same for the biproduct, the coproduct and
  the product of two coherent sheaves of modules.

## Implementation notes

**What a direct sum is used for, and it is only one identity.**  Both conditions of coherence
are proved from the single identity `fst ≫ inl + snd ≫ inr = 𝟙`, read at an object of the
site, so the results are stated for a sheaf of modules carrying four maps satisfying it rather
than for a biproduct; `isCoherentOnSite_biprod` is the instance of that supplied by
`CategoryTheory.Limits.biprod.total`, which holds in any preadditive category.  No statement
that evaluation at an object preserves limits is needed, and the other four biproduct
identities are never used.

**Condition (1), finite type.**  The two given covering families need a common refinement, and
on a general site a pair of objects has no intersection: the refinement is instead indexed by
the triples consisting of a member of each family together with an object admitting an arrow to
both, which covers because the intersection of two covering sieves is covering.  Over such an
object the two generating families restrict, by `generates_restrict`, and the two restricted
families, mapped in by the two inclusions and concatenated, generate.

**Condition (2), relations.**  The relations among a finite family of sections `t` of the sum
are the tuples of coefficients that are relations among the first components `fst ∘ t` *and*
relations among the second components `snd ∘ t`; this is `mem_ker_relComb_iff`, and it is where
the total identity is used.  Such a tuple set is a submodule of the presheaf of relations among
`fst ∘ t`, cut out as the sectionwise kernel of the map sending a tuple to the corresponding
combination of the second components.  So
`Stacks.SheafOfModules.isFiniteType_kerSubmodule` applies, with the presheaf of relations among
`fst ∘ t` as the source — of finite type because `M` is coherent — and the restriction of `N`
to the slice site as the target, whose finite families of sections have finite-type relations
because coherence restricts to a slice.

**Why the module and ring universes agree here.**  The relations presheaf of a finite family of
sections takes values in modules over the ring at the *ring* universe `w`, whatever the module
universe of the sheaf is, whereas the target of the comparison map above is built from the
second summand and so lives at the module universe.  A morphism of presheaves of modules
requires the two to agree, so the direct sum clause is stated for
`SheafOfModules.{w} R`, unlike the kernel clause.

## References

* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.SheafOfModules

universe u v w m

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {S : Cᵒᵖ ⥤ RingCat.{w}}

/-- Restricting a finite generating family along an arrow of the site gives a finite generating
family over the source of that arrow. -/
theorem generates_restrict {A : PresheafOfModules.{m} S} {U V : C} (g : V ⟶ U) {n : ℕ}
    (s : Fin n → A.obj (op U)) (hs : PresheafOfModules.Generates J A s) :
    PresheafOfModules.Generates J A (fun j ↦ A.restrictₛₗ g.op (s j)) := by
  intro W f t
  obtain ⟨T, hT, hgen⟩ := hs W (f ≫ g) t
  refine ⟨T, hT, fun Z k hk ↦ ?_⟩
  obtain ⟨a, ha⟩ := hgen Z k hk
  refine ⟨a, Eq.trans (Finset.sum_congr rfl fun j _ ↦ ?_) ha⟩
  have hc : A.restrictₛₗ (k ≫ f).op (A.restrictₛₗ g.op (s j)) =
      A.restrictₛₗ (k ≫ f ≫ g).op (s j) := by
    show A.map (k ≫ f).op (A.map g.op (s j)) = A.map (k ≫ f ≫ g).op (s j)
    rw [← A.map_comp_apply]
    exact A.congr_map_apply (congrArg Quiver.Hom.op (Category.assoc k f g)) (s j)
  rw [hc]

/-- A morphism of presheaves of modules commutes with restriction and scalar multiplication. -/
private theorem smul_restrict_app {A Q : PresheafOfModules.{m} S} (i : A ⟶ Q) {X Y : Cᵒᵖ}
    (h : X ⟶ Y) (c : S.obj Y) (y : A.obj X) :
    c • Q.restrictₛₗ h (i.app X y) = i.app Y (c • A.restrictₛₗ h y) := by
  rw [map_smul]
  exact congrArg (fun z ↦ c • z) (PresheafOfModules.naturality_apply i h y).symm

/-- **Sectionwise finite type is stable under a split sum.**  If a presheaf of modules `Q` is
split as a sum of two presheaves of modules of finite type — in the weak sense that there are
maps both ways whose two composites add up to the identity on sections — then `Q` is of finite
type.

This is all that a finite direct sum, or a finite biproduct, supplies: the two biproduct
projections and inclusions satisfy the total identity `fst ≫ inl + snd ≫ inr = 𝟙`, and that
identity read at an object of the site is the hypothesis here.  Neither the other four
biproduct identities nor any statement that evaluation preserves limits is needed.

The covering family is the common refinement of the two given ones: its index type records a
member of each together with an object admitting an arrow to both, which is covering because
the intersection of two covering sieves is covering.  Over such an object the two generating
families restrict, and their images under the two inclusions, concatenated, generate `Q`,
because a section of `Q` is the sum of the images of its two components. -/
theorem isFiniteType_presheaf_of_split {A B Q : PresheafOfModules.{m} S}
    (p₁ : Q ⟶ A) (p₂ : Q ⟶ B) (i₁ : A ⟶ Q) (i₂ : B ⟶ Q)
    (htot : ∀ (X : Cᵒᵖ) (x : Q.obj X), i₁.app X (p₁.app X x) + i₂.app X (p₂.app X x) = x)
    (hA : PresheafOfModules.IsFiniteType J A) (hB : PresheafOfModules.IsFiniteType J B) :
    PresheafOfModules.IsFiniteType J Q := by
  classical
  obtain ⟨I₁, U₁, hU₁, gen₁⟩ := hA.exists_generators
  obtain ⟨I₂, U₂, hU₂, gen₂⟩ := hB.exists_generators
  refine isFiniteType_presheaf_of_coversTop
    (fun j : Σ (i : I₁) (k : I₂) (W : C), (W ⟶ U₁ i) × (W ⟶ U₂ k) ↦ j.2.2.1) ?_ ?_
  · intro Z
    refine J.superset_covering ?_ (J.intersection_covering (hU₁ Z) (hU₂ Z))
    rintro Y f ⟨h₁, h₂⟩
    obtain ⟨i, ⟨a⟩⟩ := h₁
    obtain ⟨k, ⟨b⟩⟩ := h₂
    exact ⟨⟨i, k, Y, (a, b)⟩, ⟨𝟙 Y⟩⟩
  · rintro ⟨i, k, W, a, b⟩
    obtain ⟨n, s, hs⟩ := gen₁ i
    obtain ⟨n', s', hs'⟩ := gen₂ k
    have hsW := generates_restrict (J := J) a s hs
    have hs'W := generates_restrict (J := J) b s' hs'
    refine ⟨n + n', Fin.append (fun l ↦ i₁.app (op W) (A.restrictₛₗ a.op (s l)))
      (fun l ↦ i₂.app (op W) (B.restrictₛₗ b.op (s' l))), ?_⟩
    intro V f x
    obtain ⟨T₁, hT₁, hg₁⟩ := hsW V f (p₁.app (op V) x)
    obtain ⟨T₂, hT₂, hg₂⟩ := hs'W V f (p₂.app (op V) x)
    refine ⟨T₁ ⊓ T₂, J.intersection_covering hT₁ hT₂, fun Z g hg ↦ ?_⟩
    obtain ⟨c, hc⟩ := hg₁ Z g hg.1
    obtain ⟨c', hc'⟩ := hg₂ Z g hg.2
    refine ⟨Fin.append c c', ?_⟩
    rw [Fin.sum_univ_add]
    have hleft : ∀ l : Fin n, Fin.append c c' (Fin.castAdd n' l) •
        Q.restrictₛₗ (g ≫ f).op (Fin.append
          (fun l ↦ i₁.app (op W) (A.restrictₛₗ a.op (s l)))
          (fun l ↦ i₂.app (op W) (B.restrictₛₗ b.op (s' l))) (Fin.castAdd n' l)) =
        i₁.app (op Z) (c l • A.restrictₛₗ (g ≫ f).op (A.restrictₛₗ a.op (s l))) := by
      intro l
      rw [Fin.append_left, Fin.append_left]
      exact smul_restrict_app i₁ _ _ _
    have hright : ∀ l : Fin n', Fin.append c c' (Fin.natAdd n l) •
        Q.restrictₛₗ (g ≫ f).op (Fin.append
          (fun l ↦ i₁.app (op W) (A.restrictₛₗ a.op (s l)))
          (fun l ↦ i₂.app (op W) (B.restrictₛₗ b.op (s' l))) (Fin.natAdd n l)) =
        i₂.app (op Z) (c' l • B.restrictₛₗ (g ≫ f).op (B.restrictₛₗ b.op (s' l))) := by
      intro l
      rw [Fin.append_right, Fin.append_right]
      exact smul_restrict_app i₂ _ _ _
    have hn₁ : A.restrictₛₗ g.op (p₁.app (op V) x) = p₁.app (op Z) (Q.restrictₛₗ g.op x) :=
      (PresheafOfModules.naturality_apply p₁ g.op x).symm
    have hn₂ : B.restrictₛₗ g.op (p₂.app (op V) x) = p₂.app (op Z) (Q.restrictₛₗ g.op x) :=
      (PresheafOfModules.naturality_apply p₂ g.op x).symm
    rw [Finset.sum_congr rfl fun l _ ↦ hleft l, Finset.sum_congr rfl fun l _ ↦ hright l,
      ← map_sum, ← map_sum, hc, hc', hn₁, hn₂]
    exact htot (op Z) (Q.restrictₛₗ g.op x)

section Relations

variable {R : Sheaf J RingCat.{w}} {M N P : SheafOfModules.{w} R}

/-- The map sending a tuple of coefficients to the corresponding linear combination of the
restrictions of a finite family of sections; the presheaf of relations among that family is its
kernel. -/
private noncomputable abbrev relComb (Q : SheafOfModules.{w} R) {U : C} {n : ℕ}
    (t : Fin n → Q.val.obj (op U)) (X : (Over U)ᵒᵖ) :
    (Fin n → R.obj.obj (op X.unop.left)) →ₗ[R.obj.obj (op X.unop.left)]
      Q.val.obj (op X.unop.left) :=
  Fintype.linearCombination (R.obj.obj (op X.unop.left))
    (fun j ↦ Q.val.restrictₛₗ X.unop.hom.op (t j))

private theorem relComb_comp (f : P ⟶ M) {U : C} {n : ℕ} (t : Fin n → P.val.obj (op U))
    (X : (Over U)ᵒᵖ) (a : Fin n → R.obj.obj (op X.unop.left)) :
    f.val.app (op X.unop.left) (relComb P t X a) =
      relComb M (fun j ↦ f.val.app (op U) (t j)) X a := by
  rw [Fintype.linearCombination_apply, Fintype.linearCombination_apply, map_sum]
  exact Finset.sum_congr rfl fun j _ ↦ (smul_restrict_app f.val _ _ _).symm

/-- **The relations among a finite family of sections of a split sum are the relations among
its two components.**  This is the only computation behind Stacks 01BY (3) for a direct sum,
and it uses only the total identity of the splitting. -/
private theorem mem_ker_relComb_iff (fst : P ⟶ M) (snd : P ⟶ N) (inl : M ⟶ P) (inr : N ⟶ P)
    (htot : ∀ (X : Cᵒᵖ) (x : P.val.obj X),
      inl.val.app X (fst.val.app X x) + inr.val.app X (snd.val.app X x) = x)
    {U : C} {n : ℕ} (t : Fin n → P.val.obj (op U)) (X : (Over U)ᵒᵖ)
    (a : Fin n → R.obj.obj (op X.unop.left)) :
    a ∈ LinearMap.ker (relComb P t X) ↔
      a ∈ LinearMap.ker (relComb M (fun j ↦ fst.val.app (op U) (t j)) X) ∧
        a ∈ LinearMap.ker (relComb N (fun j ↦ snd.val.app (op U) (t j)) X) := by
  simp only [LinearMap.mem_ker]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [← relComb_comp fst t X a, h, map_zero]
    · rw [← relComb_comp snd t X a, h, map_zero]
  · rintro ⟨h₁, h₂⟩
    have h := htot (op X.unop.left) (relComb P t X a)
    rw [relComb_comp fst t X a, relComb_comp snd t X a, h₁, h₂, map_zero, map_zero,
      add_zero] at h
    exact h.symm

/-- The submodule of the presheaf of relations among the first components consisting of the
tuples that are also relations among the second components.  The relations among a finite family
of sections of a split sum are exactly these, by `mem_ker_relComb_iff`. -/
private noncomputable def interSubmodule (fst : P ⟶ M) (snd : P ⟶ N)
    {U : C} {n : ℕ} (t : Fin n → P.val.obj (op U)) :
    (PresheafOfModules.relations M.val (fun j ↦ fst.val.app (op U) (t j))).Submodule where
  obj X := (LinearMap.ker (relComb N (fun j ↦ snd.val.app (op U) (t j)) X)).comap
    (LinearMap.ker (relComb M (fun j ↦ fst.val.app (op U) (t j)) X)).subtype
  map f := fun a ha ↦
    (((PresheafOfModules.relations N.val
      (fun j ↦ snd.val.app (op U) (t j))).map f) ⟨a.val, ha⟩).2

/-- The map from the presheaf of relations among the first components into the restriction of the
second summand, sending a tuple of coefficients to the corresponding linear combination of the
second components.  Its sectionwise kernel is `interSubmodule`. -/
private noncomputable def interHom (fst : P ⟶ M) (snd : P ⟶ N)
    {U : C} {n : ℕ} (t : Fin n → P.val.obj (op U)) :
    PresheafOfModules.relations M.val (fun j ↦ fst.val.app (op U) (t j)) ⟶ (N.over U).val where
  app X := ModuleCat.ofHom
    ((relComb N (fun j ↦ snd.val.app (op U) (t j)) X).comp
      (LinearMap.ker (relComb M (fun j ↦ fst.val.app (op U) (t j)) X)).subtype)
  naturality {X Y} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    have hc (j : Fin n) :
        N.val.restrictₛₗ f.unop.left.op
            (N.val.restrictₛₗ X.unop.hom.op (snd.val.app (op U) (t j))) =
          N.val.restrictₛₗ Y.unop.hom.op (snd.val.app (op U) (t j)) :=
      (N.val.map_comp_apply _ _ _).symm.trans
        (N.val.congr_map_apply (congrArg Quiver.Hom.op (Over.w f.unop)) _)
    change relComb N (fun j ↦ snd.val.app (op U) (t j)) Y
        (fun j ↦ R.obj.map f.unop.left.op (a.val j)) =
      N.val.restrictₛₗ f.unop.left.op
        (relComb N (fun j ↦ snd.val.app (op U) (t j)) X a.val)
    rw [Fintype.linearCombination_apply, Fintype.linearCombination_apply, map_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [map_smulₛₗ, hc]

private theorem mem_interSubmodule_iff (fst : P ⟶ M) (snd : P ⟶ N)
    {U : C} {n : ℕ} (t : Fin n → P.val.obj (op U)) (X : (Over U)ᵒᵖ)
    (a : (PresheafOfModules.relations M.val (fun j ↦ fst.val.app (op U) (t j))).obj X) :
    a ∈ (interSubmodule fst snd t).obj X ↔ (interHom fst snd t).app X a = 0 :=
  Iff.rfl

/-- The comparison of the presheaf of relations among a finite family of sections of a split sum
with the submodule of relations among the first components that are also relations among the
second ones.  At every object of the slice site the two are the same set of coefficient tuples,
read once as a subtype of the ambient tuples and once as a subtype of the relations among the
first components. -/
private noncomputable def interRelationsIso (fst : P ⟶ M) (snd : P ⟶ N) (inl : M ⟶ P)
    (inr : N ⟶ P)
    (htot : ∀ (X : Cᵒᵖ) (x : P.val.obj X),
      inl.val.app X (fst.val.app X x) + inr.val.app X (snd.val.app X x) = x)
    {U : C} {n : ℕ} (t : Fin n → P.val.obj (op U)) :
    (interSubmodule fst snd t).toPresheafOfModules ≅ PresheafOfModules.relations P.val t := by
  refine PresheafOfModules.isoMk (fun X ↦ LinearEquiv.toModuleIso
    { toFun := fun z ↦ ⟨z.1.1,
        (mem_ker_relComb_iff fst snd inl inr htot t X z.1.1).2 ⟨z.1.2, z.2⟩⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      invFun := fun z ↦ ⟨⟨z.1,
          ((mem_ker_relComb_iff fst snd inl inr htot t X z.1).1 z.2).1⟩,
        ((mem_ker_relComb_iff fst snd inl inr htot t X z.1).1 z.2).2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }) ?_
  intro X Y f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  rfl

/-- **Stacks Project, Tag 01BY (3), for a direct sum, on a site.**  A sheaf of modules split as
a sum of two coherent sheaves of modules is coherent.

Only the total identity of the splitting is used; the other four biproduct identities are not
needed.  Condition (1) is `isFiniteType_presheaf_of_split`.  For condition (2), the relations
among a finite family of sections of `P` are the relations among the first components which are
also relations among the second ones, by `mem_ker_relComb_iff`; that is a sectionwise kernel of
a map out of the presheaf of relations among the first components — of finite type, because `M`
is coherent — into the restriction of `N` to the slice, whose finite families of sections have
finite-type relations because `N` is coherent and coherence restricts to a slice.  So
`isFiniteType_kerSubmodule` applies. -/
@[ega "0 5.3.2" "special case"]
theorem isCoherentOnSite_of_split (fst : P ⟶ M) (snd : P ⟶ N) (inl : M ⟶ P) (inr : N ⟶ P)
    (htot : ∀ (X : Cᵒᵖ) (x : P.val.obj X),
      inl.val.app X (fst.val.app X x) + inr.val.app X (snd.val.app X x) = x)
    (hM : SheafOfModules.IsCoherentOnSite M) (hN : SheafOfModules.IsCoherentOnSite N) :
    SheafOfModules.IsCoherentOnSite P := by
  refine ⟨isFiniteType_presheaf_of_split fst.val snd.val inl.val inr.val htot
    hM.isFiniteType hN.isFiniteType, fun U n t ↦ ?_⟩
  exact isFiniteType_of_presheafIso (interRelationsIso fst snd inl inr htot t)
    (isFiniteType_kerSubmodule (interHom fst snd t) (interSubmodule fst snd t)
      (mem_interSubmodule_iff fst snd t)
      (hM.kernel_isFiniteType U n (fun j ↦ fst.val.app (op U) (t j)))
      (isCoherentOnSite_over N hN U).kernel_isFiniteType)

/-- **Stacks Project, Tag 01BY (3), for a biproduct, on a site.**  The biproduct of two coherent
sheaves of modules on a site is coherent.

The total identity of a binary biproduct in a preadditive category,
`biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙`, read at an object of the site, is
exactly the hypothesis of `isCoherentOnSite_of_split`. -/
theorem isCoherentOnSite_biprod {M N : SheafOfModules.{w} R} [HasBinaryBiproduct M N]
    (hM : SheafOfModules.IsCoherentOnSite M) (hN : SheafOfModules.IsCoherentOnSite N) :
    SheafOfModules.IsCoherentOnSite (M ⊞ N) := by
  refine isCoherentOnSite_of_split biprod.fst biprod.snd biprod.inl biprod.inr
    (fun X x ↦ ?_) hM hN
  let ev : ((M ⊞ N) ⟶ (M ⊞ N)) →+ (M ⊞ N).val.obj X :=
    { toFun := fun f ↦ f.val.app X x
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  exact (map_add ev (biprod.fst ≫ biprod.inl) (biprod.snd ≫ biprod.inr)).symm.trans
    (congrArg ev (biprod.total (X := M) (Y := N)))

/-- The coproduct of two coherent sheaves of modules on a site is coherent. -/
theorem isCoherentOnSite_coprod {M N : SheafOfModules.{w} R} [HasBinaryBiproduct M N]
    [HasBinaryCoproduct M N]
    (hM : SheafOfModules.IsCoherentOnSite M) (hN : SheafOfModules.IsCoherentOnSite N) :
    SheafOfModules.IsCoherentOnSite (M ⨿ N) :=
  isCoherentOnSite_of_iso (biprod.isoCoprod M N) (isCoherentOnSite_biprod hM hN)

/-- The product of two coherent sheaves of modules on a site is coherent. -/
theorem isCoherentOnSite_prod {M N : SheafOfModules.{w} R} [HasBinaryBiproduct M N]
    [HasBinaryProduct M N]
    (hM : SheafOfModules.IsCoherentOnSite M) (hN : SheafOfModules.IsCoherentOnSite N) :
    SheafOfModules.IsCoherentOnSite (M ⨯ N) :=
  isCoherentOnSite_of_iso (biprod.isoProd M N) (isCoherentOnSite_biprod hM hN)

end Relations

end Stacks.SheafOfModules

end
