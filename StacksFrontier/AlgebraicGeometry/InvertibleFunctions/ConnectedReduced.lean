module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.GroupTheory.Finiteness
public import StacksFrontier.AlgebraicGeometry.InvertibleFunctions.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleFunctions.FiniteType
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme

/-!
# Invertible functions on a connected reduced scheme over an algebraically closed field

Stacks Tag 04L6: for `k` an algebraically closed field and `X` a connected reduced scheme which is
locally of finite type over `k` with finitely many irreducible components, the group `𝒪^*(X)/k^*`
is finitely generated.

The source's argument has one geometric step and one topological one.  The irreducible components
`X_i` of `X`, taken with their reduced induced structure, are integral and locally of finite type
over `k`, so Tag 04L5 applies to each of them; and the homomorphism
`𝒪^*(X) → ∏ 𝒪^*(X_i)/k^*` has kernel exactly `k^*`.  Indeed a function in the kernel restricts on
each component to a constant `λ_i`, two components that meet force the corresponding constants to
agree, and since `X` is connected all the `λ_i` coincide; a reduced scheme covered by the `X_i` has
no section other than that constant with these restrictions.

Both steps are carried out here in the generality the argument actually uses:
`AlgebraicGeometry.fg_units_quotient_of_closed_cover` asks only that `X` be connected and reduced
and covered by the images of finitely many morphisms with closed image on each of which the
invertible functions modulo the constants are already known to be finitely generated.  Specialising
it to the irreducible components gives
`AlgebraicGeometry.fg_units_quotient_of_connectedSpace_of_isReduced_of_fg`, which is the tag with
Tag 04L5 as an explicit hypothesis quantified over all integral schemes locally of finite type over
`k`; `AlgebraicGeometry.fg_units_quotient_of_locallyOfFiniteType` is that tag, and discharging it
gives the tag itself.

## Main results

* `ConnectedSpace.exists_eq_const_of_isClosed_cover`: a function on the index set of a finite
  closed cover of a connected space which is constant on overlapping members is constant.
* `AlgebraicGeometry.fg_units_quotient_of_closed_cover`: the geometric step.  If a connected
  reduced scheme over `k` is covered by the images of finitely many morphisms with closed image,
  and the invertible functions modulo the constants are finitely generated on each source, then
  they are finitely generated on the scheme itself.
* `AlgebraicGeometry.fg_units_quotient_of_connectedSpace_of_isReduced_of_fg`: the two steps
  assembled, with Tag 04L5 as a hypothesis.
* `AlgebraicGeometry.fg_units_quotient_of_connectedSpace_of_isReduced`: Tag 04L6.

## References

* [Stacks Project, Tag 04L6](https://stacks.math.columbia.edu/tag/04L6)
* [Stacks Project, Tag 04L5](https://stacks.math.columbia.edu/tag/04L5)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

/-- Let a connected space be covered by finitely many nonempty closed subsets `C i`, and let
`a : ι → α` be a function on the index set such that `a i = a j` whenever `C i` and `C j` meet.
Then `a` is constant.

The subsets whose index has a given value of `a` form a closed set whose complement is the union of
the remaining ones, again closed; connectedness makes the first everything, so no index can have a
different value. -/
theorem ConnectedSpace.exists_eq_const_of_isClosed_cover {X : Type*} [TopologicalSpace X]
    [ConnectedSpace X] {ι : Type*} [Finite ι] {α : Type*} {C : ι → Set X}
    (hclosed : ∀ i, IsClosed (C i)) (hne : ∀ i, (C i).Nonempty)
    (hcover : ⋃ i, C i = Set.univ) (a : ι → α)
    (hoverlap : ∀ i j, (C i ∩ C j).Nonempty → a i = a j) :
    ∃ c, ∀ i, a i = c := by
  classical
  obtain ⟨x₀⟩ : Nonempty X := inferInstance
  obtain ⟨i₀, hx₀⟩ := Set.mem_iUnion.mp (hcover.ge (Set.mem_univ x₀))
  refine ⟨a i₀, fun i => ?_⟩
  have hclosedU : ∀ S : Set ι, IsClosed (⋃ j ∈ S, C j) := fun S =>
    (Set.toFinite S).isClosed_biUnion fun j _ => hclosed j
  have hdisj : ∀ x, x ∈ (⋃ j ∈ {j | a j = a i₀}, C j) →
      x ∉ (⋃ j ∈ {j | a j = a i₀}ᶜ, C j) := by
    intro x hxA hxB
    obtain ⟨j, hjS, hxj⟩ := Set.mem_iUnion₂.mp hxA
    obtain ⟨l, hlS, hxl⟩ := Set.mem_iUnion₂.mp hxB
    exact hlS ((hoverlap j l ⟨x, hxj, hxl⟩).symm.trans hjS)
  have hAB : (⋃ j ∈ {j | a j = a i₀}, C j) = (⋃ j ∈ {j | a j = a i₀}ᶜ, C j)ᶜ := by
    refine Set.eq_of_subset_of_subset (fun x hx => hdisj x hx) fun x hx => ?_
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp (hcover.ge (Set.mem_univ x))
    by_cases hj : a j = a i₀
    · exact Set.mem_biUnion hj hxj
    · exact absurd (Set.mem_biUnion hj hxj) hx
  have hclopen : IsClopen (⋃ j ∈ {j | a j = a i₀}, C j) :=
    ⟨hclosedU _, hAB ▸ (hclosedU _).isOpen_compl⟩
  have hAuniv : (⋃ j ∈ {j | a j = a i₀}, C j) = Set.univ :=
    hclopen.eq_univ ⟨x₀, Set.mem_biUnion rfl hx₀⟩
  by_contra hi
  obtain ⟨x, hx⟩ := hne i
  exact hdisj x (hAuniv.ge (Set.mem_univ x)) (Set.mem_biUnion hi hx)

namespace AlgebraicGeometry

/-- Global sections with equal pullbacks along `g` have equal evaluations at points of its
image. -/
private lemma Scheme.Γevaluation_eq_of_appTop_eq {X Y : Scheme.{u}} (g : Y ⟶ X) {s t : Γ(X, ⊤)}
    (h : g.appTop s = g.appTop t) (y : Y) : X.Γevaluation (g y) s = X.Γevaluation (g y) t :=
  (g.residueFieldMap y).hom.injective <| ((Scheme.Γevaluation_naturality_apply g y s).trans
    (congrArg (Y.Γevaluation y) h)).trans (Scheme.Γevaluation_naturality_apply g y t).symm

/-- **The geometric step of Stacks Tag 04L6.** Let `k` be a field and let `f : X ⟶ Spec k` be a
connected reduced scheme over `k`.  Suppose `X` is covered by the images of finitely many morphisms
`g i : Y i ⟶ X` with nonempty closed image, and that on each `Y i` the invertible global functions
modulo the constants from `k` form a finitely generated group.  Then the same holds for `X`.

The homomorphism `𝒪^*(X) → ∏ 𝒪^*(Y i)/k^*` has kernel the constants: a unit in the kernel
restricts on `Y i` to the image of some `c i ∈ k^*`, two indices whose images meet force
`c i = c j` because the evaluations at a common point agree and `k` injects into every residue
field, connectedness of `X` then makes all the `c i` equal to a single `c`, and the difference of
the unit and the image of `c` has vanishing evaluation at every point of `X`, hence is zero because
`X` is reduced.  A quotient which embeds into a finitely generated commutative group is finitely
generated. -/
theorem fg_units_quotient_of_closed_cover {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [ConnectedSpace X] [IsReduced X]
    {ι : Type*} [Finite ι] {Y : ι → Scheme.{u}} (g : ∀ i, Y i ⟶ X)
    (hne : ∀ i, Nonempty (Y i)) (hclosed : ∀ i, IsClosed (Set.range (g i)))
    (hcover : ⋃ i, Set.range (g i) = Set.univ)
    (hfg : ∀ i, Group.FG (Γ(Y i, ⊤)ˣ ⧸ (Units.map
      (((Scheme.ΓSpecIso (.of k)).inv ≫ (g i ≫ f).appTop).hom).toMonoidHom).range)) :
    Group.FG (Γ(X, ⊤)ˣ ⧸ (Units.map
      (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).toMonoidHom).range) := by
  classical
  set φ : k →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom with hφ
  set ψ : ∀ i, k →+* Γ(Y i, ⊤) :=
    fun i => ((Scheme.ΓSpecIso (.of k)).inv ≫ (g i ≫ f).appTop).hom with hψ
  have hcomp : ∀ (i : ι) (c : k), (g i).appTop (φ c) = ψ i c := by
    intro i c
    simp only [hψ, hφ, Scheme.Hom.comp_appTop]
    rfl
  have : Group.FG (∀ i, Γ(Y i, ⊤)ˣ ⧸ (Units.map (ψ i).toMonoidHom).range) := by
    rw [Group.fg_def, ← Subgroup.pi_top Set.univ]
    exact Subgroup.FG.pi fun i => (hfg i).out
  refine Group.fg_quotient_of_ker_eq
    (A := ∀ i, Γ(Y i, ⊤)ˣ ⧸ (Units.map (ψ i).toMonoidHom).range)
    (MonoidHom.pi fun i => (QuotientGroup.mk' (Units.map (ψ i).toMonoidHom).range).comp
      (Units.map ((g i).appTop.hom).toMonoidHom)) ?_
  ext u
  simp only [MonoidHom.mem_ker, MonoidHom.mem_range, MonoidHom.pi_apply, MonoidHom.coe_comp,
    Function.comp_apply, funext_iff, Pi.one_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  constructor
  · intro hu
    choose a ha using fun i => MonoidHom.mem_range.mp (hu i)
    have hval : ∀ i, ψ i (a i : k) = (g i).appTop (u : Γ(X, ⊤)) :=
      fun i => by simpa using congrArg Units.val (ha i)
    have hEval : ∀ (i : ι) (x : X), x ∈ Set.range (g i) →
        X.Γevaluation x (φ (a i : k)) = X.Γevaluation x (u : Γ(X, ⊤)) := by
      rintro i x ⟨y, rfl⟩
      exact Scheme.Γevaluation_eq_of_appTop_eq (g i) ((hcomp i _).trans (hval i)) y
    have hoverlap : ∀ i j, (Set.range (g i) ∩ Set.range (g j)).Nonempty → a i = a j := by
      rintro i j ⟨x, hxi, hxj⟩
      exact Units.ext (RingHom.injective ((X.Γevaluation x).hom.comp φ)
        ((hEval i x hxi).trans (hEval j x hxj).symm))
    obtain ⟨b, hb⟩ := ConnectedSpace.exists_eq_const_of_isClosed_cover hclosed
      (fun i => Set.range_nonempty_iff_nonempty.mpr (hne i)) hcover a hoverlap
    refine ⟨b, Units.ext (sub_eq_zero.mp ?_).symm⟩
    refine eq_zero_of_basicOpen_eq_bot _ ?_
    rw [Scheme.basicOpen_eq_bot_iff_forall_evaluation_eq_zero]
    intro x
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hcover.ge (Set.mem_univ (x : X)))
    simp only [map_sub]
    exact sub_eq_zero.mpr (hb i ▸ hEval i x hxi).symm
  · rintro ⟨c, rfl⟩ i
    exact ⟨c, Units.ext (by simpa using (hcomp i (c : k)).symm)⟩

/-- **Stacks Project, Tag 04L6, with Tag 04L5 as a hypothesis.** Let `k` be an algebraically closed
field and let `X` be a connected reduced scheme which is locally of finite type over `k` and has
finitely many irreducible components.  Then the invertible global functions on `X` modulo the
constants coming from `k` form a finitely generated group.

The hypothesis `h04L5` is Tag 04L5: for an *integral* scheme locally of finite type over `k` the
invertible global functions modulo the constants are finitely generated.  It is applied to the
irreducible components of `X` with their reduced induced structure, which are integral because `X`
is reduced and are locally of finite type over `k` because their inclusions are closed immersions;
they are finitely many by hypothesis, they are closed and nonempty, and they cover `X`.  Everything
else in this statement is the tag, and
`AlgebraicGeometry.fg_units_quotient_of_connectedSpace_of_isReduced` is the tag itself. -/
theorem fg_units_quotient_of_connectedSpace_of_isReduced_of_fg
    (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [ConnectedSpace X] [IsReduced X]
    [LocallyOfFiniteType f] (hX : (irreducibleComponents (X : Type u)).Finite)
    (h04L5 : ∀ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of k)), IsIntegral Y → LocallyOfFiniteType g →
      Group.FG (Γ(Y, ⊤)ˣ ⧸ (Units.map
        (((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom).toMonoidHom).range)) :
    Group.FG (Γ(X, ⊤)ˣ ⧸ (Units.map
      (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).toMonoidHom).range) := by
  classical
  have : Finite {C : Set X // C ∈ irreducibleComponents (X : Type u)} := hX.to_subtype
  have hcl : ∀ i : {C : Set X // C ∈ irreducibleComponents (X : Type u)}, IsClosed i.1 :=
    fun i => isClosed_of_mem_irreducibleComponents i.1 i.2
  have hrange : ∀ i : {C : Set X // C ∈ irreducibleComponents (X : Type u)},
      Set.range (Scheme.IdealSheafData.vanishingIdeal ⟨i.1, hcl i⟩).subschemeι = i.1 :=
    fun i => Scheme.IdealSheafData.range_subschemeι_vanishingIdeal _
  refine fg_units_quotient_of_closed_cover f
    (ι := {C : Set X // C ∈ irreducibleComponents (X : Type u)})
    (Y := fun i => (Scheme.IdealSheafData.vanishingIdeal ⟨i.1, hcl i⟩).subscheme)
    (g := fun i => (Scheme.IdealSheafData.vanishingIdeal ⟨i.1, hcl i⟩).subschemeι)
    (fun i => ?_) (fun i => ?_) ?_ (fun i => ?_)
  · obtain ⟨x, hx⟩ := i.2.1.nonempty
    obtain ⟨y, -⟩ := (hrange i).ge hx
    exact ⟨y⟩
  · rw [hrange i]
    exact hcl i
  · refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨C, hC, hxC⟩ := Set.mem_sUnion.mp
      (sUnion_irreducibleComponents.ge (Set.mem_univ x))
    exact Set.mem_iUnion.mpr ⟨⟨C, hC⟩, (hrange ⟨C, hC⟩).ge hxC⟩
  · have hirr : IrreducibleSpace
        (Scheme.IdealSheafData.vanishingIdeal (X := X) ⟨i.1, hcl i⟩).subscheme :=
      Scheme.IdealSheafData.irreducibleSpace_subscheme X _ (by rw [hrange i]; exact i.2.1)
    have : IsIntegral (Scheme.IdealSheafData.vanishingIdeal (X := X) ⟨i.1, hcl i⟩).subscheme :=
      isIntegral_of_irreducibleSpace_of_isReduced _
    exact h04L5 _ _ inferInstance inferInstance

/-- Let `k` be an algebraically closed field and let `X` be a connected reduced scheme which is
locally of finite type over `k` and has finitely many irreducible components.  Then `𝒪^*(X)/k^*`,
the group of invertible global functions on `X` modulo the constants coming from `k`, is a finitely
generated abelian group. -/
@[stacks 04L6]
theorem fg_units_quotient_of_connectedSpace_of_isReduced (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [ConnectedSpace X] [IsReduced X]
    [LocallyOfFiniteType f] (hX : (irreducibleComponents (X : Type u)).Finite) :
    Group.FG (Γ(X, ⊤)ˣ ⧸ (Units.map
      (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).toMonoidHom).range) :=
  fg_units_quotient_of_connectedSpace_of_isReduced_of_fg k f hX fun _ g hY hg =>
    have := hY; have := hg; fg_units_quotient_of_locallyOfFiniteType k g

end AlgebraicGeometry

end
