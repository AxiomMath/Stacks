module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.NoetherianSpace
public import StacksFrontier.AlgebraicGeometry.GroupScheme.ProjectiveLineToGroupSchemeConstant
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Components
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineDimension
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineProjModel

/-!
# The geometry of part (a) of Stacks 0AFB: a loop of rational curves

Part (a) of the proof of Stacks 0AFB shows that `H¹(X₀, A)` is not torsion, for `X₀` a nodal
curve over an algebraically closed field `k` whose dual graph has a loop `C₀, …, C_{m-1}` of
rational curves, by glueing trivial torsors along the components with a twist by a point of
infinite order at one node. Its non-triviality comes from a computation on the components: a
morphism from a rational curve to a group scheme is constant (Stacks 0AEN), so a family of
sections over the components that agree at the nodes up to the twist forces the twist to vanish
when one goes around the loop.

This file proves that computation, on two opens `V₀ = Y ∖ {x₀}` and `V₁ ∋ x₀` of a scheme `Y`
locally of finite type over `k`, whose intersection is the disjoint union of an open `W''`
meeting only the component `C₁` and an open `W'` not meeting `C₁`, where `x₀` is the node
between `C₀` and `C₁`. Sections `s₀` over `V₀` and `s₁` over `V₁` of a separated group scheme
`G` locally of finite type over `k` which agree on `W'` and differ by a point `b ∈ G(k)` on `W''`
force `b = 1`.

## Main results

* `Stacks.Examples.NonAlgebraicHomStack.isClosed_singleton_of_ne_genericPoint`: in an
  irreducible space of dimension at most one, a point other than the generic point is closed.
* `Stacks.Examples.NonAlgebraicHomStack.exists_opens_of_component`: the two opens `V₀`, `V₁`
  and the decomposition `V₀ ∩ V₁ = W' ⊔ W''` attached to a component `C₁` whose non-generic
  points are closed and a closed point `x₀`.
* `Stacks.Examples.NonAlgebraicHomStack.exists_glue_of_sup_eq_top`: glueing two morphisms
  defined on two opens covering a scheme.
* `Stacks.Examples.NonAlgebraicHomStack.exists_eq_comp_of_iso_projectiveLine`: a morphism over
  `k` from a scheme isomorphic to `ℙ¹_k` to a separated group scheme locally of finite type is
  constant (Stacks 0AEN).
* `Stacks.Examples.NonAlgebraicHomStack.eq_one_of_loop`: the computation around the loop.

## References

* [Stacks Project, Tag 0AFB](https://stacks.math.columbia.edu/tag/0AFB)
* [Stacks Project, Tag 0AEN](https://stacks.math.columbia.edu/tag/0AEN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Examples.NonAlgebraicHomStack

/-! ### Closed points of a curve -/

section Topology

variable {X : Type*} [TopologicalSpace X]

/-- In an irreducible quasi-sober `T₀` space of Krull dimension at most one, every point other
than the generic point is closed: otherwise a point in its closure, its closure and the whole
space would form a chain of three irreducible closed subsets. -/
theorem isClosed_singleton_of_ne_genericPoint [IrreducibleSpace X] [QuasiSober X] [T0Space X]
    (hdim : topologicalKrullDim X ≤ 1) {z : X} (hz : z ≠ genericPoint X) :
    IsClosed ({z} : Set X) := by
  by_contra hcl
  obtain ⟨z', hz'cl, hz'ne⟩ : ∃ z' ∈ closure ({z} : Set X), z' ≠ z := by
    by_contra h
    push Not at h
    refine hcl ?_
    have : closure ({z} : Set X) = {z} :=
      Set.Subset.antisymm (fun y hy => Set.mem_singleton_iff.mpr (h y hy)) subset_closure
    rw [← this]
    exact isClosed_closure
  let a : IrreducibleCloseds X := ⟨closure {z'}, isIrreducible_singleton.closure, isClosed_closure⟩
  let b : IrreducibleCloseds X := ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩
  let c : IrreducibleCloseds X := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hab : a < b := by
    refine lt_of_le_of_ne (show closure {z'} ⊆ closure {z} from
      closure_minimal (Set.singleton_subset_iff.mpr hz'cl) isClosed_closure) fun h => ?_
    have h1 : z ∈ closure ({z'} : Set X) := by
      have : closure ({z'} : Set X) = closure {z} := congrArg (fun t : IrreducibleCloseds X =>
        (t : Set X)) h
      rw [this]
      exact subset_closure rfl
    exact hz'ne ((specializes_iff_mem_closure.mpr hz'cl).antisymm
      (specializes_iff_mem_closure.mpr h1)).eq.symm
  have hbc : b < c := by
    refine lt_of_le_of_ne (show closure {z} ⊆ Set.univ from Set.subset_univ _) fun h => ?_
    have h1 : IsGenericPoint z (⊤ : Set X) :=
      isGenericPoint_def.mpr (congrArg (fun t : IrreducibleCloseds X => (t : Set X)) h)
    exact hz (h1.eq (genericPoint_spec X))
  rcases Order.krullDim_le_one_iff.mp hdim b with hmin | hmax
  · exact not_isMin_of_lt hab hmin
  · exact not_isMax_of_lt hbc hmax

/-- In a quasi-sober Noetherian space, a closed set all of whose points are closed is finite: it is
a finite union of irreducible closed subsets, each the closure of its generic point. -/
theorem finite_of_isClosed_of_forall_isClosed_singleton [NoetherianSpace X] [QuasiSober X]
    {F : Set X} (hF : IsClosed F) (h : ∀ x ∈ F, IsClosed ({x} : Set X)) : F.Finite := by
  obtain ⟨S, hSf, hScl, hSirr, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hF
  refine hSf.sUnion fun t ht => ?_
  obtain ⟨g, hg⟩ := QuasiSober.sober (hSirr t ht) (hScl t ht)
  have hgt : t = {g} := by
    rw [← hg.def]
    exact (h g (Set.mem_sUnion_of_mem hg.mem ht)).closure_eq
  rw [hgt]
  exact Set.finite_singleton g

end Topology

/-! ### The two opens around a node -/

/-- **The two opens around a node.** Let `Y` be a Noetherian scheme, `C₁` an irreducible
component of `Y` all of whose points other than its generic point are closed in `Y`, and `x₀` a
closed point of `Y`. There are opens `V₀ = Y ∖ {x₀}` and `V₁ ∋ x₀` covering `Y`, and a
decomposition of `V₀ ∩ V₁` into disjoint opens `W'` and `W''`, where `W'` does not meet `C₁` and
`W''` meets no other irreducible component of `Y`.

`V₁` is the complement of the finitely many points other than `x₀` in which `C₁` meets the union
`D` of the other components; `W'` is the part of `V₀ ∩ V₁` off `C₁` and `W''` the part off `D`. -/
theorem exists_opens_of_component (Y : Scheme.{u}) [NoetherianSpace Y]
    (C₁ : irreducibleComponents Y)
    (hC₁ : ∀ z ∈ (C₁ : Set Y), ¬ IsGenericPoint z (C₁ : Set Y) → IsClosed ({z} : Set Y))
    (x₀ : Y) (hx₀ : IsClosed ({x₀} : Set Y)) :
    ∃ V₀ V₁ W' W'' : Y.Opens, V₀ ⊔ V₁ = ⊤ ∧ V₀ ⊓ V₁ ≤ W' ⊔ W'' ∧ W' ⊓ W'' = ⊥ ∧
      W' ≤ V₀ ⊓ V₁ ∧ W'' ≤ V₀ ⊓ V₁ ∧ x₀ ∈ V₁ ∧ (∀ y, y ≠ x₀ → y ∈ V₀) ∧
      (∀ y ∈ W', y ∉ (C₁ : Set Y)) ∧
      ∀ Z : irreducibleComponents Y, Z ≠ C₁ → ∀ y ∈ W'', y ∉ (Z : Set Y) := by
  classical
  have hfin : (irreducibleComponents Y).Finite := NoetherianSpace.finite_irreducibleComponents
  let D : Set Y := ⋃ Z ∈ {Z : Set Y | Z ∈ irreducibleComponents Y ∧ Z ≠ (C₁ : Set Y)}, Z
  have hDcl : IsClosed D :=
    (hfin.subset fun Z hZ => hZ.1).isClosed_biUnion fun Z hZ =>
      isClosed_of_mem_irreducibleComponents Z hZ.1
  have hsubD : ∀ Z : irreducibleComponents Y, Z ≠ C₁ → (Z : Set Y) ⊆ D := fun Z hZ y hy =>
    Set.mem_biUnion (x := (Z : Set Y)) ⟨Z.2, fun h => hZ (Subtype.ext h)⟩ hy
  let F : Set Y := (C₁ : Set Y) ∩ D
  have hFcl : IsClosed F := (isClosed_of_mem_irreducibleComponents _ C₁.2).inter hDcl
  have hFpts : ∀ z ∈ F, IsClosed ({z} : Set Y) := by
    rintro z ⟨hzC, hzD⟩
    refine hC₁ z hzC fun hgen => ?_
    obtain ⟨Z, ⟨hZcomp, hZne⟩, hzZ⟩ := Set.mem_iUnion₂.mp hzD
    have hsub : (C₁ : Set Y) ⊆ Z := by
      rw [← hgen.def]
      exact closure_minimal (Set.singleton_subset_iff.mpr hzZ)
        (isClosed_of_mem_irreducibleComponents Z hZcomp)
    exact hZne (Set.Subset.antisymm (C₁.2.2 hZcomp.1 hsub) hsub)
  have hFfin : F.Finite := finite_of_isClosed_of_forall_isClosed_singleton hFcl hFpts
  let F' : Set Y := F \ {x₀}
  have hF'cl : IsClosed F' := by
    have : F' = ⋃ y ∈ F', {y} := (Set.biUnion_of_singleton F').symm
    rw [this]
    exact (hFfin.sdiff (t := {x₀})).isClosed_biUnion fun y hy => hFpts y hy.1
  let V₀ : Y.Opens := ⟨{x₀}ᶜ, hx₀.isOpen_compl⟩
  let V₁ : Y.Opens := ⟨F'ᶜ, hF'cl.isOpen_compl⟩
  let OC : Y.Opens := ⟨(C₁ : Set Y)ᶜ,
    (isClosed_of_mem_irreducibleComponents _ C₁.2).isOpen_compl⟩
  let OD : Y.Opens := ⟨Dᶜ, hDcl.isOpen_compl⟩
  refine ⟨V₀, V₁, V₀ ⊓ V₁ ⊓ OC, V₀ ⊓ V₁ ⊓ OD, ?_, ?_, ?_, inf_le_left, inf_le_left, ?_, ?_, ?_, ?_⟩
  · refine eq_top_iff.mpr fun y _ => ?_
    by_cases hy : y = x₀
    · refine Or.inr fun hyF' => ?_
      exact hyF'.2 hy
    · exact Or.inl hy
  · rintro y ⟨hy₀, hy₁⟩
    by_cases hyC : y ∈ (C₁ : Set Y)
    · refine Or.inr ⟨⟨hy₀, hy₁⟩, fun hyD => hy₁ ⟨⟨hyC, hyD⟩, hy₀⟩⟩
    · exact Or.inl ⟨⟨hy₀, hy₁⟩, hyC⟩
  · refine eq_bot_iff.mpr ?_
    rintro y ⟨⟨_, hyC⟩, ⟨_, hyD⟩⟩
    obtain ⟨Z, hZ, hyZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {y}
      isIrreducible_singleton
    by_cases hZC : Z = (C₁ : Set Y)
    · exact hyC (hZC ▸ hyZ rfl)
    · exact hyD (hsubD ⟨Z, hZ⟩ (fun h => hZC (congrArg Subtype.val h)) (hyZ rfl))
  · exact fun hx => hx.2 rfl
  · exact fun y hy => hy
  · exact fun y hy => hy.2
  · exact fun Z hZ y hy hyZ => hy.2 (hsubD Z hZ hyZ)

/-- A point of an open subscheme lies in the open. -/
lemma ι_apply_mem {Z : Scheme.{u}} (V : Z.Opens) (x : V.toScheme) : V.ι x ∈ V := by
  have : V.ι x ∈ Set.range V.ι := ⟨x, rfl⟩
  rwa [Scheme.Opens.range_ι] at this

/-! ### Glueing morphisms on two opens -/

section Glue

variable {Z T : Scheme.{u}}

/-- The projections of the fibre product of two open immersions factor through the intersection
of the two opens. -/
theorem pullback_fst_snd_eq_homOfLE (V V' : Z.Opens) :
    ∃ φ : pullback V.ι V'.ι ⟶ (V ⊓ V').toScheme,
      pullback.fst V.ι V'.ι = φ ≫ Z.homOfLE inf_le_left ∧
        pullback.snd V.ι V'.ι = φ ≫ Z.homOfLE inf_le_right := by
  have hrange : Set.range (pullback.fst V.ι V'.ι ≫ V.ι) ⊆ Set.range (V ⊓ V').ι := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine ⟨ι_apply_mem V _, ?_⟩
    rw [pullback.condition]
    exact ι_apply_mem V' _
  refine ⟨IsOpenImmersion.lift (V ⊓ V').ι _ hrange, ?_, ?_⟩
  · rw [← cancel_mono V.ι, Category.assoc, Scheme.homOfLE_ι, IsOpenImmersion.lift_fac]
  · rw [← cancel_mono V'.ι, Category.assoc, Scheme.homOfLE_ι, IsOpenImmersion.lift_fac,
      pullback.condition]

/-- Two morphisms on opens which agree on the intersection agree on the fibre product of the two
open immersions. -/
theorem pullback_fst_comp_eq_of_homOfLE (V V' : Z.Opens) (a : V.toScheme ⟶ T)
    (b : V'.toScheme ⟶ T)
    (hab : Z.homOfLE (inf_le_left : V ⊓ V' ≤ V) ≫ a = Z.homOfLE inf_le_right ≫ b) :
    pullback.fst V.ι V'.ι ≫ a = pullback.snd V.ι V'.ι ≫ b := by
  obtain ⟨φ, h₁, h₂⟩ := pullback_fst_snd_eq_homOfLE V V'
  rw [h₁, h₂, Category.assoc, Category.assoc, hab]

/-- **Glueing two morphisms.** Two morphisms defined on opens `P`, `Q` covering a scheme `Z` which
agree on `P ∩ Q` are the restrictions of a single morphism on `Z`. -/
theorem exists_glue_of_sup_eq_top (P Q : Z.Opens) (hPQ : P ⊔ Q = ⊤) (a : P.toScheme ⟶ T)
    (b : Q.toScheme ⟶ T)
    (hab : Z.homOfLE (inf_le_left : P ⊓ Q ≤ P) ≫ a = Z.homOfLE inf_le_right ≫ b) :
    ∃ g : Z ⟶ T, P.ι ≫ g = a ∧ Q.ι ≫ g = b := by
  let U : Bool → Z.Opens := fun i => cond i P Q
  have hU : IsOpenCover U := by
    change iSup U = ⊤
    rw [iSup_bool_eq]
    exact hPQ
  let 𝒰 := Z.openCoverOfIsOpenCover U hU
  let f : ∀ i, 𝒰.X i ⟶ T := fun i => match i with
    | true => a
    | false => b
  have hba : Z.homOfLE (inf_le_left : Q ⊓ P ≤ Q) ≫ b = Z.homOfLE inf_le_right ≫ a := by
    have e₁ : Z.homOfLE (inf_le_left : Q ⊓ P ≤ Q) =
        Z.homOfLE (inf_comm Q P).le ≫ Z.homOfLE (inf_le_right : P ⊓ Q ≤ Q) :=
      (Z.homOfLE_homOfLE _ _).symm
    have e₂ : Z.homOfLE (inf_le_right : Q ⊓ P ≤ P) =
        Z.homOfLE (inf_comm Q P).le ≫ Z.homOfLE (inf_le_left : P ⊓ Q ≤ P) :=
      (Z.homOfLE_homOfLE _ _).symm
    rw [e₁, e₂, Category.assoc, Category.assoc, hab]
  have hcompat : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ f i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ f j
  · rintro (_ | _) (_ | _)
    · exact pullback_fst_comp_eq_of_homOfLE Q Q b b rfl
    · exact pullback_fst_comp_eq_of_homOfLE Q P b a hba
    · exact pullback_fst_comp_eq_of_homOfLE P Q a b hab
    · exact pullback_fst_comp_eq_of_homOfLE P P a a rfl
  exact ⟨𝒰.glueMorphisms f hcompat, 𝒰.ι_glueMorphisms f hcompat true,
    𝒰.ι_glueMorphisms f hcompat false⟩

/-- **Glueing two morphisms over a base.** -/
theorem exists_glue_over_of_sup_eq_top {S : Scheme.{u}} {Z G : Over S} (P Q : Z.left.Opens)
    (hPQ : P ⊔ Q = ⊤) (a : P.toScheme ⟶ G.left) (b : Q.toScheme ⟶ G.left)
    (ha : a ≫ G.hom = P.ι ≫ Z.hom) (hb : b ≫ G.hom = Q.ι ≫ Z.hom)
    (hab : Z.left.homOfLE (inf_le_left : P ⊓ Q ≤ P) ≫ a = Z.left.homOfLE inf_le_right ≫ b) :
    ∃ g : Z ⟶ G, P.ι ≫ g.left = a ∧ Q.ι ≫ g.left = b := by
  obtain ⟨g, hga, hgb⟩ := exists_glue_of_sup_eq_top P Q hPQ a b hab
  refine ⟨Over.homMk g ?_, hga, hgb⟩
  refine Scheme.hom_ext_of_forall _ _ fun x => ?_
  have hx : x ∈ P ⊔ Q := hPQ ▸ trivial
  rcases hx with hx | hx
  · exact ⟨P, hx, by rw [← Category.assoc, hga, ha]⟩
  · exact ⟨Q, hx, by rw [← Category.assoc, hgb, hb]⟩

end Glue

/-! ### Morphisms from a rational curve to a group scheme -/

section Constant

variable {k : Type u} [Field k]

/-- **Stacks 0AEN on a rational curve.** A morphism over `k` from a scheme isomorphic over `k` to
the projective line `ℙ¹_k` into a separated group scheme locally of finite type over `k` factors
through the structure morphism, followed by a morphism `Spec k ⟶ G`. -/
theorem exists_eq_comp_of_iso_projectiveLine {Z : Over (Spec (.of k))}
    (e : Z ≅ Over.mk (projectiveLine k ↘ Spec (.of k))) (G : Over (Spec (.of k))) [GrpObj G]
    [IsSeparated G.hom] [LocallyOfFiniteType G.hom] (g : Z ⟶ G) :
    ∃ c : Spec (.of k) ⟶ G.left, g.left = Z.hom ≫ c := by
  let eP := projectiveLineIsoProjectiveSpaceOver k
  have hι : eP.inv ≫ (projectiveLine k ↘ Spec (.of k)) =
      projectiveSpaceOverRing 1 (CommRingCat.of k) ↘ Spec (CommRingCat.of k) := by
    rw [Iso.inv_comp_eq]
    exact (projectiveLineIsoProjectiveSpaceOver_hom_fst k).symm
  let ψ := eP.inv ≫ e.inv.left ≫ g.left
  have hψ : ψ ≫ G.hom =
      projectiveSpaceOverRing 1 (CommRingCat.of k) ↘ Spec (CommRingCat.of k) := by
    simp only [ψ, Category.assoc, Over.w g]
    rw [Over.w e.inv]
    exact hι
  obtain ⟨s, hs⟩ := exists_eq_comp_of_projectiveSpace_to_grpObj k G ψ hψ
  refine ⟨s, ?_⟩
  have h₁ : g.left = e.hom.left ≫ eP.hom ≫ ψ := by
    simp only [ψ, Iso.hom_inv_id_assoc]
    rw [← Over.comp_left_assoc, e.hom_inv_id, Over.id_left, Category.id_comp]
  rw [h₁, hs, ← Category.assoc eP.hom, projectiveLineIsoProjectiveSpaceOver_hom_fst,
    ← Category.assoc]
  exact congrArg (· ≫ s) (Over.w e.hom)

/-- On an irreducible component of `Y` isomorphic over `k` to `ℙ¹_k`, every point other than the
generic point of the component is closed in `Y`: the component has dimension one. -/
theorem isClosed_singleton_of_mem_component {Y : Scheme.{u}} (π : Y ⟶ Spec (.of k))
    (Cc : irreducibleComponents Y)
    (e : Over.mk (Y.reducedComponentι Cc ≫ π) ≅ Over.mk (projectiveLine k ↘ Spec (.of k))) :
    ∀ z ∈ (Cc : Set Y), ¬ IsGenericPoint z (Cc : Set Y) → IsClosed ({z} : Set Y) := by
  intro z hz hgen
  let ic := Y.reducedComponentι Cc
  have hdim : topologicalKrullDim (Y.reducedComponent Cc) ≤ 1 := by
    let eS : Y.reducedComponent Cc ≅ projectiveLine k := (Over.forget _).mapIso e
    rw [IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso eS).isHomeomorph,
      topologicalKrullDim_projectiveLine]
  obtain ⟨w, rfl⟩ : z ∈ Set.range ic := (Y.range_reducedComponentι Cc).symm ▸ hz
  have hw : w ≠ genericPoint (Y.reducedComponent Cc) := fun h =>
    hgen (h ▸ Y.isGenericPoint_reducedComponentι Cc)
  have := isClosed_singleton_of_ne_genericPoint hdim hw
  have himg := ic.isClosedEmbedding.isClosedMap _ this
  rwa [Set.image_singleton] at himg

end Constant

/-! ### Going around the loop -/

section Loop

variable {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} (π : Y ⟶ Spec (.of k))

/-- An open of a scheme `Y` over `k`, as a scheme over `k`. -/
abbrev openOver (V : Y.Opens) : Over (Spec (.of k)) := Over.mk (V.ι ≫ π)

/-- The inclusion of opens `V ≤ V'`, as a morphism of schemes over `k`. -/
def openOverHomOfLE {V V' : Y.Opens} (h : V ≤ V') : openOver π V ⟶ openOver π V' :=
  Over.homMk (Y.homOfLE h) (by simp [openOver])

omit [IsAlgClosed k] in
@[simp]
lemma openOverHomOfLE_left {V V' : Y.Opens} (h : V ≤ V') :
    (openOverHomOfLE π h).left = Y.homOfLE h := rfl

/-- The restriction of a closed immersion `i : Z ⟶ Y` to the preimage of an open `V`, as a
morphism to `V`. -/
def restrictPreimage {Z : Scheme.{u}} (i : Z ⟶ Y) (V : Y.Opens) :
    (i ⁻¹ᵁ V).toScheme ⟶ V.toScheme :=
  IsOpenImmersion.lift V.ι ((i ⁻¹ᵁ V).ι ≫ i) (by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact ι_apply_mem (i ⁻¹ᵁ V) p)

@[reassoc (attr := simp)]
lemma restrictPreimage_ι {Z : Scheme.{u}} (i : Z ⟶ Y) (V : Y.Opens) :
    restrictPreimage i V ≫ V.ι = (i ⁻¹ᵁ V).ι ≫ i :=
  IsOpenImmersion.lift_fac _ _ _

/-- A morphism whose image lies in an open of any scheme factors through it. -/
lemma exists_comp_ι_eq' {Z T : Scheme.{u}} (V : Z.Opens) (g : T ⟶ Z) (hg : ∀ t, g t ∈ V) :
    ∃ g' : T ⟶ V.toScheme, g' ≫ V.ι = g :=
  ⟨IsOpenImmersion.lift V.ι g (by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hg t), IsOpenImmersion.lift_fac _ _ _⟩

/-- A morphism whose image lies in an open factors through it. -/
lemma exists_comp_ι_eq {T : Scheme.{u}} (V : Y.Opens) (g : T ⟶ Y) (hg : ∀ t, g t ∈ V) :
    ∃ g' : T ⟶ V.toScheme, g' ≫ V.ι = g :=
  ⟨IsOpenImmersion.lift V.ι g (by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hg t), IsOpenImmersion.lift_fac _ _ _⟩

omit [IsAlgClosed k] in
/-- **The section of the twist.** If an open `W` is the disjoint union of opens `W'` and `W''`,
there is a morphism `W ⟶ G` over `k` which is `1` on `W'` and the constant `b ∈ G(k)` on `W''`. -/
theorem exists_twist_section (G : Over (Spec (.of k))) [GrpObj G] (W W' W'' : Y.Opens)
    (hW : W ≤ W' ⊔ W'') (h' : W' ≤ W) (h'' : W'' ≤ W) (hdisj : W' ⊓ W'' = ⊥)
    (b : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    ∃ σ : openOver π W ⟶ G, openOverHomOfLE π h' ≫ σ = 1 ∧
      openOverHomOfLE π h'' ≫ σ = toUnit _ ≫ b := by
  let Z := openOver π W
  let P := W.ι ⁻¹ᵁ W'
  let Q := W.ι ⁻¹ᵁ W''
  have hPQ : P ⊔ Q = ⊤ := by
    refine eq_top_iff.mpr fun z _ => ?_
    have : W.ι z ∈ W := by
      have : W.ι z ∈ Set.range W.ι := ⟨z, rfl⟩
      rwa [Scheme.Opens.range_ι] at this
    exact hW this
  have hη : η[G].left ≫ G.hom = 𝟙 (Spec (.of k)) := Over.w η[G]
  have hb : b.left ≫ G.hom = 𝟙 (Spec (.of k)) := Over.w b
  obtain ⟨g, hgP, hgQ⟩ := exists_glue_over_of_sup_eq_top (Z := Z) (G := G) P Q hPQ
    (P.ι ≫ Z.hom ≫ η[G].left) (Q.ι ≫ Z.hom ≫ b.left)
    (by rw [Category.assoc, Category.assoc, hη, Category.comp_id])
    (by rw [Category.assoc, Category.assoc, hb, Category.comp_id]) (by
      have : IsEmpty (P ⊓ Q).toScheme := ⟨fun z => by
        have h₁ : W.ι ((P ⊓ Q).ι z) ∈ W' ⊓ W'' := by
          have hz : (P ⊓ Q).ι z ∈ P ⊓ Q := by
            have : (P ⊓ Q).ι z ∈ Set.range (P ⊓ Q).ι := ⟨z, rfl⟩
            rwa [Scheme.Opens.range_ι] at this
          exact ⟨hz.1, hz.2⟩
        rw [hdisj] at h₁
        exact h₁⟩
      exact isInitialOfIsEmpty.hom_ext _ _)
  have hlift : ∀ (V : Y.Opens) (hV : V ≤ W), ∃ q : V.toScheme ⟶ (W.ι ⁻¹ᵁ V).toScheme,
      q ≫ (W.ι ⁻¹ᵁ V).ι = Y.homOfLE hV := fun V hV =>
    exists_comp_ι_eq' (W.ι ⁻¹ᵁ V) (Y.homOfLE hV) fun v => by
      change W.ι (Y.homOfLE hV v) ∈ V
      have e : W.ι (Y.homOfLE hV v) = V.ι v := congrArg (fun f => f v) (Y.homOfLE_ι hV)
      rw [e]
      exact ι_apply_mem V v
  refine ⟨g, ?_, ?_⟩
  · obtain ⟨q, hq⟩ := hlift W' h'
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, openOverHomOfLE_left, Hom.one_def, Over.toUnit_left]
    rw [← hq, Category.assoc, hgP, ← Category.assoc, ← Category.assoc, hq]
    simp [Z]
  · obtain ⟨q, hq⟩ := hlift W'' h''
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, openOverHomOfLE_left, Over.toUnit_left]
    rw [← hq, Category.assoc, hgQ, ← Category.assoc, ← Category.assoc, hq]
    simp [Z]

variable [LocallyOfFiniteType π]

/-- The `k`-point of `Y` at a closed point. -/
def kPoint (y : Y) (hy : IsClosed ({y} : Set Y)) : Spec (.of k) ⟶ Y :=
  pointOfClosedPoint π y hy

lemma kPoint_comp (y : Y) (hy : IsClosed ({y} : Set Y)) : kPoint π y hy ≫ π = 𝟙 _ :=
  pointOfClosedPoint_comp π y hy

/-- A section of `π` through a closed point `y` is the `k`-point of `y`. -/
lemma eq_kPoint (y : Y) (hy : IsClosed ({y} : Set Y)) (p : Spec (.of k) ⟶ Y) (hp : p ≫ π = 𝟙 _)
    (hpy : p (IsLocalRing.closedPoint k) = y) : p = kPoint π y hy :=
  ext_of_apply_closedPoint_eq π hp (kPoint_comp π y hy)
    (by rw [hpy]; exact (pointOfClosedPoint_apply π y hy _).symm)

/-- The `k`-point at a closed point lying in an open, as a morphism to the open. -/
def kPointOpenLeft (V : Y.Opens) (y : Y) (hy : IsClosed ({y} : Set Y)) (hyV : y ∈ V) :
    Spec (.of k) ⟶ V.toScheme :=
  IsOpenImmersion.lift V.ι (kPoint π y hy) (by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι, kPoint, pointOfClosedPoint_apply]
    exact hyV)

lemma kPointOpen_left_ι (V : Y.Opens) (y : Y) (hy : IsClosed ({y} : Set Y)) (hyV : y ∈ V) :
    kPointOpenLeft π V y hy hyV ≫ V.ι = kPoint π y hy :=
  IsOpenImmersion.lift_fac _ _ _

/-- The `k`-point at a closed point lying in an open, as a point of the open. -/
def kPointOpen (V : Y.Opens) (y : Y) (hy : IsClosed ({y} : Set Y)) (hyV : y ∈ V) :
    𝟙_ (Over (Spec (.of k))) ⟶ openOver π V :=
  Over.homMk (kPointOpenLeft π V y hy hyV) (by
    change _ ≫ V.ι ≫ π = 𝟙 _
    rw [← Category.assoc, kPointOpen_left_ι, kPoint_comp])

@[simp]
lemma kPointOpen_left (V : Y.Opens) (y : Y) (hy : IsClosed ({y} : Set Y)) (hyV : y ∈ V) :
    (kPointOpen π V y hy hyV).left = kPointOpenLeft π V y hy hyV := rfl

variable (G : Over (Spec (.of k))) [GrpObj G] [IsSeparated G.hom] [LocallyOfFiniteType G.hom]

/-- **A component isomorphic to `ℙ¹_k`.** Let `Cc` be an irreducible component of `Y` isomorphic
over `k` to `ℙ¹_k`, let `V₀`, `V₁` be opens covering `Y`, and let `t` over `V₀` and `s₁` over
`V₁` be morphisms to `G` which agree on an open `W ≤ V₀ ⊓ V₁` containing `Cc ∩ V₀ ∩ V₁`. Then
there is a morphism `c : Spec k ⟶ G` which is the value of `t` at the `k`-point of every closed
point of `Cc ∩ V₀` and the value of `s₁` at the `k`-point of every closed point of `Cc ∩ V₁`: the
two glue to a morphism on the component, which is constant by Stacks 0AEN. -/
theorem exists_const_of_agree (Cc : irreducibleComponents Y)
    (e : Over.mk (Y.reducedComponentι Cc ≫ π) ≅ Over.mk (projectiveLine k ↘ Spec (.of k)))
    (V₀ V₁ : Y.Opens) (hcov : V₀ ⊔ V₁ = ⊤) (t : openOver π V₀ ⟶ G) (s₁ : openOver π V₁ ⟶ G)
    (W : Y.Opens) (hW₀ : W ≤ V₀) (hW₁ : W ≤ V₁)
    (hCW : ∀ y ∈ (Cc : Set Y), y ∈ V₀ → y ∈ V₁ → y ∈ W)
    (hts : openOverHomOfLE π hW₀ ≫ t = openOverHomOfLE π hW₁ ≫ s₁) :
    ∃ c : Spec (.of k) ⟶ G.left,
      (∀ (y : Y) (hy : IsClosed ({y} : Set Y)) (_ : y ∈ (Cc : Set Y)) (hy₀ : y ∈ V₀),
        c = (kPointOpen π V₀ y hy hy₀ ≫ t).left) ∧
      (∀ (y : Y) (hy : IsClosed ({y} : Set Y)) (_ : y ∈ (Cc : Set Y)) (hy₁ : y ∈ V₁),
        c = (kPointOpen π V₁ y hy hy₁ ≫ s₁).left) := by
  classical
  let ic := Y.reducedComponentι Cc
  let Zc : Over (Spec (.of k)) := Over.mk (ic ≫ π)
  let P := ic ⁻¹ᵁ V₀
  let Q := ic ⁻¹ᵁ V₁
  have hPQ : P ⊔ Q = ⊤ := by
    refine eq_top_iff.mpr fun z _ => ?_
    have : ic z ∈ V₀ ⊔ V₁ := hcov ▸ trivial
    exact this
  have hmemC : ∀ z, ic z ∈ (Cc : Set Y) := fun z => Y.reducedComponentι_mem Cc z
  obtain ⟨q, hq⟩ := exists_comp_ι_eq W ((P ⊓ Q).ι ≫ ic) (fun z' =>
    hCW _ (hmemC _) z'.2.1 z'.2.2)
  have e₀ : (Y.reducedComponent Cc).homOfLE (inf_le_left : P ⊓ Q ≤ P) ≫ restrictPreimage ic V₀ =
      q ≫ Y.homOfLE hW₀ := by
    rw [← cancel_mono V₀.ι, Category.assoc, restrictPreimage_ι, Category.assoc,
      Scheme.homOfLE_ι, hq, ← Category.assoc, Scheme.homOfLE_ι]
  have e₁ : (Y.reducedComponent Cc).homOfLE (inf_le_right : P ⊓ Q ≤ Q) ≫ restrictPreimage ic V₁ =
      q ≫ Y.homOfLE hW₁ := by
    rw [← cancel_mono V₁.ι, Category.assoc, restrictPreimage_ι, Category.assoc,
      Scheme.homOfLE_ι, hq, ← Category.assoc, Scheme.homOfLE_ι]
  have hts' := congrArg Over.Hom.left hts
  simp only [Over.comp_left, openOverHomOfLE_left] at hts'
  obtain ⟨g, hgP, hgQ⟩ := exists_glue_over_of_sup_eq_top (Z := Zc) (G := G) P Q hPQ
    (restrictPreimage ic V₀ ≫ t.left) (restrictPreimage ic V₁ ≫ s₁.left)
    (by rw [Category.assoc, Over.w t]; exact restrictPreimage_ι_assoc ic V₀ π)
    (by rw [Category.assoc, Over.w s₁]; exact restrictPreimage_ι_assoc ic V₁ π) (by
      change (Y.reducedComponent Cc).homOfLE _ ≫ _ ≫ _ =
        (Y.reducedComponent Cc).homOfLE _ ≫ _ ≫ _
      rw [← Category.assoc, e₀, ← Category.assoc, e₁, Category.assoc, Category.assoc, hts'])
  obtain ⟨c, hc⟩ := exists_eq_comp_of_iso_projectiveLine e G g
  -- the value at the `k`-point of a closed point of the component lying in an open
  have hval : ∀ (V : Y.Opens) (s : openOver π V ⟶ G) (_ : (ic ⁻¹ᵁ V).ι ≫ g.left =
      restrictPreimage ic V ≫ s.left) (y : Y) (hy : IsClosed ({y} : Set Y))
      (_ : y ∈ (Cc : Set Y)) (hyV : y ∈ V), c = (kPointOpen π V y hy hyV ≫ s).left := by
    intro V s hgs y hy hyC hyV
    obtain ⟨z, rfl⟩ : y ∈ Set.range ic := (Y.range_reducedComponentι Cc).symm ▸ hyC
    have hzcl : IsClosed ({z} : Set (Y.reducedComponent Cc)) := by
      have : ({z} : Set (Y.reducedComponent Cc)) = ic ⁻¹' {ic z} := by
        ext z'
        simp only [Set.mem_singleton_iff, Set.mem_preimage]
        exact ⟨fun h => h ▸ rfl, fun h => ic.isClosedEmbedding.injective h⟩
      rw [this]
      exact hy.preimage ic.continuous
    let p := pointOfClosedPoint (ic ≫ π) z hzcl
    have hp : p ≫ ic ≫ π = 𝟙 _ := pointOfClosedPoint_comp (ic ≫ π) z hzcl
    have hpι : p ≫ ic = kPoint π (ic z) hy :=
      eq_kPoint π (ic z) hy (p ≫ ic) (by rw [Category.assoc, hp])
        (congrArg ic (pointOfClosedPoint_apply _ _ _ _))
    obtain ⟨p', hp'⟩ := exists_comp_ι_eq' (ic ⁻¹ᵁ V) p (fun _ => by
      change ic (p _) ∈ V
      rw [pointOfClosedPoint_apply]; exact hyV)
    have hp'r : p' ≫ restrictPreimage ic V = (kPointOpen π V (ic z) hy hyV).left := by
      rw [← cancel_mono V.ι, Category.assoc, restrictPreimage_ι, ← Category.assoc, hp', hpι,
        kPointOpen_left, kPointOpen_left_ι]
    calc c = p ≫ (ic ≫ π) ≫ c := by rw [← Category.assoc, hp, Category.id_comp]
      _ = p ≫ g.left := by rw [hc]; rfl
      _ = p' ≫ (ic ⁻¹ᵁ V).ι ≫ g.left := by rw [← Category.assoc, hp']
      _ = (kPointOpen π V (ic z) hy hyV ≫ s).left := by
        rw [hgs, ← Category.assoc, hp'r, Over.comp_left]
  exact ⟨c, hval V₀ t hgP, hval V₁ s₁ hgQ⟩

/-- A function on `Fin (n + 2)` which is invariant under the rotation `j ↦ j + 1` at every
`j ≠ 0` takes the same value at `0` and `1`. -/
theorem eq_of_forall_ne_zero_finRotate {M : Type*} {n : ℕ} (δ : Fin (n + 2) → M)
    (hδ : ∀ j, j ≠ 0 → δ (finRotate (n + 2) j) = δ j) : δ 0 = δ 1 := by
  have hstep : ∀ r : ℕ, ∀ hr : r + 1 < n + 2, δ ⟨r + 1, hr⟩ = δ 1 := by
    intro r
    induction r with
    | zero => intro hr; rfl
    | succ r ih =>
      intro hr
      have hj : (⟨r + 1, by omega⟩ : Fin (n + 2)) ≠ 0 := by
        intro h; have := congrArg Fin.val h; simp at this
      have hrot : finRotate (n + 2) ⟨r + 1, by omega⟩ = ⟨r + 1 + 1, hr⟩ := by
        rw [finRotate_apply]
        ext
        rw [Fin.val_add_one_of_lt]
        exact (Fin.lt_last_iff_ne_last).mpr fun h => by
          have := congrArg Fin.val h; simp at this; omega
      rw [← hrot, hδ _ hj, ih]
  have hlast : finRotate (n + 2) (Fin.last (n + 1)) = 0 := finRotate_last
  rw [← hlast, hδ _ (by simp [Fin.ext_iff])]
  exact hstep n (by omega)

lemma finRotate_zero_eq_one (n : ℕ) : finRotate (n + 2) 0 = 1 := by
  rw [finRotate_apply, zero_add]

/-- **Going around the loop.** Let `C₀, …, C_{n+1}` be irreducible components of `Y`, each
isomorphic over `k` to `ℙ¹_k`, and `x₀, …, x_{n+1}` closed points with `xᵢ ∈ Cᵢ ∩ C_{i+1}`. Let
`V₀`, `V₁` be opens covering `Y` with `x₀ ∈ V₁` and `xᵢ ∈ V₀` for `i ≠ 0`, and with
`V₀ ∩ V₁ ⊆ W' ∪ W''`, where `W'` does not meet `C₁` and `W''` meets no other `Cᵢ`. If `s₀` over `V₀`
and `s₁` over `V₁` are morphisms to `G` which agree on `W'` and differ by a point `b ∈ G(k)` on
`W''`, then `b = 1`.

On each `Cᵢ`, `s₁` glues with `s₀` (twisted by `b` on `C₁`) to a constant; at the nodes `xᵢ`,
`i ≠ 0`, the untwisted constants agree, as they are values of `s₀`, and at `x₀` the constants of
`C₀` and `C₁` agree, as they are values of `s₁`. Going around the loop the twist must vanish. -/
theorem eq_one_of_loop (n : ℕ) (C : Fin (n + 2) → irreducibleComponents Y)
    (x : Fin (n + 2) → Y) (hC : Function.Injective C) (hxcl : ∀ i, IsClosed ({x i} : Set Y))
    (hmem : ∀ i, x i ∈ (C i : Set Y) ∧ x i ∈ (C (finRotate (n + 2) i) : Set Y))
    (e : ∀ i, Over.mk (Y.reducedComponentι (C i) ≫ π) ≅ Over.mk (projectiveLine k ↘ Spec (.of k)))
    (V₀ V₁ W' W'' : Y.Opens) (hcov : V₀ ⊔ V₁ = ⊤) (hW : V₀ ⊓ V₁ ≤ W' ⊔ W'')
    (h₀' : W' ≤ V₀) (h₁' : W' ≤ V₁) (h₀'' : W'' ≤ V₀) (h₁'' : W'' ≤ V₁)
    (hx₀ : x 0 ∈ V₁) (hV₀ : ∀ i, i ≠ 0 → x i ∈ V₀)
    (hW'C : ∀ y ∈ W', y ∉ (C 1 : Set Y))
    (hW''C : ∀ i, C i ≠ C 1 → ∀ y ∈ W'', y ∉ (C i : Set Y))
    (s₀ : openOver π V₀ ⟶ G) (s₁ : openOver π V₁ ⟶ G) (b : 𝟙_ (Over (Spec (.of k))) ⟶ G)
    (h' : openOverHomOfLE π h₁' ≫ s₁ = openOverHomOfLE π h₀' ≫ s₀)
    (h'' : openOverHomOfLE π h₁'' ≫ s₁ = openOverHomOfLE π h₀'' ≫ (s₀ * (toUnit _ ≫ b))) :
    b = 1 := by
  classical
  let t : Fin (n + 2) → (openOver π V₀ ⟶ G) := fun i =>
    if C i = C 1 then s₀ * (toUnit _ ≫ b) else s₀
  have key : ∀ i, ∃ c : Spec (.of k) ⟶ G.left,
      (∀ (y : Y) (hy : IsClosed ({y} : Set Y)) (_ : y ∈ (C i : Set Y)) (hy₀ : y ∈ V₀),
        c = (kPointOpen π V₀ y hy hy₀ ≫ t i).left) ∧
      (∀ (y : Y) (hy : IsClosed ({y} : Set Y)) (_ : y ∈ (C i : Set Y)) (hy₁ : y ∈ V₁),
        c = (kPointOpen π V₁ y hy hy₁ ≫ s₁).left) := by
    intro i
    by_cases hi : C i = C 1
    · refine exists_const_of_agree π G (C i) (e i) V₀ V₁ hcov (t i) s₁ W'' h₀'' h₁''
        (fun y hyC hy₀ hy₁ => ?_) ?_
      · rcases (TopologicalSpace.Opens.mem_sup.mp (hW ⟨hy₀, hy₁⟩)) with h | h
        · exact absurd (hi ▸ hyC) (hW'C y h)
        · exact h
      · simp only [t, ite_eq_left hi]
        exact h''.symm
    · refine exists_const_of_agree π G (C i) (e i) V₀ V₁ hcov (t i) s₁ W' h₀' h₁'
        (fun y hyC hy₀ hy₁ => ?_) ?_
      · rcases (TopologicalSpace.Opens.mem_sup.mp (hW ⟨hy₀, hy₁⟩)) with h | h
        · exact h
        · exact absurd hyC (hW''C i hi y h)
      · simp only [t, ite_eq_right hi]
        exact h'.symm
  choose c hc₀ hc₁ using key
  -- the values as points of `G`
  have hcG : ∀ i, c i ≫ G.hom = 𝟙 _ := by
    intro i
    by_cases hi : i = 0
    · subst hi
      rw [hc₁ 0 (x 0) (hxcl 0) (hmem 0).1 hx₀, Over.w]
      rfl
    · rw [hc₀ i (x i) (hxcl i) (hmem i).1 (hV₀ i hi), Over.w]
      rfl
  let ĉ : Fin (n + 2) → (𝟙_ (Over (Spec (.of k))) ⟶ G) := fun i => Over.homMk (c i) (hcG i)
  have hĉ : ∀ i (v : 𝟙_ (Over (Spec (.of k))) ⟶ G), c i = v.left → ĉ i = v := fun i v h =>
    Over.OverMorphism.ext h
  have htwist : ∀ (p : 𝟙_ (Over (Spec (.of k))) ⟶ openOver π V₀),
      p ≫ (s₀ * (toUnit _ ≫ b)) = p ≫ s₀ * b := by
    intro p
    rw [MonObj.comp_mul, ← Category.assoc p, toUnit_unique (p ≫ toUnit _) (𝟙 _),
      Category.id_comp]
  let δ : Fin (n + 2) → (𝟙_ (Over (Spec (.of k))) ⟶ G) := fun i =>
    if C i = C 1 then ĉ i * b⁻¹ else ĉ i
  have hδ : ∀ i (y : Y) (hy : IsClosed ({y} : Set Y)) (_ : y ∈ (C i : Set Y)) (hy₀ : y ∈ V₀),
      δ i = kPointOpen π V₀ y hy hy₀ ≫ s₀ := by
    intro i y hy hyC hy₀
    have h := hĉ i _ (hc₀ i y hy hyC hy₀)
    by_cases hi : C i = C 1
    · simp only [δ, ite_eq_left hi, h, t, htwist, mul_inv_cancel_right]
    · simp only [δ, ite_eq_right hi, h, t]
  have hrot : ∀ j, j ≠ 0 → δ (finRotate (n + 2) j) = δ j := fun j hj =>
    (hδ _ (x j) (hxcl j) (hmem j).2 (hV₀ j hj)).trans
      (hδ j (x j) (hxcl j) (hmem j).1 (hV₀ j hj)).symm
  have h01 := eq_of_forall_ne_zero_finRotate δ hrot
  have hC01 : C 0 ≠ C 1 := fun h => by
    have := hC h
    simp at this
  have hĉ01 : ĉ 0 = ĉ 1 := by
    have e₀ := hĉ 0 _ (hc₁ 0 (x 0) (hxcl 0) (hmem 0).1 hx₀)
    have e₁ := hĉ 1 _ (hc₁ 1 (x 0) (hxcl 0)
      ((finRotate_zero_eq_one n) ▸ (hmem 0).2) hx₀)
    rw [e₀, e₁]
  simp only [δ, ite_eq_right hC01, ite_eq_left rfl, hĉ01] at h01
  have : b⁻¹ = 1 := by
    have h' := h01.symm
    rwa [mul_eq_left] at h'
  exact inv_eq_one.mp this

end Loop

end Stacks.Examples.NonAlgebraicHomStack

end
