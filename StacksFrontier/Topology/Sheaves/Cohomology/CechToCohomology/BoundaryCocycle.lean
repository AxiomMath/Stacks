module

public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.RefinementOfACovering
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.DegreeOneComparison

/-!
# The Čech boundary map of a short exact sequence of abelian sheaves

Let `0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` be a short exact sequence of abelian sheaves on a topological space
`X`, and let `τ ∈ ℱ₃(W)` be a section that lifts to `ℱ₂` over every member of an open covering
`𝒰` of `W`. Choosing such lifts `τ̃`, the assignment

  `(i₀, i₁) ↦ τ̃_{i₀}|_{U_{i₀i₁}} - τ̃_{i₁}|_{U_{i₀i₁}}`

is a `1`-coboundary in the Čech complex of `ℱ₂` which takes values in `ℱ₁`. Such a covering with
such lifts exists, the assignment is a `1`-cocycle of `ℱ₁`, its class in `Ȟ¹(𝒰, ℱ₁)` does not
depend on the chosen lifts, and on a common refinement it does not depend on the chosen covering
either. That class is the boundary map `δ(τ)` of Stacks 02AP, and it is additive in `τ`.

The assignment above is `deltaCochain`. It is the *negative* of the Čech coboundary
`cechD U ℱ₂ 0 τ̃`: with the differential `(d t)_{i₀i₁} = t_{i₁} - t_{i₀}` of Stacks 01FG, the
coboundary of the lifts is `(i₀, i₁) ↦ τ̃_{i₁} - τ̃_{i₀}` (`deltaCochain_eq_neg_cechD`). The
statements phrased with `cechD U ℱ₂ 0 τ̃` (`exists_cocycle_of_localLifts` and the class lemmas
next to it) therefore describe the cocycle of `-δ(τ)`, the opposite-sign convention; the
statements phrased with `deltaCochain` (`exists_cocycle_deltaCochain_of_localLifts` and the
`…_deltaCochain` class lemmas) describe the cocycle of `δ(τ)` with the sign of the source.

The statements are about abelian presheaves and take the exactness properties they use as
hypotheses: injectivity of `ℱ₁(V) → ℱ₂(V)` for every open `V`, exactness of
`ℱ₁(V) → ℱ₂(V) → ℱ₃(V)` in the middle, and, for the existence of a covering with lifts, local
surjectivity of `ℱ₂ → ℱ₃` for the topology of open covers. A short exact sequence of abelian
sheaves satisfies all three (`TopCat.Sheaf.isLocallySurjective_iff_epi`). Čech degree `0` is
indexed by `Fin 1 → I`.

## Main results

* `Stacks.Cohomology.CechBoundary.exists_covering_localLifts`: a locally surjective `ℱ₂ → ℱ₃`
  gives every section of `ℱ₃` over `W` an open covering of `W` and a `0`-cochain of `ℱ₂` lifting
  its restrictions.
* `Stacks.Cohomology.CechBoundary.exists_cocycle_deltaCochain_of_localLifts`: the cochain
  `(i₀, i₁) ↦ τ̃_{i₀} - τ̃_{i₁}` of a `0`-cochain of lifts is the image of a `1`-cocycle of `ℱ₁`;
  `cls_eq_of_push_eq_deltaCochain`, `cls_add_of_push_eq_deltaCochain`,
  `cls_eq_of_refinement_of_push_eq_deltaCochain` and
  `exists_common_refinement_cls_eq_of_push_eq_deltaCochain` are the well-definedness, additivity
  and independence statements for its class `δ(τ)`.
* `Stacks.Cohomology.CechBoundary.exists_cocycle_of_localLifts`: the coboundary of a `0`-cochain
  of lifts, which is `-deltaCochain`, is the image of a `1`-cocycle of `ℱ₁`; the class lemmas
  below are stated for this cocycle, so they are about `-δ(τ)`.
* `Stacks.Cohomology.CechBoundary.cls_eq_of_localLifts`: two systems of lifts of the same section
  give `1`-cocycles with the same class in `Ȟ¹(𝒰, ℱ₁)`.
* `Stacks.Cohomology.CechBoundary.cls_add_of_localLifts`: the class attached to a sum of sections
  is the sum of the classes.
* `Stacks.Cohomology.CechBoundary.cls_eq_of_refinement_of_localLifts`: two coverings of `W`, each
  with lifts of the same `τ`, give classes with the same image in `Ȟ¹(𝒱, ℱ₁)` for every common
  refinement `𝒱`.
* `Stacks.Cohomology.CechBoundary.exists_common_refinement_cls_eq_of_localLifts`: two coverings
  of `W` with lifts of the same `τ` have a common refinement, the family of pairwise
  intersections, on which the two classes agree.
* `Stacks.Cohomology.CechBoundary.injective_push`: a morphism of presheaves injective on
  sections induces an injective map of Čech cochains in every degree.
* `Stacks.Cohomology.CechBoundary.cechD_eq_zero_of_restr`: a `0`-cochain whose components are
  restrictions of a single section is a cocycle.
* `Stacks.Cohomology.CechOne.push_refinementMap`: pushing a Čech cochain along a morphism of
  presheaves commutes with refining the covering.

## References

* [Stacks Project, Tag 02AP](https://stacks.math.columbia.edu/tag/02AP)
* [Stacks Project, Tag 01FJ](https://stacks.math.columbia.edu/tag/01FJ)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe v w w' w'' uX

namespace Stacks.Cohomology.CechOne

open CechCochains

variable {X : TopCat.{uX}} {I : Type w} {K : Type w'} (U : I → Opens X) (V : K → Opens X)
  (r : K → I) (hr : ∀ k, V k ≤ U (r k))

/-- Pushing a Čech cochain along a morphism of presheaves commutes with refining the
covering. -/
theorem push_refinementMap {P Q : TopCat.Presheaf AddCommGrpCat.{v} X} (χ : P ⟶ Q) (p : ℕ)
    (s : Cochain U P p) :
    push V χ p (refinementMap U V r hr P p s) = refinementMap U V r hr Q p (push U χ p s) := by
  funext j
  rw [push_apply, refinementMap_apply, refinementMap_apply, push_apply, restr_app]

end Stacks.Cohomology.CechOne

namespace Stacks.Cohomology.CechBoundary

open CechCochains CechOne

variable {X : TopCat.{uX}} {I : Type w} (U : I → Opens X)
  {ℱ₁ ℱ₂ ℱ₃ : TopCat.Presheaf AddCommGrpCat.{v} X} (φ : ℱ₁ ⟶ ℱ₂) (ψ : ℱ₂ ⟶ ℱ₃)

/-- A morphism of abelian presheaves injective on sections over every open induces an injective
map of Čech cochains in every degree. -/
theorem injective_push (hφ : ∀ V : Opens X, Function.Injective (φ.app (op V))) (p : ℕ) :
    Function.Injective (push U φ p) := by
  intro s t hst
  funext i
  refine hφ _ ?_
  rw [← push_apply U φ p s i, ← push_apply U φ p t i, hst]

/-- If every component of the `0`-cochain `t` is the restriction of a single `x : ℱ(W)`, then
`d⁰ t = 0`. -/
theorem cechD_eq_zero_of_restr {ℱ : TopCat.Presheaf AddCommGrpCat.{v} X} {W : Opens X}
    (x : ToType (ℱ.obj (op W))) (hle : ∀ i : Fin 1 → I, inter U i ≤ W) (t : Cochain U ℱ 0)
    (ht : ∀ i, t i = restr ℱ (hle i) x) : cechD U ℱ 0 t = 0 := by
  funext i
  rw [Cochain.zero_apply, cechD_apply, Fin.sum_univ_two, ht, ht, restr_restr, restr_restr,
    Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul, add_neg_cancel]

/-- If `ψ : ℱ₂ ⟶ ℱ₃` is locally surjective for the topology of open covers, then every section `τ`
of `ℱ₃` over an open `W` admits an open covering of `W` together with a `0`-cochain of `ℱ₂`
lifting the restrictions of `τ`. -/
@[stacks 02AP "existence of a covering with lifts"]
theorem exists_covering_localLifts {W : Opens X} (τ : ToType (ℱ₃.obj (op W)))
    (hψ : CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) ψ) :
    ∃ (I₀ : Type uX) (U₀ : I₀ → Opens X) (hU₀ : W = ⨆ i, U₀ i) (lift : Cochain U₀ ℱ₂ 0),
      ∀ i : Fin 1 → I₀,
        ψ.app (op (inter U₀ i)) (lift i) = restr ℱ₃ (inter_le_of_eq_iSup hU₀ i) τ := by
  classical
  have hloc : ∀ y : X, y ∈ W → ∃ (V : Opens X) (hV : V ≤ W), y ∈ V ∧
      ∃ b : ToType (ℱ₂.obj (op V)), ψ.app (op V) b = restr ℱ₃ hV τ := by
    intro y hy
    obtain ⟨V, f, ⟨b, hb⟩, hyV⟩ :=
      CategoryTheory.Presheaf.imageSieve_mem (Opens.grothendieckTopology X) ψ
        (U := op W) τ y hy
    refine ⟨V, leOfHom f, hyV, b, hb.trans ?_⟩
    rw [restr, Subsingleton.elim (homOfLE (leOfHom f)) f]
  choose U₀ hU₀le hU₀mem using fun y : {y : X // y ∈ W} => hloc y.1 y.2
  choose b hb using fun y => (hU₀mem y).2
  have hU₀ : W = ⨆ y : {y : X // y ∈ W}, U₀ y := by
    refine le_antisymm (fun z hz => ?_) (iSup_le fun y => hU₀le y)
    exact Opens.mem_iSup.mpr ⟨⟨z, hz⟩, (hU₀mem ⟨z, hz⟩).1⟩
  refine ⟨{y : X // y ∈ W}, U₀, hU₀,
    fun i => restr ℱ₂ (inter_le U₀ i 0) (b (i 0)), fun i => ?_⟩
  rw [← restr_app ψ (inter_le U₀ i 0) (b (i 0)), hb, restr_restr]

variable {W : Opens X} (hle : ∀ i : Fin 1 → I, inter U i ≤ W)
  {τ : ToType (ℱ₃.obj (op W))} {lift : Cochain U ℱ₂ 0}

/-- Let `φ : ℱ₁ ⟶ ℱ₂` be injective on sections and `ℱ₁ → ℱ₂ → ℱ₃` exact in the middle on
sections. If `τ` is a section of `ℱ₃` over `W` and `lift` is a `0`-cochain of `ℱ₂` lifting the
restrictions of `τ`, then the coboundary of `lift` is the image of a `1`-cocycle of `ℱ₁`.

The coboundary `(cechD U ℱ₂ 0 lift)(i₀, i₁) = lift_{i₁} - lift_{i₀}` is the negative of the
cochain of Stacks 02AP, so the class of this cocycle is `-δ(τ)`; the source's sign is
`exists_cocycle_deltaCochain_of_localLifts`. -/
theorem exists_cocycle_of_localLifts
    (hmono : ∀ V : Opens X, Function.Injective (φ.app (op V)))
    (hexact : ∀ (V : Opens X) (b : ToType (ℱ₂.obj (op V))), ψ.app (op V) b = 0 →
      ∃ a, φ.app (op V) a = b)
    (hlift : ∀ i, ψ.app (op (inter U i)) (lift i) = restr ℱ₃ (hle i) τ) :
    ∃ c : cocycles1 U ℱ₁, push U φ 1 (c : Cochain U ℱ₁ 1) = cechD U ℱ₂ 0 lift := by
  classical
  have hψ : push U ψ 1 (cechD U ℱ₂ 0 lift) = 0 := (push_cechD U ψ 0 lift).trans <|
    cechD_eq_zero_of_restr U τ hle _ fun i => by rw [push_apply, hlift]
  have hcomp : ∀ i : Fin 2 → I, ψ.app (op (inter U i)) (cechD U ℱ₂ 0 lift i) = 0 := fun i => by
    rw [← push_apply U ψ 1, hψ, Cochain.zero_apply]
  choose c hc using fun i : Fin 2 → I => hexact _ _ (hcomp i)
  have hmap : push U φ 1 c = cechD U ℱ₂ 0 lift :=
    funext fun i => (push_apply U φ 1 c i).trans (hc i)
  refine ⟨⟨c, ?_⟩, hmap⟩
  refine injective_push U φ hmono 2 ((push_cechD U φ 1 c).trans ?_)
  rw [map_zero, hmap]
  exact cechD_cechD U ℱ₂ 0 lift

/-- Let `φ : ℱ₁ ⟶ ℱ₂` be injective on sections and `ℱ₁ → ℱ₂ → ℱ₃` exact in the middle on
sections. Two systems of lifts of the same section give `1`-cocycles of `ℱ₁` with the same class
in `Ȟ¹(𝒰, ℱ₁)`. The cocycles here are those of `exists_cocycle_of_localLifts`, of class `-δ(τ)`;
`cls_eq_of_push_eq_deltaCochain` is the same statement with the sign of Stacks 02AP. -/
theorem cls_eq_of_localLifts
    (hmono : ∀ V : Opens X, Function.Injective (φ.app (op V)))
    (hexact : ∀ (V : Opens X) (b : ToType (ℱ₂.obj (op V))), ψ.app (op V) b = 0 →
      ∃ a, φ.app (op V) a = b)
    {lift' : Cochain U ℱ₂ 0}
    (hlift : ∀ i, ψ.app (op (inter U i)) (lift i) = restr ℱ₃ (hle i) τ)
    (hlift' : ∀ i, ψ.app (op (inter U i)) (lift' i) = restr ℱ₃ (hle i) τ)
    {c c' : cocycles1 U ℱ₁}
    (hc : push U φ 1 (c : Cochain U ℱ₁ 1) = cechD U ℱ₂ 0 lift)
    (hc' : push U φ 1 (c' : Cochain U ℱ₁ 1) = cechD U ℱ₂ 0 lift') :
    cls U ℱ₁ c = cls U ℱ₁ c' := by
  classical
  have hzero : ∀ i : Fin 1 → I, ψ.app (op (inter U i)) (lift' i - lift i) = 0 := fun i => by
    rw [map_sub, hlift, hlift', sub_self]
  choose b hb using fun i : Fin 1 → I => hexact _ _ (hzero i)
  have hmap : push U φ 0 b = lift' - lift :=
    funext fun i => (push_apply U φ 0 b i).trans (hb i)
  have key : cechD U ℱ₁ 0 b = (c' : Cochain U ℱ₁ 1) - (c : Cochain U ℱ₁ 1) := by
    refine injective_push U φ hmono 1 ((push_cechD U φ 0 b).trans ?_)
    rw [hmap, map_sub, map_sub, hc, hc']
  have h0 : cls U ℱ₁ (c' - c) = 0 :=
    (cls_eq_zero_iff U ℱ₁ (c' - c)).mpr ⟨b, by rw [key]; rfl⟩
  rw [cls, QuotientAddGroup.mk_sub, sub_eq_zero] at h0
  exact h0.symm

/-- Let `φ : ℱ₁ ⟶ ℱ₂` be injective on sections. The class attached to the sum of two systems of
local lifts is the sum of the two classes. The cocycles here are those of
`exists_cocycle_of_localLifts`, of class `-δ(τ)`; `cls_add_of_push_eq_deltaCochain` is the same
statement with the sign of Stacks 02AP. -/
theorem cls_add_of_localLifts
    (hmono : ∀ V : Opens X, Function.Injective (φ.app (op V)))
    {lift' : Cochain U ℱ₂ 0} {c c' d : cocycles1 U ℱ₁}
    (hc : push U φ 1 (c : Cochain U ℱ₁ 1) = cechD U ℱ₂ 0 lift)
    (hc' : push U φ 1 (c' : Cochain U ℱ₁ 1) = cechD U ℱ₂ 0 lift')
    (hd : push U φ 1 (d : Cochain U ℱ₁ 1) = cechD U ℱ₂ 0 (lift + lift')) :
    cls U ℱ₁ d = cls U ℱ₁ c + cls U ℱ₁ c' := by
  have hcoe : ((c + c' : cocycles1 U ℱ₁) : Cochain U ℱ₁ 1) = (c : Cochain U ℱ₁ 1) + c' := rfl
  have hsum : d = c + c' := by
    refine Subtype.ext (injective_push U φ hmono 1 ?_)
    rw [hd, hcoe, map_add (push U φ 1), hc, hc']
    exact map_add _ _ _
  rw [hsum, cls, cls, cls, QuotientAddGroup.mk_add]

/-- Adding two systems of local lifts lifts the sum of the two sections. -/
theorem add_lifts_add {τ' : ToType (ℱ₃.obj (op W))} {lift' : Cochain U ℱ₂ 0}
    (hlift : ∀ i, ψ.app (op (inter U i)) (lift i) = restr ℱ₃ (hle i) τ)
    (hlift' : ∀ i, ψ.app (op (inter U i)) (lift' i) = restr ℱ₃ (hle i) τ') :
    ∀ i, ψ.app (op (inter U i)) ((lift + lift') i) = restr ℱ₃ (hle i) (τ + τ') := fun i => by
  rw [Cochain.add_apply, map_add, hlift, hlift', map_add]

/-! ### Independence of the covering -/

variable {I' : Type w'} {K : Type w''}

/-- Let `φ : ℱ₁ ⟶ ℱ₂` be injective on sections and `ℱ₁ → ℱ₂ → ℱ₃` exact in the middle on
sections. Let `𝒰` and `𝒰'` be two families of opens over `W`, each carrying a system of lifts of
the same section `τ` of `ℱ₃`, and let `𝒱` be a common refinement of the two: a family of opens
with refinement functions into the index sets of `𝒰` and of `𝒰'`. Then the two classes attached
to `τ` have the same image in `Ȟ¹(𝒱, ℱ₁)`. The cocycles here are those of
`exists_cocycle_of_localLifts`, of class `-δ(τ)`; `cls_eq_of_refinement_of_push_eq_deltaCochain`
is the same statement with the sign of Stacks 02AP. -/
theorem cls_eq_of_refinement_of_localLifts
    (U' : I' → Opens X) (V : K → Opens X)
    (r : K → I) (hr : ∀ k, V k ≤ U (r k))
    (r' : K → I') (hr' : ∀ k, V k ≤ U' (r' k))
    (hle' : ∀ i : Fin 1 → I', inter U' i ≤ W)
    (hmono : ∀ V₀ : Opens X, Function.Injective (φ.app (op V₀)))
    (hexact : ∀ (V₀ : Opens X) (b : ToType (ℱ₂.obj (op V₀))), ψ.app (op V₀) b = 0 →
      ∃ a, φ.app (op V₀) a = b)
    {lift' : Cochain U' ℱ₂ 0}
    (hlift : ∀ i, ψ.app (op (inter U i)) (lift i) = restr ℱ₃ (hle i) τ)
    (hlift' : ∀ i, ψ.app (op (inter U' i)) (lift' i) = restr ℱ₃ (hle' i) τ)
    {c : cocycles1 U ℱ₁} {c' : cocycles1 U' ℱ₁}
    (hc : push U φ 1 (c : Cochain U ℱ₁ 1) = cechD U ℱ₂ 0 lift)
    (hc' : push U' φ 1 (c' : Cochain U' ℱ₁ 1) = cechD U' ℱ₂ 0 lift') :
    refinementCechH1 U V r hr ℱ₁ (cls U ℱ₁ c) =
      refinementCechH1 U' V r' hr' ℱ₁ (cls U' ℱ₁ c') := by
  have hleV : ∀ j : Fin 1 → K, inter V j ≤ W := fun j =>
    (inter_le_inter_comp U V r hr j).trans (hle (r ∘ j))
  have hliftV : ∀ j, ψ.app (op (inter V j)) (refinementMap U V r hr ℱ₂ 0 lift j) =
      restr ℱ₃ (hleV j) τ := fun j => by
    rw [refinementMap_apply, ← restr_app ψ (inter_le_inter_comp U V r hr j) (lift (r ∘ j)),
      hlift, restr_restr]
  have hliftV' : ∀ j, ψ.app (op (inter V j)) (refinementMap U' V r' hr' ℱ₂ 0 lift' j) =
      restr ℱ₃ (hleV j) τ := fun j => by
    rw [refinementMap_apply, ← restr_app ψ (inter_le_inter_comp U' V r' hr' j) (lift' (r' ∘ j)),
      hlift', restr_restr]
  have hcV : push V φ 1
      ((refinementCocycles1 U V r hr ℱ₁ c : cocycles1 V ℱ₁) : Cochain V ℱ₁ 1) =
      cechD V ℱ₂ 0 (refinementMap U V r hr ℱ₂ 0 lift) := by
    rw [refinementCocycles1_coe, push_refinementMap, hc, refinementMap_cechD]
  have hcV' : push V φ 1
      ((refinementCocycles1 U' V r' hr' ℱ₁ c' : cocycles1 V ℱ₁) : Cochain V ℱ₁ 1) =
      cechD V ℱ₂ 0 (refinementMap U' V r' hr' ℱ₂ 0 lift') := by
    rw [refinementCocycles1_coe, push_refinementMap, hc', refinementMap_cechD]
  rw [refinementCechH1_cls, refinementCechH1_cls]
  exact cls_eq_of_localLifts V φ ψ hleV hmono hexact hliftV hliftV' hcV hcV'

/-- Let `φ : ℱ₁ ⟶ ℱ₂` be injective on sections and `ℱ₁ → ℱ₂ → ℱ₃` exact in the middle on
sections. Two families of opens covering `W`, each carrying a system of lifts of the same section
`τ` of `ℱ₃`, admit a common refinement covering `W`, the family of their pairwise intersections,
on which the two classes attached to `τ` agree. The cocycles here are those of
`exists_cocycle_of_localLifts`, of class `-δ(τ)`;
`exists_common_refinement_cls_eq_of_push_eq_deltaCochain` is the same statement with the sign of
Stacks 02AP. -/
theorem exists_common_refinement_cls_eq_of_localLifts
    (U' : I' → Opens X) (hU : W = ⨆ i, U i) (hU' : W = ⨆ i', U' i')
    (hmono : ∀ V₀ : Opens X, Function.Injective (φ.app (op V₀)))
    (hexact : ∀ (V₀ : Opens X) (b : ToType (ℱ₂.obj (op V₀))), ψ.app (op V₀) b = 0 →
      ∃ a, φ.app (op V₀) a = b)
    {lift' : Cochain U' ℱ₂ 0}
    (hlift : ∀ i, ψ.app (op (inter U i)) (lift i) = restr ℱ₃ (inter_le_of_eq_iSup hU i) τ)
    (hlift' : ∀ i, ψ.app (op (inter U' i)) (lift' i) = restr ℱ₃ (inter_le_of_eq_iSup hU' i) τ)
    {c : cocycles1 U ℱ₁} {c' : cocycles1 U' ℱ₁}
    (hc : push U φ 1 (c : Cochain U ℱ₁ 1) = cechD U ℱ₂ 0 lift)
    (hc' : push U' φ 1 (c' : Cochain U' ℱ₁ 1) = cechD U' ℱ₂ 0 lift') :
    ∃ (V : I × I' → Opens X) (r : I × I' → I) (hr : ∀ k, V k ≤ U (r k))
      (r' : I × I' → I') (hr' : ∀ k, V k ≤ U' (r' k)),
      W = ⨆ k, V k ∧
        refinementCechH1 U V r hr ℱ₁ (cls U ℱ₁ c) =
          refinementCechH1 U' V r' hr' ℱ₁ (cls U' ℱ₁ c') := by
  refine ⟨fun p => U p.1 ⊓ U' p.2, Prod.fst, fun _ => inf_le_left, Prod.snd,
    fun _ => inf_le_right, eq_iSup_inf_of_eq_iSup U hU hU', ?_⟩
  exact cls_eq_of_refinement_of_localLifts U φ ψ (inter_le_of_eq_iSup hU) U' _ _ _ _ _
    (inter_le_of_eq_iSup hU') hmono hexact hlift hlift' hc hc'

/-! ### The cocycle with the sign of Stacks 02AP -/

/-- The intersection `U_{i₀i₁}` of a pair of indices lies in the member `U_{i_a}`, written as
the intersection of the one-term tuple `(i_a)`. -/
theorem inter_le_inter_const (i : Fin 2 → I) (a : Fin 2) :
    inter U i ≤ inter U (fun _ : Fin 1 => i a) :=
  le_iInf fun _ => iInf_le (fun k => U (i k)) a

/-- The Čech `1`-cochain `(i₀, i₁) ↦ τ̃_{i₀}|_{U_{i₀i₁}} - τ̃_{i₁}|_{U_{i₀i₁}}` attached to a
`0`-cochain `τ̃`: the assignment of Stacks 02AP. It is the negative of the Čech coboundary of `τ̃`
(`deltaCochain_eq_neg_cechD`). -/
@[stacks 02AP "the assignment `(i₀, i₁) ↦ τ̃_{i₀}|_{U_{i₀i₁}} - τ̃_{i₁}|_{U_{i₀i₁}}`"]
def deltaCochain {ℱ : TopCat.Presheaf AddCommGrpCat.{v} X} (t : Cochain U ℱ 0) :
    Cochain U ℱ 1 := fun i =>
  restr ℱ (inter_le_inter_const U i 0) (t fun _ => i 0) -
    restr ℱ (inter_le_inter_const U i 1) (t fun _ => i 1)

/-- The value of `deltaCochain` at a pair of indices `(i₀, i₁)` is `τ̃_{i₀} - τ̃_{i₁}`. -/
theorem deltaCochain_apply {ℱ : TopCat.Presheaf AddCommGrpCat.{v} X} (t : Cochain U ℱ 0)
    (i : Fin 2 → I) :
    deltaCochain U t i =
      restr ℱ (inter_le_inter_const U i 0) (t fun _ => i 0) -
        restr ℱ (inter_le_inter_const U i 1) (t fun _ => i 1) := rfl

/-- Restrictions of the values of a `0`-cochain at equal index tuples agree. -/
theorem restr_cochain_congr {ℱ : TopCat.Presheaf AddCommGrpCat.{v} X} (t : Cochain U ℱ 0)
    {a b : Fin 1 → I} (hab : a = b) {V : Opens X} (ha : V ≤ inter U a) (hb : V ≤ inter U b) :
    restr ℱ ha (t a) = restr ℱ hb (t b) := by
  subst hab
  rfl

/-- The cochain `(i₀, i₁) ↦ τ̃_{i₀} - τ̃_{i₁}` of Stacks 02AP is the negative of the Čech
coboundary of `τ̃`, whose value at `(i₀, i₁)` is `τ̃_{i₁} - τ̃_{i₀}`. -/
theorem deltaCochain_eq_neg_cechD {ℱ : TopCat.Presheaf AddCommGrpCat.{v} X}
    (t : Cochain U ℱ 0) : deltaCochain U t = -cechD U ℱ 0 t := by
  funext i
  have h0 : i ∘ (0 : Fin 2).succAbove = fun _ => i 1 :=
    funext fun k => by rw [Subsingleton.elim k 0]; rfl
  have h1 : i ∘ (1 : Fin 2).succAbove = fun _ => i 0 :=
    funext fun k => by rw [Subsingleton.elim k 0]; rfl
  rw [deltaCochain_apply, Cochain.neg_apply, cechD_apply, Fin.sum_univ_two, Fin.val_zero,
    Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul,
    restr_cochain_congr U t h0 (inter_le_omit U i 0) (inter_le_inter_const U i 1),
    restr_cochain_congr U t h1 (inter_le_omit U i 1) (inter_le_inter_const U i 0)]
  abel

/-- A cocycle whose image is `deltaCochain` of the lifts has negative with image the Čech
coboundary of the lifts. -/
theorem push_neg_eq_cechD_of_push_eq_deltaCochain {c : cocycles1 U ℱ₁}
    (hc : push U φ 1 (c : Cochain U ℱ₁ 1) = deltaCochain U lift) :
    push U φ 1 ((-c : cocycles1 U ℱ₁) : Cochain U ℱ₁ 1) = cechD U ℱ₂ 0 lift := by
  change push U φ 1 (-(c : Cochain U ℱ₁ 1)) = _
  rw [map_neg, hc, deltaCochain_eq_neg_cechD, neg_neg]

/-- **Stacks 02AP, the cocycle.** Let `φ : ℱ₁ ⟶ ℱ₂` be injective on sections and
`ℱ₁ → ℱ₂ → ℱ₃` exact in the middle on sections. If `τ` is a section of `ℱ₃` over `W` and `τ̃` is a
`0`-cochain of `ℱ₂` lifting the restrictions of `τ`, then the cochain
`(i₀, i₁) ↦ τ̃_{i₀}|_{U_{i₀i₁}} - τ̃_{i₁}|_{U_{i₀i₁}}` is the image of a `1`-cocycle of `ℱ₁`. -/
@[stacks 02AP "the cocycle `(i₀, i₁) ↦ τ̃_{i₀} - τ̃_{i₁}` with values in `ℱ₁`"]
theorem exists_cocycle_deltaCochain_of_localLifts
    (hmono : ∀ V : Opens X, Function.Injective (φ.app (op V)))
    (hexact : ∀ (V : Opens X) (b : ToType (ℱ₂.obj (op V))), ψ.app (op V) b = 0 →
      ∃ a, φ.app (op V) a = b)
    (hlift : ∀ i, ψ.app (op (inter U i)) (lift i) = restr ℱ₃ (hle i) τ) :
    ∃ c : cocycles1 U ℱ₁, push U φ 1 (c : Cochain U ℱ₁ 1) = deltaCochain U lift := by
  obtain ⟨c, hc⟩ := exists_cocycle_of_localLifts U φ ψ hle hmono hexact hlift
  refine ⟨-c, ?_⟩
  change push U φ 1 (-(c : Cochain U ℱ₁ 1)) = _
  rw [map_neg, hc, deltaCochain_eq_neg_cechD]

/-- **Stacks 02AP, independence of the lifts.** Let `φ : ℱ₁ ⟶ ℱ₂` be injective on sections and
`ℱ₁ → ℱ₂ → ℱ₃` exact in the middle on sections. Two systems of lifts of the same section give
cocycles `(i₀, i₁) ↦ τ̃_{i₀} - τ̃_{i₁}` with the same class in `Ȟ¹(𝒰, ℱ₁)`. -/
@[stacks 02AP "the class `δ(τ)` does not depend on the lifts"]
theorem cls_eq_of_push_eq_deltaCochain
    (hmono : ∀ V : Opens X, Function.Injective (φ.app (op V)))
    (hexact : ∀ (V : Opens X) (b : ToType (ℱ₂.obj (op V))), ψ.app (op V) b = 0 →
      ∃ a, φ.app (op V) a = b)
    {lift' : Cochain U ℱ₂ 0}
    (hlift : ∀ i, ψ.app (op (inter U i)) (lift i) = restr ℱ₃ (hle i) τ)
    (hlift' : ∀ i, ψ.app (op (inter U i)) (lift' i) = restr ℱ₃ (hle i) τ)
    {c c' : cocycles1 U ℱ₁}
    (hc : push U φ 1 (c : Cochain U ℱ₁ 1) = deltaCochain U lift)
    (hc' : push U φ 1 (c' : Cochain U ℱ₁ 1) = deltaCochain U lift') :
    cls U ℱ₁ c = cls U ℱ₁ c' := by
  have h := cls_eq_of_localLifts U φ ψ hle hmono hexact hlift hlift'
    (push_neg_eq_cechD_of_push_eq_deltaCochain U φ hc)
    (push_neg_eq_cechD_of_push_eq_deltaCochain U φ hc')
  rwa [cls, cls, QuotientAddGroup.mk_neg, QuotientAddGroup.mk_neg, neg_inj] at h

/-- **Stacks 02AP, additivity of `δ`.** Let `φ : ℱ₁ ⟶ ℱ₂` be injective on sections. The class of
the cocycle `(i₀, i₁) ↦ τ̃_{i₀} - τ̃_{i₁}` attached to the sum of two systems of local lifts is the
sum of the two classes. -/
@[stacks 02AP "additivity of the boundary map `δ`"]
theorem cls_add_of_push_eq_deltaCochain
    (hmono : ∀ V : Opens X, Function.Injective (φ.app (op V)))
    {lift' : Cochain U ℱ₂ 0} {c c' d : cocycles1 U ℱ₁}
    (hc : push U φ 1 (c : Cochain U ℱ₁ 1) = deltaCochain U lift)
    (hc' : push U φ 1 (c' : Cochain U ℱ₁ 1) = deltaCochain U lift')
    (hd : push U φ 1 (d : Cochain U ℱ₁ 1) = deltaCochain U (lift + lift')) :
    cls U ℱ₁ d = cls U ℱ₁ c + cls U ℱ₁ c' := by
  have h := cls_add_of_localLifts U φ hmono
    (push_neg_eq_cechD_of_push_eq_deltaCochain U φ hc)
    (push_neg_eq_cechD_of_push_eq_deltaCochain U φ hc')
    (push_neg_eq_cechD_of_push_eq_deltaCochain U φ hd)
  rwa [cls, cls, cls, QuotientAddGroup.mk_neg, QuotientAddGroup.mk_neg, QuotientAddGroup.mk_neg,
    ← neg_add, neg_inj] at h

/-- **Stacks 02AP, independence of the covering on a common refinement.** Let `φ : ℱ₁ ⟶ ℱ₂` be
injective on sections and `ℱ₁ → ℱ₂ → ℱ₃` exact in the middle on sections. Let `𝒰` and `𝒰'` be
two families of opens over `W`, each with a system of lifts of the same section `τ` of `ℱ₃`, and
let `𝒱` be a common refinement of the two. Then the classes of the two cocycles
`(i₀, i₁) ↦ τ̃_{i₀} - τ̃_{i₁}` have the same image in `Ȟ¹(𝒱, ℱ₁)`. -/
@[stacks 02AP "the class `δ(τ)` agrees on a given common refinement of two coverings"]
theorem cls_eq_of_refinement_of_push_eq_deltaCochain
    (U' : I' → Opens X) (V : K → Opens X)
    (r : K → I) (hr : ∀ k, V k ≤ U (r k))
    (r' : K → I') (hr' : ∀ k, V k ≤ U' (r' k))
    (hle' : ∀ i : Fin 1 → I', inter U' i ≤ W)
    (hmono : ∀ V₀ : Opens X, Function.Injective (φ.app (op V₀)))
    (hexact : ∀ (V₀ : Opens X) (b : ToType (ℱ₂.obj (op V₀))), ψ.app (op V₀) b = 0 →
      ∃ a, φ.app (op V₀) a = b)
    {lift' : Cochain U' ℱ₂ 0}
    (hlift : ∀ i, ψ.app (op (inter U i)) (lift i) = restr ℱ₃ (hle i) τ)
    (hlift' : ∀ i, ψ.app (op (inter U' i)) (lift' i) = restr ℱ₃ (hle' i) τ)
    {c : cocycles1 U ℱ₁} {c' : cocycles1 U' ℱ₁}
    (hc : push U φ 1 (c : Cochain U ℱ₁ 1) = deltaCochain U lift)
    (hc' : push U' φ 1 (c' : Cochain U' ℱ₁ 1) = deltaCochain U' lift') :
    refinementCechH1 U V r hr ℱ₁ (cls U ℱ₁ c) =
      refinementCechH1 U' V r' hr' ℱ₁ (cls U' ℱ₁ c') := by
  have h := cls_eq_of_refinement_of_localLifts U φ ψ hle U' V r hr r' hr' hle' hmono hexact
    hlift hlift' (push_neg_eq_cechD_of_push_eq_deltaCochain U φ hc)
    (push_neg_eq_cechD_of_push_eq_deltaCochain U' φ hc')
  rwa [cls, cls, QuotientAddGroup.mk_neg, QuotientAddGroup.mk_neg, map_neg, map_neg,
    neg_inj] at h

/-- **Stacks 02AP, independence of the covering.** Let `φ : ℱ₁ ⟶ ℱ₂` be injective on sections
and `ℱ₁ → ℱ₂ → ℱ₃` exact in the middle on sections. Two families of opens covering `W`, each with
a system of lifts of the same section `τ` of `ℱ₃`, admit a common refinement covering `W`, the
family of their pairwise intersections, on which the classes of the two cocycles
`(i₀, i₁) ↦ τ̃_{i₀} - τ̃_{i₁}` agree. -/
@[stacks 02AP "the class `δ(τ)` does not depend on the covering"]
theorem exists_common_refinement_cls_eq_of_push_eq_deltaCochain
    (U' : I' → Opens X) (hU : W = ⨆ i, U i) (hU' : W = ⨆ i', U' i')
    (hmono : ∀ V₀ : Opens X, Function.Injective (φ.app (op V₀)))
    (hexact : ∀ (V₀ : Opens X) (b : ToType (ℱ₂.obj (op V₀))), ψ.app (op V₀) b = 0 →
      ∃ a, φ.app (op V₀) a = b)
    {lift' : Cochain U' ℱ₂ 0}
    (hlift : ∀ i, ψ.app (op (inter U i)) (lift i) = restr ℱ₃ (inter_le_of_eq_iSup hU i) τ)
    (hlift' : ∀ i, ψ.app (op (inter U' i)) (lift' i) = restr ℱ₃ (inter_le_of_eq_iSup hU' i) τ)
    {c : cocycles1 U ℱ₁} {c' : cocycles1 U' ℱ₁}
    (hc : push U φ 1 (c : Cochain U ℱ₁ 1) = deltaCochain U lift)
    (hc' : push U' φ 1 (c' : Cochain U' ℱ₁ 1) = deltaCochain U' lift') :
    ∃ (V : I × I' → Opens X) (r : I × I' → I) (hr : ∀ k, V k ≤ U (r k))
      (r' : I × I' → I') (hr' : ∀ k, V k ≤ U' (r' k)),
      W = ⨆ k, V k ∧
        refinementCechH1 U V r hr ℱ₁ (cls U ℱ₁ c) =
          refinementCechH1 U' V r' hr' ℱ₁ (cls U' ℱ₁ c') := by
  refine ⟨fun p => U p.1 ⊓ U' p.2, Prod.fst, fun _ => inf_le_left, Prod.snd,
    fun _ => inf_le_right, eq_iSup_inf_of_eq_iSup U hU hU', ?_⟩
  exact cls_eq_of_refinement_of_push_eq_deltaCochain U φ ψ (inter_le_of_eq_iSup hU) U' _ _ _ _ _
    (inter_le_of_eq_iSup hU') hmono hexact hlift hlift' hc hc'

end Stacks.Cohomology.CechBoundary

end
