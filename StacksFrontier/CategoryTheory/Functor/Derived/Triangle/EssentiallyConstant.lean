module

public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Opposite.Basic
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import StacksFrontier.CategoryTheory.EssentiallyConstant.Cofinal
import StacksFrontier.CategoryTheory.EssentiallyConstant.IndObject
public import StacksFrontier.CategoryTheory.Functor.Derived.DefinedAt
import StacksFrontier.CategoryTheory.Functor.Derived.Morphisms
public import StacksFrontier.CategoryTheory.Localization.Saturated.Defs
import StacksFrontier.CategoryTheory.Triangulated.Localization
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.CategoryTheory.Functor.Derived.Triangle.Values

/-!
# Transport of essential constancy

Essential constancy of ind-objects transported along functors, isomorphisms, final functors,
changes of index and shifts, and the values of `RF` moved along morphisms of `W`. Part of the
proof of [Stacks, Tag 05SC].
-/

section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

open scoped CategoryTheory.Pretriangulated.Opposite

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace DerivedFunctorValues

section Transport

open EssentiallyConstantInd

variable {A : Type*} [Category A] {B : Type*} [Category B] {I : Type*} [Category I]
  {J : Type*} [Category J]

/-- Essential constancy of an ind-object is preserved by an arbitrary functor: the witnessing
data is a splitting and a factorisation of transition morphisms, and both are equations between
composites. No hypothesis on the functor, the index category or the target is needed. -/
private lemma isEssentiallyConstantWith_comp {M : I ⥤ A} {t : Cocone M} {i : I}
    {r : t.pt ⟶ M.obj i} (h : IsEssentiallyConstantWith M t i r) (Φ : A ⥤ B) :
    IsEssentiallyConstantWith (M ⋙ Φ) (Φ.mapCocone t) i (Φ.map r) where
  retraction := by
    change Φ.map r ≫ Φ.map (t.ι.app i) = 𝟙 _
    rw [← Φ.map_comp, h.retraction, Φ.map_id]
  cofinal j := by
    obtain ⟨k, σ, τ, hk⟩ := h.cofinal j
    refine ⟨k, σ, τ, ?_⟩
    change Φ.map (M.map τ) = Φ.map (t.ι.app j) ≫ Φ.map r ≫ Φ.map (M.map σ)
    rw [← Φ.map_comp, ← Φ.map_comp, hk]

/-- Essential constancy of an ind-object is invariant under an isomorphism of diagrams. -/
private lemma isEssentiallyConstantWith_ofIso {M M' : I ⥤ A} {t : Cocone M} {i : I}
    {r : t.pt ⟶ M.obj i} (h : IsEssentiallyConstantWith M t i r) (α : M ≅ M') :
    IsEssentiallyConstantWith M' (Cocone.mk t.pt (α.inv ≫ t.ι)) i (r ≫ α.hom.app i) where
  retraction := by
    change (r ≫ α.hom.app i) ≫ α.inv.app i ≫ t.ι.app i = 𝟙 _
    rw [Category.assoc, ← Category.assoc (α.hom.app i), α.hom_inv_id_app, Category.id_comp]
    exact h.retraction
  cofinal j := by
    obtain ⟨k, σ, τ, hk⟩ := h.cofinal j
    refine ⟨k, σ, τ, ?_⟩
    change M'.map τ = (α.inv.app j ≫ t.ι.app j) ≫ (r ≫ α.hom.app i) ≫ M'.map σ
    have hτ : M'.map τ = α.inv.app j ≫ M.map τ ≫ α.hom.app k := by
      rw [α.hom.naturality τ, ← Category.assoc, α.inv_hom_id_app, Category.id_comp]
    rw [hτ, hk]
    simp only [Category.assoc]
    rw [α.hom.naturality σ]

/-- Essential constancy of an ind-object is invariant under an isomorphism of the value: extending
the cocone along an isomorphism `e : t.pt ≅ V` of its vertex keeps it essentially constant, the
retraction becoming `e.inv ≫ r`. -/
private lemma isEssentiallyConstantWith_extend {M : I ⥤ A} {t : Cocone M} {i : I}
    {r : t.pt ⟶ M.obj i} (h : IsEssentiallyConstantWith M t i r) {V : A} (e : t.pt ≅ V) :
    IsEssentiallyConstantWith M (t.extend e.hom) i (e.inv ≫ r) where
  retraction := by
    change (e.inv ≫ r) ≫ t.ι.app i ≫ e.hom = 𝟙 V
    rw [Category.assoc, ← Category.assoc r, h.retraction, Category.id_comp, e.inv_hom_id]
  cofinal j := by
    obtain ⟨k, σ, τ, hk⟩ := h.cofinal j
    refine ⟨k, σ, τ, ?_⟩
    change M.map τ = (t.ι.app j ≫ e.hom) ≫ (e.inv ≫ r) ≫ M.map σ
    rw [hk]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- The retraction of an essentially constant ind-object, followed by a transition map out of its
index, is a section of the coprojection at the target. -/
private lemma comp_map_comp_ι_app_aux {M : I ⥤ A} {t : Cocone M} {i : I} {r : t.pt ⟶ M.obj i}
    (h : IsEssentiallyConstantWith M t i r) {k : I} (σ : i ⟶ k) :
    (r ≫ M.map σ) ≫ t.ι.app k = 𝟙 t.pt := by
  rw [Category.assoc, t.w σ]
  exact h.retraction

/-- Essential constancy of an ind-object is inherited by the restriction of the diagram along a
full and essentially surjective functor of index categories. Filteredness is not used, and the
functor need not be faithful. -/
private lemma isEssentiallyConstantWith_precomp {M : I ⥤ A} {t : Cocone M} {i : I}
    {r : t.pt ⟶ M.obj i} (h : IsEssentiallyConstantWith M t i r) (G : J ⥤ I) [G.Full]
    [G.EssSurj] :
    IsEssentiallyConstantWith (G ⋙ M) (t.whisker G) (G.objPreimage i)
      (r ≫ M.map (G.objObjPreimageIso i).inv) := by
  set e := G.objObjPreimageIso i with he
  constructor
  · exact comp_map_comp_ι_app_aux h e.inv
  · intro j
    obtain ⟨k, σ, τ, hk⟩ := h.cofinal (G.obj j)
    refine ⟨G.objPreimage k, G.preimage (e.hom ≫ σ ≫ (G.objObjPreimageIso k).inv),
      G.preimage (τ ≫ (G.objObjPreimageIso k).inv), ?_⟩
    set f := G.objObjPreimageIso k with hf
    have key : M.map e.inv ≫ M.map (e.hom ≫ σ ≫ f.inv) = M.map σ ≫ M.map f.inv := by
      rw [← M.map_comp, ← M.map_comp, ← Category.assoc, e.inv_hom_id, Category.id_comp,
        M.map_comp]
    change M.map (G.map (G.preimage (τ ≫ f.inv))) =
      t.ι.app (G.obj j) ≫ (r ≫ M.map e.inv) ≫
        M.map (G.map (G.preimage (e.hom ≫ σ ≫ f.inv)))
    rw [G.map_preimage, G.map_preimage]
    calc M.map (τ ≫ f.inv) = M.map τ ≫ M.map f.inv := M.map_comp _ _
      _ = (t.ι.app (G.obj j) ≫ r ≫ M.map σ) ≫ M.map f.inv := by rw [hk]
      _ = t.ι.app (G.obj j) ≫ (r ≫ M.map e.inv) ≫ M.map (e.hom ≫ σ ≫ f.inv) := by
          simp only [Category.assoc]
          rw [key]

/-- **Change of base index.** Essential constancy of an ind-object over a filtered index category
does not depend on which index carries the retraction: if the ind-object is essentially constant
with cocone `t`, index `i` and retraction `r`, then any other index `i'` carrying a section `r'`
of the coprojection at `i'` witnesses it as well.

*Argument.* The cofinality clause at `i'` gives transitions with `r' ≫ M(τ₂) = r ≫ M(σ₂)`, so the
two retractions agree after transition maps; merging that with the cofinality clause at `j` — a
common target and one cancellation of the two morphisms out of `i` by `IsFiltered.coeq` — gives
the clause for `r'`. -/
private lemma isEssentiallyConstantWith_changeIndex [IsFiltered I] {M : I ⥤ A} {t : Cocone M}
    {i : I} {r : t.pt ⟶ M.obj i} (h : IsEssentiallyConstantWith M t i r) {i' : I}
    {r' : t.pt ⟶ M.obj i'} (hr' : r' ≫ t.ι.app i' = 𝟙 t.pt) :
    IsEssentiallyConstantWith M t i' r' := by
  refine ⟨hr', fun j => ?_⟩
  obtain ⟨k₁, σ₁, τ₁, h₁⟩ := h.cofinal j
  obtain ⟨k₂, σ₂, τ₂, h₂⟩ := h.cofinal i'
  have key : r' ≫ M.map τ₂ = r ≫ M.map σ₂ := by
    rw [h₂, ← Category.assoc, ← Category.assoc, hr', Category.id_comp]
  set m₁ := IsFiltered.leftToMax k₁ k₂ with hm₁
  set m₂ := IsFiltered.rightToMax k₁ k₂ with hm₂
  set w := IsFiltered.coeqHom (σ₁ ≫ m₁) (σ₂ ≫ m₂) with hwdef
  have hw : (σ₁ ≫ m₁) ≫ w = (σ₂ ≫ m₂) ≫ w := IsFiltered.coeq_condition _ _
  have e₁ : ∀ {Q : A} (z : M.obj k₁ ⟶ Q), M.map τ₁ ≫ z = t.ι.app j ≫ r ≫ M.map σ₁ ≫ z := by
    intro Q z; rw [h₁]; simp only [Category.assoc]
  have e₂ : ∀ {Q : A} (z : M.obj k₂ ⟶ Q), r' ≫ M.map τ₂ ≫ z = r ≫ M.map σ₂ ≫ z := by
    intro Q z; rw [← Category.assoc, key, Category.assoc]
  refine ⟨_, τ₂ ≫ m₂ ≫ w, τ₁ ≫ m₁ ≫ w, ?_⟩
  calc M.map (τ₁ ≫ m₁ ≫ w) = M.map τ₁ ≫ M.map (m₁ ≫ w) := by rw [M.map_comp]
    _ = t.ι.app j ≫ r ≫ M.map σ₁ ≫ M.map (m₁ ≫ w) := e₁ _
    _ = t.ι.app j ≫ r ≫ M.map ((σ₁ ≫ m₁) ≫ w) := by
        simp only [M.map_comp, Category.assoc]
    _ = t.ι.app j ≫ r ≫ M.map ((σ₂ ≫ m₂) ≫ w) := by rw [hw]
    _ = t.ι.app j ≫ r ≫ M.map σ₂ ≫ M.map (m₂ ≫ w) := by
        simp only [M.map_comp, Category.assoc]
    _ = t.ι.app j ≫ r' ≫ M.map τ₂ ≫ M.map (m₂ ≫ w) := by rw [e₂]
    _ = t.ι.app j ≫ r' ≫ M.map (τ₂ ≫ m₂ ≫ w) := by
        simp only [M.map_comp]

/-- **Restriction along a cofinal functor**, Tag 0A1S read on a pinned cocone. If `M` is
essentially constant with cocone `t`, index `i₀` and retraction `r`, and `G : J ⥤ I` is cofinal
between filtered categories, then `G ⋙ M` is essentially constant with the whiskered cocone, at
any index `j₀` of `J` equipped with a morphism `τ₀ : i₀ ⟶ G(j₀)`, the retraction being
`r ≫ M(τ₀)` — or any morphism equal to it, which is what the side condition `hr'` is for: at the
base index of Tag 05R9 the transition `τ₀` is an identity and the retraction is `r` on the nose.

This is `essentiallyConstant_comp_final_of` (Tag 0A1S, forward direction) with the cocone and the
retraction kept rather than existentially quantified, so that the value and its coprojections can
be named; the index is an arbitrary one under `i₀` rather than `Functor.Final.lift G i₀`. -/
lemma isEssentiallyConstantWith_comp_final [IsFiltered I] [IsFiltered J] {M : I ⥤ A}
    {t : Cocone M} {i₀ : I} {r : t.pt ⟶ M.obj i₀} (h : IsEssentiallyConstantWith M t i₀ r)
    (G : J ⥤ I) [G.Final] {j₀ : J} (τ₀ : i₀ ⟶ G.obj j₀) {r' : t.pt ⟶ (G ⋙ M).obj j₀}
    (hr' : r ≫ M.map τ₀ = r' := by rfl) :
    IsEssentiallyConstantWith (G ⋙ M) (t.whisker G) j₀ r' := by
  subst hr'
  constructor
  · exact comp_map_comp_ι_app_aux h τ₀
  · intro j
    obtain ⟨kJ, vJ, uJ, hJ⟩ := h.cofinal (G.obj j)
    obtain ⟨c, u, v, z, hu, hv⟩ := exists_lift_cospan G τ₀ uJ vJ
    refine ⟨c, v, u, ?_⟩
    change M.map (G.map u) = t.ι.app (G.obj j) ≫ (r ≫ M.map τ₀) ≫ M.map (G.map v)
    rw [hu, M.map_comp, hJ, Category.assoc, Category.assoc, ← M.map_comp, ← hv, M.map_comp]
    simp only [Category.assoc]

/-- **Extension along a cofinal functor**, Tag 0A1S read on a pinned cocone. If `G ⋙ M` is
essentially constant with cocone `s`, index `j₀` and retraction `r`, and `G : J ⥤ I` is cofinal,
then `M` is essentially constant with the extended cocone
`Functor.Final.extendCocone.obj s` — which has the same vertex, and whose coprojection at an
object of the form `G(j)` is the coprojection of `s` at `j` — at the index `G(j₀)` and with the
same retraction.

This is `essentiallyConstant_of_comp_final` (Tag 0A1S, backward direction) with the cocone kept
rather than existentially quantified; filteredness of neither index category is used. -/
lemma isEssentiallyConstantWith_of_comp_final (M : I ⥤ A) (G : J ⥤ I) [G.Final]
    {s : Cocone (G ⋙ M)} {j₀ : J} {r : s.pt ⟶ M.obj (G.obj j₀)}
    (h : IsEssentiallyConstantWith (G ⋙ M) s j₀ r) :
    IsEssentiallyConstantWith M (Functor.Final.extendCocone.obj s) (G.obj j₀) r := by
  constructor
  · change r ≫ M.map (Functor.Final.homToLift G (G.obj j₀)) ≫
        s.ι.app (Functor.Final.lift G (G.obj j₀)) = 𝟙 s.pt
    rw [Functor.Final.colimit_cocone_comp_aux s j₀]
    exact h.retraction
  · intro d
    obtain ⟨k, σ, τ, hστ⟩ := h.cofinal (Functor.Final.lift G d)
    refine ⟨G.obj k, G.map σ, Functor.Final.homToLift G d ≫ G.map τ, ?_⟩
    have hι : (Functor.Final.extendCocone.obj s).ι.app d =
        M.map (Functor.Final.homToLift G d) ≫ s.ι.app (Functor.Final.lift G d) :=
      Functor.Final.extendCocone_obj_ι_app' s (Functor.Final.homToLift G d)
    change M.map (Functor.Final.homToLift G d ≫ G.map τ) =
      (Functor.Final.extendCocone.obj s).ι.app d ≫ r ≫ M.map (G.map σ)
    calc M.map (Functor.Final.homToLift G d ≫ G.map τ)
        = M.map (Functor.Final.homToLift G d) ≫ M.map (G.map τ) := M.map_comp _ _
      _ = M.map (Functor.Final.homToLift G d) ≫
            s.ι.app (Functor.Final.lift G d) ≫ r ≫ M.map (G.map σ) := by
          rw [show M.map (G.map τ) =
            s.ι.app (Functor.Final.lift G d) ≫ r ≫ M.map (G.map σ) from hστ]
      _ = (M.map (Functor.Final.homToLift G d) ≫ s.ι.app (Functor.Final.lift G d)) ≫
            r ≫ M.map (G.map σ) := (Category.assoc _ _ _).symm
      _ = (Functor.Final.extendCocone.obj s).ι.app d ≫ r ≫ M.map (G.map σ) := by
          rw [hι]
          rfl

/-- **The criterion of Tag 05PY(4)**, in the colimit-free form that holds at an index category of
arbitrary size. Let `M : I ⥤ A` be a diagram indexed by a filtered category, `X` an object of `A`,
`i₀` an index and `ρ : X ⟶ M(i₀)`. Suppose that for every object `V` the map
`Mor(V, X) ⟶ colim_j Mor(V, M(j))`, `h ↦ [h ≫ ρ]`, is bijective, with the equality of classes in
the filtered colimit of Hom-sets spelled out by the transition data that witnesses it: `hsurj`
says every `g : V ⟶ M(j)` becomes `h ≫ ρ` after transition maps, and `hinj` says two morphisms
`V ⟶ X` that agree after `ρ` and a pair of transition maps out of `i₀` are equal. Then `M` is
essentially constant with value `X`, the cocone being built from `hsurj` and the retraction at
`i₀` being `ρ`.

Neither hypothesis mentions a colimit, so this applies at index categories that are not small in
the hom-universe of `A` — such as the `X/W` of Tag 05Q0, whose objects live in `Type (max u v)`
while the Hom-sets of the target live in `Type v`. -/
lemma exists_isEssentiallyConstantWith_of_hom_factorization [IsFiltered I] (M : I ⥤ A)
    {X : A} {i₀ : I} (ρ : X ⟶ M.obj i₀)
    (hsurj : ∀ (V : A) (j : I) (g : V ⟶ M.obj j),
      ∃ (k : I) (σ : i₀ ⟶ k) (τ : j ⟶ k) (h : V ⟶ X), g ≫ M.map τ = h ≫ ρ ≫ M.map σ)
    (hinj : ∀ (V : A) (h h' : V ⟶ X) (k : I) (σ σ' : i₀ ⟶ k),
      h ≫ ρ ≫ M.map σ = h' ≫ ρ ≫ M.map σ' → h = h') :
    ∃ ι : M ⟶ (Functor.const I).obj X, IsEssentiallyConstantWith M (Cocone.mk X ι) i₀ ρ := by
  choose K σ τ c hc using fun j : I => hsurj (M.obj j) j (𝟙 _)
  simp only [Category.id_comp] at hc
  have key : ∀ (j : I) {l : I} (w : K j ⟶ l),
      c j ≫ ρ ≫ M.map (σ j ≫ w) = M.map (τ j ≫ w) := by
    intro j l w
    rw [Functor.map_comp, Functor.map_comp, hc j]
    simp only [Category.assoc]
  refine ⟨⟨c, ?_⟩, ?_, fun j => ⟨K j, σ j, τ j, hc j⟩⟩
  · intro j j' φ
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
    set m := IsFiltered.leftToMax (K j) (K j') with hm
    set m' := IsFiltered.rightToMax (K j) (K j') with hm'
    set n := IsFiltered.coeqHom (τ j ≫ m) (φ ≫ τ j' ≫ m') with hn
    have hcoeq : τ j ≫ m ≫ n = φ ≫ τ j' ≫ m' ≫ n := by
      simpa only [Category.assoc] using
        IsFiltered.coeq_condition (τ j ≫ m) (φ ≫ τ j' ≫ m')
    refine hinj (M.obj j) _ _ _ (σ j' ≫ m' ≫ n) (σ j ≫ m ≫ n) ?_
    rw [Category.assoc, key j' (m' ≫ n), key j (m ≫ n), ← Functor.map_comp, ← hcoeq]
  · change ρ ≫ c i₀ = 𝟙 X
    refine hinj X _ _ (K i₀) (σ i₀) (τ i₀) ?_
    rw [Category.assoc, ← hc i₀, Category.id_comp]

/-- The other half of the bijectivity of Tag 05PY(4) at an essentially constant ind-object: every
`g : V ⟶ M(j)` agrees, after transition maps, with `(g ≫ c_j) ≫ r`, so the comparison map
`Mor(V, t.pt) ⟶ colim_j Mor(V, M(j))` is surjective. Again no smallness of `I` is used. -/
private lemma exists_factorization_of_isEssentiallyConstantWith {M : I ⥤ A} {t : Cocone M} {i : I}
    {r : t.pt ⟶ M.obj i} (h : IsEssentiallyConstantWith M t i r) {V : A} (j : I)
    (g : V ⟶ M.obj j) :
    ∃ (k : I) (σ : i ⟶ k) (τ : j ⟶ k), g ≫ M.map τ = (g ≫ t.ι.app j) ≫ r ≫ M.map σ := by
  obtain ⟨k, σ, τ, hk⟩ := h.cofinal j
  refine ⟨k, σ, τ, ?_⟩
  rw [hk]
  simp only [Category.assoc]

/-- **A member of a comparison family out of a pinned value is split by a coprojection.** If the
ind-object is essentially constant with cocone `t`, index `i` and retraction `r`, then `r` followed
by any transition map out of `i` is a section of the coprojection at its target. This is what makes
the morphisms of the source's comparison family split monomorphisms, so that the five lemma
applies. -/
lemma comp_map_comp_ι_app {M : I ⥤ A} {t : Cocone M} {i : I} {r : t.pt ⟶ M.obj i}
    (h : IsEssentiallyConstantWith M t i r) {k : I} (σ : i ⟶ k) :
    (r ≫ M.map σ) ≫ t.ι.app k = 𝟙 t.pt :=
  comp_map_comp_ι_app_aux h σ

/-- **The surjectivity half of Tag 05PY(4), read on a comparison family.** Let the ind-object `M`
be essentially constant with cocone `t`, index `i₀` and retraction `r`, and let `ψ` be a family of
morphisms `t.pt ⟶ M(k)` agreeing with `r` followed by the transition maps out of `i₀`. Then every
`g : V ⟶ M(j)` factors as `h ≫ ψ k` after a transition `j ⟶ k`, namely with `h = g ≫ c_j`. -/
lemma exists_factorization_of_pinned {M : I ⥤ A} {t : Cocone M} {i₀ : I}
    {r : t.pt ⟶ M.obj i₀} (h : IsEssentiallyConstantWith M t i₀ r) (ψ : ∀ k, t.pt ⟶ M.obj k)
    (hψ : ∀ {k : I} (σ : i₀ ⟶ k), r ≫ M.map σ = ψ k) {V : A} (j : I) (g : V ⟶ M.obj j) :
    ∃ (k : I) (τ : j ⟶ k) (h' : V ⟶ t.pt), g ≫ M.map τ = h' ≫ ψ k := by
  obtain ⟨k, σ, τ, hk⟩ := exists_factorization_of_isEssentiallyConstantWith h j g
  exact ⟨k, τ, g ≫ t.ι.app j, hk.trans (by rw [hψ σ])⟩

end Transport

section IndexTransport

variable {C : Type u₁} [Category.{v₁} C] {H : Type u₂} [Category.{v₂} H]
  (F : C ⥤ H) (W : MorphismProperty C)

open EssentiallyConstantInd

/-- Being a value of `RF` at `X` (Tag 05S9) is essential constancy of the ind-object at `X` in
the sense of `CategoryTheory.EssentiallyConstantInd.IsEssentiallyConstantWith`; the two differ
only in the order in which the two transition morphisms of the cofinality clause are
quantified. -/
private lemma exists_isEssentiallyConstantWith_of_isRightDerivedValueAt {X : C}
    {c : Cocone (indDiagram F W X)} (hc : F.IsRightDerivedValueAt W X c) :
    ∃ (s₀ : W.Under ⊤ X) (r : c.pt ⟶ (indDiagram F W X).obj s₀),
      IsEssentiallyConstantWith (indDiagram F W X) c s₀ r := by
  obtain ⟨s₀, r, hr, hcof⟩ := hc
  refine ⟨s₀, r, hr, fun j => ?_⟩
  obtain ⟨t, u, v, huv⟩ := hcof j
  exact ⟨t, v, u, huv⟩

/-- The converse of `exists_isEssentiallyConstantWith_of_isRightDerivedValueAt`. -/
lemma isRightDerivedValueAt_of_isEssentiallyConstantWith {X : C}
    {c : Cocone (indDiagram F W X)} {s₀ : W.Under ⊤ X} {r : c.pt ⟶ (indDiagram F W X).obj s₀}
    (h : IsEssentiallyConstantWith (indDiagram F W X) c s₀ r) :
    F.IsRightDerivedValueAt W X c := by
  refine ⟨s₀, r, h.retraction, fun s => ?_⟩
  obtain ⟨k, σ, τ, hk⟩ := h.cofinal s
  exact ⟨k, τ, σ, hk⟩

variable [W.RespectsIso]

/-- Precomposition with an isomorphism `e : X ≅ Y`, as a functor `Y/W ⥤ X/W` on the index
categories of Tag 05Q0. It is an isomorphism of categories; only fullness and essential
surjectivity are recorded, since that is what transport of essential constancy needs. -/
private def underPrecomp {X Y : C} (e : X ≅ Y) : W.Under ⊤ Y ⥤ W.Under ⊤ X where
  obj s := MorphismProperty.Under.mk ⊤ (e.hom ≫ s.hom)
    ((W.cancel_left_of_respectsIso e.hom s.hom).2 s.prop)
  map {s t} α := MorphismProperty.Under.homMk α.right
    ((Category.assoc e.hom s.hom α.right).trans
      (congrArg (fun z => e.hom ≫ z) (MorphismProperty.Under.w α))) trivial
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

private lemma underPrecomp_full {X Y : C} (e : X ≅ Y) : (underPrecomp W e).Full where
  map_surjective {s t} β :=
    ⟨MorphismProperty.Under.homMk β.right (by
      exact (Iso.cancel_iso_hom_left e _ _).1
        ((Category.assoc e.hom s.hom β.right).symm.trans
          (MorphismProperty.Under.w β))) trivial, rfl⟩

private lemma underPrecomp_essSurj {X Y : C} (e : X ≅ Y) : (underPrecomp W e).EssSurj where
  mem_essImage s := by
    have hs : W (e.inv ≫ s.hom) := (W.cancel_left_of_respectsIso e.inv s.hom).2 s.prop
    refine ⟨MorphismProperty.Under.mk ⊤ (e.inv ≫ s.hom) hs, ⟨?_⟩⟩
    refine MorphismProperty.Under.isoMk (Iso.refl _) ?_
    change (e.hom ≫ e.inv ≫ s.hom) ≫ 𝟙 _ = s.hom
    rw [Category.comp_id, ← Category.assoc, e.hom_inv_id, Category.id_comp]

/-- **Tag 05S9 is invariant under isomorphism of the object.** -/
private lemma exists_isRightDerivedValueAt_of_iso {X Y : C} (e : X ≅ Y)
    (h : ∃ c, F.IsRightDerivedValueAt W X c) : ∃ c, F.IsRightDerivedValueAt W Y c := by
  have := underPrecomp_full W e
  have := underPrecomp_essSurj W e
  obtain ⟨c, hc⟩ := h
  obtain ⟨s₀, r, h⟩ := exists_isEssentiallyConstantWith_of_isRightDerivedValueAt F W hc
  refine ⟨_, isRightDerivedValueAt_of_isEssentiallyConstantWith F W
    (isEssentiallyConstantWith_ofIso (isEssentiallyConstantWith_precomp h (underPrecomp W e))
      (NatIso.ofComponents (fun _ => Iso.refl _)
        (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm)))⟩

variable [HasShift C ℤ] [HasShift H ℤ] [W.IsCompatibleWithShift ℤ]

/-- The shift of indices, as a functor `X/W ⥤ (X⟦n⟧)/W`, `s ↦ s⟦n⟧`. -/
@[implicit_reducible]
public def underShift (X : C) (n : ℤ) : W.Under ⊤ X ⥤ W.Under ⊤ (X⟦n⟧) where
  obj s := MorphismProperty.Under.mk ⊤ (s.hom⟦n⟧')
    ((MorphismProperty.IsCompatibleWithShift.iff W s.hom n).2 s.prop)
  map {s _t} α := MorphismProperty.Under.homMk (α.right⟦n⟧')
    (((shiftFunctor C n).map_comp s.hom α.right).symm.trans
      (congrArg (shiftFunctor C n).map (MorphismProperty.Under.w α))) trivial
  map_id _ := MorphismProperty.Under.Hom.ext ((shiftFunctor C n).map_id _)
  map_comp _ _ := MorphismProperty.Under.Hom.ext ((shiftFunctor C n).map_comp _ _)

omit [W.RespectsIso] in
public lemma underShift_full (X : C) (n : ℤ) : (underShift W X n).Full where
  map_surjective {s _t} β := by
    have hw := MorphismProperty.Under.w β
    simp only [underShift, MorphismProperty.Under.mk_hom] at hw
    have hp := (shiftFunctor C n).map_preimage β.right
    refine ⟨MorphismProperty.Under.homMk ((shiftFunctor C n).preimage β.right) ?_ trivial, ?_⟩
    · apply (shiftFunctor C n).map_injective
      rwa [Functor.map_comp, hp]
    · exact MorphismProperty.Under.Hom.ext hp

public lemma underShift_essSurj (X : C) (n : ℤ) : (underShift W X n).EssSurj where
  mem_essImage t := by
    refine ⟨MorphismProperty.Under.mk ⊤
      ((shiftFunctorCompIsoId C n (-n) (add_neg_cancel n)).inv.app X ≫ t.hom⟦-n⟧')
      ((W.cancel_left_of_respectsIso _ _).2
        ((MorphismProperty.IsCompatibleWithShift.iff W t.hom (-n)).2 t.prop)), ⟨?_⟩⟩
    refine MorphismProperty.Under.isoMk
      ((shiftFunctorCompIsoId C (-n) n (neg_add_cancel n)).app t.right) ?_
    change (((shiftFunctorCompIsoId C n (-n) (add_neg_cancel n)).inv.app X ≫
        t.hom⟦-n⟧')⟦n⟧') ≫ _ = t.hom
    rw [Functor.map_comp, shift_shiftFunctorCompIsoId_add_neg_cancel_inv_app,
      Category.assoc]
    exact shiftFunctorCompIsoId_naturality_1 t.hom (-n) n (neg_add_cancel n)

variable [F.CommShift ℤ]

/-- **The commutation of `F` with the shift, read on the index categories.** The ind-object at
`X⟦n⟧` restricted along the shift of indices `s ↦ s⟦n⟧` is the ind-object at `X` followed by the
shift, the isomorphism at an index `s : X ⟶ X'` being `F(X'⟦n⟧) ≅ F(X')⟦n⟧`. -/
public def indDiagramShiftIso (X : C) (n : ℤ) :
    underShift W X n ⋙ indDiagram F W (X⟦n⟧) ≅ indDiagram F W X ⋙ shiftFunctor H n :=
  NatIso.ofComponents (fun s => (F.commShiftIso n).app s.right)
    (fun {_s _t} α => (F.commShiftIso n).hom.naturality α.right)

/-- **Tag 05SU(1)**, the descent. If `RF` is defined at `X⟦n⟧` then it is defined at `X`.

The functor `s ↦ s⟦n⟧` of index categories is full and essentially surjective (`underShift_full`,
`underShift_essSurj`), so the ind-object at `X⟦n⟧` restricts to an essentially constant
`s ↦ F(X'⟦n⟧)` on `X/W`; the commutation of `F` with the shift identifies that with
`(s ↦ F(X')) ⋙ (-)⟦n⟧`, and applying `(-)⟦-n⟧` returns the ind-object at `X`. -/
private lemma exists_isRightDerivedValueAt_of_shift (X : C) (n : ℤ)
    (h : ∃ c, F.IsRightDerivedValueAt W (X⟦n⟧) c) : ∃ c, F.IsRightDerivedValueAt W X c := by
  have := underShift_full W X n
  have := underShift_essSurj W X n
  obtain ⟨c, hc⟩ := h
  obtain ⟨s₀, r, h⟩ := exists_isEssentiallyConstantWith_of_isRightDerivedValueAt F W hc
  have γ : (indDiagram F W X ⋙ shiftFunctor H n) ⋙ shiftFunctor H (-n) ≅
      indDiagram F W X :=
    Functor.isoWhiskerLeft (indDiagram F W X)
      (shiftFunctorCompIsoId H n (-n) (add_neg_cancel n))
  exact ⟨_, isRightDerivedValueAt_of_isEssentiallyConstantWith F W
    (isEssentiallyConstantWith_ofIso
      (isEssentiallyConstantWith_comp
        (isEssentiallyConstantWith_ofIso
          (isEssentiallyConstantWith_precomp h (underShift W X n))
            (indDiagramShiftIso F W X n))
        (shiftFunctor H (-n))) γ)⟩

/-- **Tag 05SU(1)**. `RF` is defined at `X` if and only if it is defined at `X⟦n⟧`. -/
theorem exists_isRightDerivedValueAt_shift_iff (X : C) (n : ℤ) :
    (∃ c, F.IsRightDerivedValueAt W X c) ↔ ∃ c, F.IsRightDerivedValueAt W (X⟦n⟧) c := by
  refine ⟨fun h => exists_isRightDerivedValueAt_of_shift F W (X⟦n⟧) (-n)
    (exists_isRightDerivedValueAt_of_iso F W
      ((shiftFunctorCompIsoId C n (-n) (add_neg_cancel n)).symm.app X) h),
    exists_isRightDerivedValueAt_of_shift F W X n⟩


/-- **The canonical identification `RF(X)⟦n⟧ = RF(X⟦n⟧)`** of Tag 05SU(1), written on the cofinal
family of shifted indices rather than as an abstract isomorphism. If `c` is a value of `RF` at `X`
and `c₁` is a value of `RF` at `X⟦n⟧`, there is an isomorphism `e : c.pt⟦n⟧ ≅ c₁.pt` carrying the
morphism `F(X'⟦n⟧) ⟶ F(X')⟦n⟧ ⟶ c.pt⟦n⟧` to the coprojection of `c₁` at the shifted index `s⟦n⟧`,
for every index `s : X ⟶ X'` of `X/W`.

*Argument.* Restricted along `s ↦ s⟦n⟧`, which is full and essentially surjective
(`underShift_full`, `underShift_essSurj`), the ind-object at `X⟦n⟧` is essentially constant with
the whiskered cocone of `c₁`; the commutation of `F` with the shift identifies that same restricted
diagram with `(s ↦ F(X')) ⋙ (-)⟦n⟧`, on which the shift of the cocone `c` is essentially constant.
Two essentially constant cocones on one diagram are colimit cocones, hence uniquely isomorphic
compatibly with the coprojections. -/
lemma exists_iso_shift_of_isRightDerivedValueAt (X : C) (n : ℤ)
    {c : Cocone (indDiagram F W X)} (hc : F.IsRightDerivedValueAt W X c)
    {c₁ : Cocone (indDiagram F W (X⟦n⟧))} (hc₁ : F.IsRightDerivedValueAt W (X⟦n⟧) c₁) :
    ∃ e : c.pt⟦n⟧ ≅ c₁.pt, ∀ s : W.Under ⊤ X,
      ((F.commShiftIso n).hom.app s.right ≫ (c.ι.app s)⟦n⟧') ≫ e.hom =
        c₁.ι.app ((underShift W X n).obj s) := by
  have := underShift_full W X n
  have := underShift_essSurj W X n
  obtain ⟨s₀, r, h₀⟩ := exists_isEssentiallyConstantWith_of_isRightDerivedValueAt F W hc
  obtain ⟨t₀, r₁, h₁⟩ := exists_isEssentiallyConstantWith_of_isRightDerivedValueAt F W hc₁
  have hQ₂ := isEssentiallyConstantWith_ofIso
    (isEssentiallyConstantWith_comp h₀ (shiftFunctor H n)) (indDiagramShiftIso F W X n).symm
  have hQ₁ := isEssentiallyConstantWith_precomp h₁ (underShift W X n)
  exact ⟨hQ₂.isColimit.coconePointUniqueUpToIso hQ₁.isColimit,
    fun s => hQ₂.isColimit.comp_coconePointUniqueUpToIso_hom hQ₁.isColimit s⟩
end IndexTransport

section MoveValues

variable {C : Type u₁} [Category.{v₁} C] {H : Type u₂} [Category.{v₂} H]
  (F : C ⥤ H) (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]

open EssentiallyConstantInd

/-- **Moving a value forward along a morphism of `W`** (Tag 05SB). Let `RF` be defined at `X` with
value `c`, let `s` be an index of `X/W` and let `α : c.pt ⟶ F(X')` split the coprojection of `c` at
`s`. Then `c.pt` is a value of `RF` at `X'`, for a cocone whose retraction at the identity index of
`X'/W` is `α` itself.

*Argument.* By Tag 05SB `RF` is defined at `X'`, say with value `d`, and the induced morphism
`φ : c.pt ⟶ d.pt` is an isomorphism; the cocone `d` extended along `φ⁻¹` has vertex `c.pt` and is
essentially constant. Its coprojection at the identity index is `c_s ≫ φ ≫ φ⁻¹ = c_s`, by the
characterisation of `φ` at the square `s ≫ 𝟙 = s ≫ 𝟙`, so `α` splits it; and the base index of an
essential-constancy witness may be moved to any index carrying such a splitting
(`isEssentiallyConstantWith_changeIndex`, the index category being filtered by Tag 05Q0). -/
lemma exists_isEssentiallyConstantWith_at_index {X : C}
    {c : Cocone (indDiagram F W X)} (hc : F.IsRightDerivedValueAt W X c) (s : W.Under ⊤ X)
    (α : c.pt ⟶ F.obj s.right) (hα : α ≫ c.ι.app s = 𝟙 c.pt) :
    ∃ ι : indDiagram F W s.right ⟶ (Functor.const (W.Under ⊤ s.right)).obj c.pt,
      IsEssentiallyConstantWith (indDiagram F W s.right) (Cocone.mk c.pt ι)
        (idIndex W s.right) α := by
  have : IsFiltered (W.Under ⊤ s.right) :=
    W.isFiltered_under_of_hasLeftCalculusOfFractions s.right
  obtain ⟨hiff, hcomp⟩ := F.exists_isRightDerivedValueAt_iff_and_isIso_of_mem W
    (X := X) (Y := s.right) (s := (s.hom : X ⟶ s.right)) s.prop
  obtain ⟨d, hd⟩ := hiff.mp ⟨c, hc⟩
  obtain ⟨φ, hφ, hφiso⟩ := hcomp hc hd
  obtain ⟨t₀, r, h₀⟩ := exists_isEssentiallyConstantWith_of_isRightDerivedValueAt F W hd
  have hd0 : c.ι.app s ≫ φ = d.ι.app (idIndex W s.right) :=
    (hφ s (idIndex W s.right) (𝟙 s.right) rfl).trans
      ((congrArg (fun z => z ≫ d.ι.app (idIndex W s.right)) (F.map_id s.right)).trans
        (Category.id_comp _))
  exact ⟨(d.extend (inv φ)).ι, isEssentiallyConstantWith_changeIndex
    (isEssentiallyConstantWith_extend h₀ (asIso φ).symm)
    (comp_comp_eq_id hα (IsIso.hom_inv_id φ) hd0)⟩

/-- **Moving a value back along a morphism of `W`** (Tag 05SB). If `RF` is defined at `X'` with
value `d` and `s : X ⟶ X'` lies in `W`, then `d.pt` is a value of `RF` at `X`, for the cocone whose
coprojection at an index `a` of `X/W` is `F(f) ≫ d_b` for every square `a ≫ f = s ≫ b`. -/
lemma exists_isRightDerivedValueAt_of_mem {X X' : C} {s : X ⟶ X'} (hs : W s)
    {d : Cocone (indDiagram F W X')} (hd : F.IsRightDerivedValueAt W X' d) :
    ∃ ι : indDiagram F W X ⟶ (Functor.const (W.Under ⊤ X)).obj d.pt,
      F.IsRightDerivedValueAt W X (Cocone.mk d.pt ι) ∧
      ∀ (a : W.Under ⊤ X) (b : W.Under ⊤ X') (f : a.right ⟶ b.right),
        a.hom ≫ f = s ≫ b.hom → ι.app a = F.map f ≫ d.ι.app b := by
  obtain ⟨hiff, hcomp⟩ := F.exists_isRightDerivedValueAt_iff_and_isIso_of_mem W hs
  obtain ⟨c, hc⟩ := hiff.mpr ⟨d, hd⟩ -- 05SB: definedness at `X` follows from definedness at `X'`
  obtain ⟨φ, hφ, hφiso⟩ := hcomp hc hd
  obtain ⟨s₀, r, h₀⟩ := exists_isEssentiallyConstantWith_of_isRightDerivedValueAt F W hc
  exact ⟨(c.extend φ).ι, isRightDerivedValueAt_of_isEssentiallyConstantWith F W
    (isEssentiallyConstantWith_extend h₀ (asIso φ)), fun a b f hf => hφ a b f hf⟩

end MoveValues

end DerivedFunctorValues

end

end
