module

public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverRepresentable

/-!
# The coproduct presheaf of a sheaf on a localized site is a sheaf

Let `(C, J)` be a site, let `U` be an object of `C` and let `G` be a presheaf of sets on the
localized site `C/U`. The coproduct presheaf
`CategoryTheory.OverShriek.presheaf G : V ↦ ∐_{φ : V ⟶ U} G(V →φ U)` of Stacks 03CD is a sheaf for
`J` as soon as `G` is a sheaf for `J.over U` and the representable presheaf of `U` is a sheaf for
`J`. In particular, on a subcanonical site the coproduct presheaf needs no sheafification, which is
what makes the formula of Stacks 03I4 part (1) an identification of sheaves rather than of
presheaves.

## Main results

* `CategoryTheory.OverShriek.isSheaf_presheaf`: the coproduct presheaf of a sheaf on `C/U` is a
  sheaf on `C`, provided `h_U` is.

## Implementation notes

A section of `presheaf G` over `V` is a pair `(φ, s)` with `φ : V ⟶ U` and `s ∈ G(V →φ U)`, so
amalgamating a compatible family splits into two steps. Its first components form a compatible
family of sections of `h_U`, which amalgamate to a single `φ : V ⟶ U` because `h_U` is a sheaf;
this promotes the family to a compatible family of sections of `G` over the objects of `C/U` lying
above `Over.mk φ`, which amalgamate because `G` is a sheaf for `J.over U`. Uniqueness is the same
argument run backwards.

The bookkeeping lemmas `presheafSection`, `sigmaMk_presheafSection` and `map_presheafSection`
convert between a section `p` of `presheaf G` over `A.left` whose first component is `A.hom` and a
section of `G` over `A`; they are the pointwise form of
`CategoryTheory.OverShriek.presheafUnitEquiv`, written out so that the restriction maps of
`presheaf G` can be compared with those of `G` directly.

## References

* [Stacks Project, Tag 03CD](https://stacks.math.columbia.edu/tag/03CD)
* [Stacks Project, Tag 03I4](https://stacks.math.columbia.edu/tag/03I4)
-/

@[expose] public section

open CategoryTheory Opposite

universe v u

namespace CategoryTheory.OverShriek

variable {C : Type u} [Category.{v} C] {U : C}

/-- The section of `G` over `A` carried by a section `p` of the coproduct presheaf over `A.left`
whose first component is the structure morphism of `A`. -/
def presheafSection {G : (Over U)ᵒᵖ ⥤ Type v} {A : Over U}
    (p : (presheaf G).obj (op A.left)) (h : p.1 = A.hom) : G.obj (op A) :=
  G.map (Over.homMk (𝟙 A.left) (by simpa using h) : A ⟶ Over.mk p.1).op p.2

/-- The first component of a section of the coproduct presheaf is preserved by restriction: if `p`
has first component `A.hom` and restricts to `q` along `b : B ⟶ A`, then `q` has first component
`B.hom`. -/
lemma presheafSection_fst {G : (Over U)ᵒᵖ ⥤ Type v} {A B : Over U}
    (b : B ⟶ A) {p : (presheaf G).obj (op A.left)} (h : p.1 = A.hom)
    {q : (presheaf G).obj (op B.left)}
    (hq : (presheaf G).map b.left.op p = q) : q.1 = B.hom := by
  subst hq
  rw [presheaf_map_apply_fst, Quiver.Hom.unop_op, h]
  exact Over.w b

/-- Rebuilding a section of the coproduct presheaf from the section of `G` it carries recovers
it. -/
lemma sigmaMk_presheafSection {G : (Over U)ᵒᵖ ⥤ Type v} {A : Over U}
    (p : (presheaf G).obj (op A.left)) (h : p.1 = A.hom) :
    (⟨A.hom, presheafSection p h⟩ : (presheaf G).obj (op A.left)) = p :=
  sigmaMk_eq_self G p.2
    (Over.homMk (𝟙 A.left) (by simpa using h) : Over.mk A.hom ⟶ Over.mk p.1) rfl

/-- Restriction in the coproduct presheaf of a section built from a section of `G`. -/
lemma presheaf_map_sigmaMk {G : (Over U)ᵒᵖ ⥤ Type v} {A B : Over U}
    (b : B ⟶ A) (t : G.obj (op A)) :
    (presheaf G).map b.left.op (⟨A.hom, t⟩ : (presheaf G).obj (op A.left)) =
      ⟨B.hom, G.map b.op t⟩ :=
  sigmaMk_eq G t (Over.homMk b.left rfl : Over.mk (b.left ≫ A.hom) ⟶ Over.mk A.hom) b rfl

/-- Two sections of `G` over `Over.mk φ` that give the same pair are equal. -/
lemma sigma_snd_inj {G : (Over U)ᵒᵖ ⥤ Type v} {V : C} {φ : V ⟶ U}
    {s t : G.obj (op (Over.mk φ))}
    (hst : (⟨φ, s⟩ : Σ ψ : V ⟶ U, G.obj (op (Over.mk ψ))) = ⟨φ, t⟩) : s = t := by
  simpa using hst

/-- The section of `G` carried by a section of the coproduct presheaf is compatible with
restriction. -/
lemma map_presheafSection {G : (Over U)ᵒᵖ ⥤ Type v} {A B : Over U}
    (b : B ⟶ A) {p : (presheaf G).obj (op A.left)} (h : p.1 = A.hom)
    {q : (presheaf G).obj (op B.left)}
    (hq : (presheaf G).map b.left.op p = q) :
    G.map b.op (presheafSection p h) = presheafSection q (presheafSection_fst b h hq) :=
  sigma_snd_inj <|
    (presheaf_map_sigmaMk b (presheafSection p h)).symm.trans <|
      ((congrArg (fun z => (presheaf G).map b.left.op z)
        (sigmaMk_presheafSection p h)).trans hq).trans
        (sigmaMk_presheafSection q (presheafSection_fst b h hq)).symm

/-- The coproduct presheaf `V ↦ ∐_{φ : V ⟶ U} G(V →φ U)` of a sheaf `G` on the localized site
`C/U` is a sheaf on `C`, provided the representable presheaf of `U` is one. -/
lemma isSheaf_presheaf (J : GrothendieckTopology C) (G : (Over U)ᵒᵖ ⥤ Type v)
    (hU : Presieve.IsSheaf J (yoneda.obj U))
    (hG : Presieve.IsSheaf (J.over U) G) :
    Presieve.IsSheaf J (presheaf G) := by
  intro V S hS x hx
  obtain ⟨φ, hφ, hφuniq⟩ := hU S hS _ (hx.map (presheafToYoneda G))
  have key : ∀ {A : Over U} (a : A ⟶ Over.mk φ) (ha : S.arrows a.left),
      (x a.left ha).1 = A.hom :=
    fun a ha => (hφ a.left ha).symm.trans (Over.w a)
  obtain ⟨t, ht, htuniq⟩ :=
    hG _ (J.overEquiv_symm_mem_over (Over.mk φ) S hS)
      (fun _ a ha => presheafSection (x a.left ha) (key a ha))
      (by
        intro _ _ _ b₁ b₂ _ _ h₁ h₂ hcomm
        exact (map_presheafSection b₁ _ rfl).trans
          (map_presheafSection b₂ _
            (hx b₁.left b₂.left h₁ h₂ (congrArg Over.Hom.left hcomm)).symm).symm)
  refine ⟨⟨φ, t⟩, ?_, ?_⟩
  · intro Y f hf
    let b : Over.mk (f ≫ φ) ⟶ Over.mk φ := Over.homMk f rfl
    exact (presheaf_map_sigmaMk b t).trans
      ((congrArg (fun s => (⟨f ≫ φ, s⟩ : (presheaf G).obj (op Y))) (ht b hf)).trans
        (sigmaMk_presheafSection (A := Over.mk (f ≫ φ)) (x f hf) (key b hf)))
  · intro p hp
    have hψ : p.1 = φ := hφuniq _ (hp.map (presheafToYoneda G))
    exact (sigmaMk_presheafSection (A := Over.mk φ) p hψ).symm.trans
      (congrArg (fun s => (⟨φ, s⟩ : (presheaf G).obj (op V)))
        (htuniq _ fun _ a ha => map_presheafSection a hψ (hp a.left ha)))

end CategoryTheory.OverShriek

end
