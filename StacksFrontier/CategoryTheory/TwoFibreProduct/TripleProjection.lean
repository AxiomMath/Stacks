module

public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The outer projection of a triple 2-fibre product (Stacks 04S7)

Consider a diagram of categories and functors
```
𝒜 --F--> ℬ <--G-- 𝒞 --H--> 𝒟 <--I-- ℰ
         |                  |
         P                  Q
         v                  v
         ℱ ================ ℱ
```
in which the inner square commutes, `G ⋙ P = H ⋙ Q`. Then `F ⋙ P` and `I ⋙ Q` form a cospan
over `ℱ`, and there is a canonical functor
`(𝒜 ×_ℬ 𝒞) ×_𝒟 ℰ ⥤ 𝒜 ×_ℱ ℰ`
forgetting the middle factor: on objects it sends `((a, c, φ), e, ψ)` to `(a, e, Q(ψ) ∘ P(φ))`,
where the two structural isomorphisms are pushed into `ℱ` and spliced along the commutativity
of the inner square.

Both 2-fibre products are Mathlib's `CategoryTheory.Limits.CategoricalPullback` (Example 003R):
the source is `CategoricalPullback (π₂ F G ⋙ H) I` and the target is
`CategoricalPullback (F ⋙ P) (I ⋙ Q)`. The inner square is required to commute on the nose,
which is why the object component of the comparison isomorphism contains an `eqToIso`.
-/

@[expose] public section

namespace CategoryTheory.Limits

variable {𝒜 ℬ 𝒞 𝒟 ℰ ℱ : Type*}
variable [Category 𝒜] [Category ℬ] [Category 𝒞] [Category 𝒟] [Category ℰ] [Category ℱ]
variable (F : 𝒜 ⥤ ℬ) (G : 𝒞 ⥤ ℬ) (H : 𝒞 ⥤ 𝒟) (I : ℰ ⥤ 𝒟) (P : ℬ ⥤ ℱ) (Q : 𝒟 ⥤ ℱ)

/-- The object-level identification supplied by the commuting inner square: the middle join
of `CategoricalPullback.pr₀₂Iso`.

Its endpoints are spelled `P.obj (G.obj _)` and `Q.obj ((π₂ F G ⋙ H).obj _)` — the forms in
which `P.mapIso` and `Q.mapIso` present them — rather than the `(G ⋙ P).obj _`/`(H ⋙ Q).obj _`
of the underlying `congrFun`, which are only definitionally equal to them. `rw` and `simp`
unify at reducible transparency, so a join spelled differently on the two sides is invisible
to them. -/
lemma CategoricalPullback.pr₀₂_obj_eq (h : G ⋙ P = H ⋙ Q)
    (X : CategoricalPullback (CategoricalPullback.π₂ F G ⋙ H) I) :
    P.obj (G.obj X.fst.snd) = Q.obj ((CategoricalPullback.π₂ F G ⋙ H).obj X.fst) :=
  congrFun (congrArg Functor.obj h) X.fst.snd

/-- The composite isomorphism `P (F a) ≅ Q (I e)` underlying the object component of
`CategoricalPullback.pr₀₂`: it is `Q(ψ) ∘ P(φ)` in diagrammatic order, spliced along
`G ⋙ P = H ⋙ Q`. -/
def CategoricalPullback.pr₀₂Iso (h : G ⋙ P = H ⋙ Q)
    (X : CategoricalPullback (CategoricalPullback.π₂ F G ⋙ H) I) :
    P.obj (F.obj X.fst.fst) ≅ Q.obj (I.obj X.snd) :=
  P.mapIso X.fst.iso ≪≫ eqToIso (pr₀₂_obj_eq F G H I P Q h X) ≪≫
    Q.mapIso (X := (CategoricalPullback.π₂ F G ⋙ H).obj X.fst) X.iso

/-- Naturality of `CategoricalPullback.pr₀₂Iso`, which is the compatibility obligation for the
morphism component of `CategoricalPullback.pr₀₂`. -/
lemma CategoricalPullback.pr₀₂Iso_naturality (h : G ⋙ P = H ⋙ Q)
    {X Y : CategoricalPullback (CategoricalPullback.π₂ F G ⋙ H) I} (f : X ⟶ Y) :
    P.map (F.map f.fst.fst) ≫ (pr₀₂Iso F G H I P Q h Y).hom =
      (pr₀₂Iso F G H I P Q h X).hom ≫ Q.map (I.map f.snd) := by
  have hh0 : ∀ {c c' : 𝒞} (g : c ⟶ c'),
      P.map (G.map g) ≫ (eqToHom (congrFun (congrArg Functor.obj h) c') :
        P.obj (G.obj c') ⟶ Q.obj (H.obj c')) =
      (eqToHom (congrFun (congrArg Functor.obj h) c) :
        P.obj (G.obj c) ⟶ Q.obj (H.obj c)) ≫ Q.map (H.map g) := by
    intro c c' g
    rw [show P.map (G.map g) = (G ⋙ P).map g from rfl,
        show Q.map (H.map g) = (H ⋙ Q).map g from rfl,
        Functor.congr_hom h g]
    simp
  -- `hh0 f.fst.snd`, restated with the joins spelled exactly as the goal spells them.
  have hh : P.map (G.map f.fst.snd) ≫ eqToHom (pr₀₂_obj_eq F G H I P Q h Y) =
      eqToHom (pr₀₂_obj_eq F G H I P Q h X) ≫
        Q.map ((CategoricalPullback.π₂ F G ⋙ H).map f.fst) :=
    hh0 f.fst.snd
  simp only [pr₀₂Iso, Iso.trans_hom, eqToIso.hom, Functor.mapIso_hom, Category.assoc]
  slice_lhs 1 2 => rw [← P.map_comp, f.fst.w, P.map_comp]
  slice_lhs 2 3 => rw [hh]
  slice_lhs 3 4 => rw [← Q.map_comp, f.w, Q.map_comp]

/-- **Stacks 04S7.** For a commuting inner square `G ⋙ P = H ⋙ Q` under the diagram
`𝒜 → ℬ ← 𝒞 → 𝒟 ← ℰ`, the canonical functor `(𝒜 ×_ℬ 𝒞) ×_𝒟 ℰ ⥤ 𝒜 ×_ℱ ℰ` which forgets the
middle factor and transports the two structural isomorphisms into `ℱ`. -/
@[stacks 04S7]
def CategoricalPullback.pr₀₂ (h : G ⋙ P = H ⋙ Q) :
    CategoricalPullback (CategoricalPullback.π₂ F G ⋙ H) I ⥤
      CategoricalPullback (F ⋙ P) (I ⋙ Q) where
  obj X :=
    { fst := X.fst.fst
      snd := X.snd
      iso := pr₀₂Iso F G H I P Q h X }
  map f :=
    { fst := f.fst.fst
      snd := f.snd
      w := pr₀₂Iso_naturality F G H I P Q h f }
  map_id _ := by apply CategoricalPullback.hom_ext <;> rfl
  map_comp _ _ := by apply CategoricalPullback.hom_ext <;> rfl

end CategoryTheory.Limits
