module

public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The diagonal is stable under base change (Stacks 04YR)

We work in the `(2,1)`-category of categories with the explicit 2-fibre product of Example 003R,
which is Mathlib's `CategoryTheory.Limits.CategoricalPullback F G`, written `F ⊡ G`: its objects
are triples `(a, c, φ)` with `φ : F a ≅ G c`, and its morphisms are pairs of morphisms compatible
with the structural isomorphisms. It comes with projections `π₁`, `π₂`, a canonical
2-commutative square `catCommSq`, and the universal property
`functorEquiv : (W ⥤ F ⊡ G) ≌ CatCommSqOver F G W`.

A 2-commutative square with apex `W`, legs `W ⥤ A` and `W ⥤ C`, cospan `F, G` and structural
2-cell is called *2-cartesian* when the functor `W ⥤ F ⊡ G` that the universal property attaches
to it is an equivalence of categories; the functor itself is `comparison` below. Applying this to
the square with both legs the identity gives the relative diagonal
`Δ_{A/B} = relativeDiagonal k : A ⥤ k ⊡ k`, `a ↦ (a, a, 𝟙)`, of a functor `k : A ⥤ B`.

Now let `h : X ⥤ Y` and `s : V ⥤ Y`, put `U = X ×_Y V = h ⊡ s` with `r = π₁ h s : U ⥤ X` and
`g = π₂ h s : U ⥤ V`, and form `U ×_V U = g ⊡ g` and `X ×_Y X = h ⊡ h`. There is a canonical
2-commutative square
```
        Δ_{U/V}
   U  ----------->  U ×_V U
   |                   |
 r |                   | r × r
   v                   v
   X  ----------->  X ×_Y X
        Δ_{X/Y}
```
whose right-hand leg `r × r = mapDiag h s` is the functor induced by `r` on both factors
(Stacks 02XA). The theorem of this file is that the square is 2-cartesian, i.e. that
`U ⥤ Δ_{X/Y} ⊡ (r × r)` is an equivalence: the diagonal of `U` over `V` is obtained from the
diagonal of `X` over `Y` by base change.

The proof gives an explicit quasi-inverse. The comparison functor composed with the projection
`Δ_{X/Y} ⊡ (r × r) ⥤ U` reading off the first `U`-component is the identity *on the nose*, so the
unit is an identity; the counit is built object-wise from the isomorphism `theta`, which upgrades
the two projections of the structural isomorphism of an object of `Δ_{X/Y} ⊡ (r × r)` to an
isomorphism `u₁ ≅ u₂` in `U`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.Limits.CategoricalPullback

/-- The first components of the two directions of an isomorphism of a categorical pullback are
mutually inverse. -/
@[simp] theorem Iso.inv_fst_comp_hom_fst {A B C : Type*} [Category A] [Category B] [Category C]
    {F : A ⥤ B} {G : C ⥤ B} {x y : F ⊡ G} (i : x ≅ y) : i.inv.fst ≫ i.hom.fst = 𝟙 y.fst := by
  rw [← CategoricalPullback.comp_fst, i.inv_hom_id, CategoricalPullback.id_fst]

/-- The mirror of `Iso.inv_fst_comp_hom_fst`. -/
@[simp] theorem Iso.hom_fst_comp_inv_fst {A B C : Type*} [Category A] [Category B] [Category C]
    {F : A ⥤ B} {G : C ⥤ B} {x y : F ⊡ G} (i : x ≅ y) : i.hom.fst ≫ i.inv.fst = 𝟙 x.fst := by
  rw [← CategoricalPullback.comp_fst, i.hom_inv_id, CategoricalPullback.id_fst]

variable {X V Y : Type*} [Category X] [Category V] [Category Y]
variable (h : X ⥤ Y) (s : V ⥤ Y)

/-- The functor `W ⥤ F ⊡ G` attached by the universal property `functorEquiv` to a
2-commutative square over `W` with cospan `F, G`. By construction it satisfies
`comparison F G sq ⋙ π₁ F G = sq.fst` and `comparison F G sq ⋙ π₂ F G = sq.snd`
definitionally, and the square is 2-cartesian precisely when this functor is an equivalence. -/
def comparison {A B C : Type*} [Category A] [Category B] [Category C]
    (F : A ⥤ B) (G : C ⥤ B) {W : Type*} [Category W] (sq : CatCommSqOver F G W) :
    W ⥤ F ⊡ G :=
  (functorEquiv F G W).inverse.obj sq

/-- The relative diagonal `Δ_{A/B} : A ⥤ A ×_B A` of a functor `k : A ⥤ B`, sending
`a` to `(a, a, 𝟙)`. It is the comparison functor of the square with both legs the identity
functor and identity structural 2-cell. -/
def relativeDiagonal {A B : Type*} [Category A] [Category B] (k : A ⥤ B) :
    A ⥤ k ⊡ k :=
  comparison k k (CatCommSqOver.mk (𝟭 A) (𝟭 A) (Iso.refl _))

/-- The functor `r × r : (g ⊡ g) ⥤ (h ⊡ h)` induced by `r = π₁ h s` on both factors of
`U ×_V U`, where `U = h ⊡ s` and `g = π₂ h s` (this is the induced functor of Stacks 02XA for
the diagram whose vertical arrows are all `r`). On objects it sends `(u₁, u₂, ψ)` to
`(r u₁, r u₂, χ)`, the structural isomorphism `χ` being assembled from the canonical 2-cell
`r ⋙ h ≅ g ⋙ s` of `U` and the 2-cell of `U ×_V U`. -/
def mapDiag : ((π₂ h s) ⊡ (π₂ h s)) ⥤ h ⊡ h :=
  comparison h h (CatCommSqOver.mk
    (π₁ (π₂ h s) (π₂ h s) ⋙ π₁ h s)
    (π₂ (π₂ h s) (π₂ h s) ⋙ π₁ h s)
    ((Functor.associator _ _ _) ≪≫
      Functor.isoWhiskerLeft _ (catCommSq h s).iso ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (catCommSq (π₂ h s) (π₂ h s)).iso s ≪≫
      (Functor.associator _ _ _) ≪≫
      Functor.isoWhiskerLeft _ (catCommSq h s).iso.symm ≪≫
      (Functor.associator _ _ _).symm))

/-- **Stacks 04YR.** The structural 2-cell `r ⋙ Δ_{X/Y} ≅ Δ_{U/V} ⋙ (r × r)` of the base-change
square for the diagonal. Both composites have both projections equal to `r = π₁ h s`, so the
2-cell is the canonical one with identity projections. -/
@[stacks 04YR]
def baseChangeDiagonalSquareIso :
    (π₁ h s ⋙ relativeDiagonal h) ≅ (relativeDiagonal (π₂ h s) ⋙ mapDiag h s) :=
  mkNatIso (Iso.refl _) (Iso.refl _) (by
    ext W
    -- Same story as in `mapDiag_iso_compat`: the identity and the structural isomorphism of `W`
    -- are spelled through `π₁`/`π₂` of a `relativeDiagonal`/`mapDiag` value on one side, so the
    -- closing cancellation is stated separately and transferred by `exact`.
    have key : 𝟙 (h.obj W.fst) ≫ W.iso.hom ≫ s.map (𝟙 W.snd) ≫ W.iso.inv
        = 𝟙 (h.obj W.fst) := by simp
    simp only [relativeDiagonal, comparison, Functor.comp_obj, mapDiag, Iso.refl_hom,
      Functor.whiskerRight_id', Category.id_comp, NatTrans.comp_app, Functor.associator_hom_app,
      Functor.whiskerLeft_app, catCommSq_iso_hom_app, functorEquiv_inverse_obj_obj_iso_hom,
      Iso.trans_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.associator_inv_app, Functor.whiskerRight_app, NatTrans.id_app, Functor.id_obj,
      catCommSq_iso_inv_app, Category.comp_id]
    exact key)

/-- **Stacks 04YR.** The base-change square for the diagonal, over `U = h ⊡ s`: its legs are
`r = π₁ h s : U ⥤ X` and `Δ_{U/V} = relativeDiagonal (π₂ h s) : U ⥤ U ×_V U`, its cospan is
`Δ_{X/Y} = relativeDiagonal h : X ⥤ X ×_Y X` and `r × r = mapDiag h s`, and its structural
2-cell is `baseChangeDiagonalSquareIso`. -/
@[stacks 04YR]
def baseChangeDiagonalSquare :
    CatCommSqOver (relativeDiagonal h) (mapDiag h s) (h ⊡ s) :=
  CatCommSqOver.mk (π₁ h s) (relativeDiagonal (π₂ h s)) (baseChangeDiagonalSquareIso h s)

/-- The quasi-inverse to the comparison functor of the base-change square: it sends an object
`(x, (u₁, u₂, ψ), f)` of `Δ_{X/Y} ⊡ (r × r)` to `u₁`, and is the composite `π₂ ⋙ π₁`. -/
abbrev baseChangeDiagonalInverse :
    (relativeDiagonal h) ⊡ (mapDiag h s) ⥤ h ⊡ s :=
  π₂ (relativeDiagonal h) (mapDiag h s) ⋙ π₁ (π₂ h s) (π₂ h s)

/-- The comparison functor of the base-change square for the diagonal, `U ⥤ Δ_{X/Y} ⊡ (r × r)`;
the content of Stacks 04YR is that it is an equivalence. -/
abbrev baseChangeDiagonalComparison :
    (h ⊡ s) ⥤ (relativeDiagonal h) ⊡ (mapDiag h s) :=
  comparison (relativeDiagonal h) (mapDiag h s) (baseChangeDiagonalSquare h s)

/-- The comparison functor followed by its quasi-inverse is the identity on the nose: the
comparison sends `u` to `(r u, (u, u, 𝟙), ·)` and the quasi-inverse reads off the first
`U`-component. Since the projections of `comparison F G sq` are `sq.fst` and `sq.snd`
definitionally, no mediating isomorphism is needed. -/
theorem baseChangeDiagonalComparison_comp_inverse :
    baseChangeDiagonalComparison h s ⋙ baseChangeDiagonalInverse h s = 𝟭 (h ⊡ s) := rfl

/-- The relative diagonal sends `x` to `(x, x, 𝟙)`. -/
theorem relativeDiagonal_obj (x : X) :
    (relativeDiagonal h).obj x = CategoricalPullback.mk x x (Iso.refl _) := rfl

section RelativeDiagonalComponents

variable {A B : Type*} [Category A] [Category B] (k : A ⥤ B)

/-- The first component of `relativeDiagonal k` at `a` is `a`. -/
@[simp] theorem relativeDiagonal_obj_fst (a : A) : ((relativeDiagonal k).obj a).fst = a := rfl

/-- The second component of `relativeDiagonal k` at `a` is `a`. -/
@[simp] theorem relativeDiagonal_obj_snd (a : A) : ((relativeDiagonal k).obj a).snd = a := rfl

/-- The structural isomorphism of `relativeDiagonal k` at `a` is the identity. -/
@[simp] theorem relativeDiagonal_obj_iso (a : A) :
    ((relativeDiagonal k).obj a).iso = Iso.refl (k.obj a) := rfl

/-- The first component of `(relativeDiagonal k).map f` is `f`. -/
@[simp] theorem relativeDiagonal_map_fst {a b : A} (f : a ⟶ b) :
    ((relativeDiagonal k).map f).fst = f := rfl

/-- The second component of `(relativeDiagonal k).map f` is `f`. -/
@[simp] theorem relativeDiagonal_map_snd {a b : A} (f : a ⟶ b) :
    ((relativeDiagonal k).map f).snd = f := rfl

end RelativeDiagonalComponents

/-- The first component of `mapDiag h s` is `r` applied to the first factor. -/
theorem mapDiag_obj_fst (w : (π₂ h s) ⊡ (π₂ h s)) :
    ((mapDiag h s).obj w).fst = (π₁ h s).obj w.fst := rfl

/-- The second component of `mapDiag h s` is `r` applied to the second factor. -/
theorem mapDiag_obj_snd (w : (π₂ h s) ⊡ (π₂ h s)) :
    ((mapDiag h s).obj w).snd = (π₁ h s).obj w.snd := rfl

/-- The first component of `mapDiag h s` at `w` is the `X`-component of the first factor. -/
theorem mapDiag_obj_fst_fst (w : (π₂ h s) ⊡ (π₂ h s)) :
    ((mapDiag h s).obj w).fst = w.fst.fst := rfl

/-- The first component of `(mapDiag h s).map f` is `r` applied to the first component of `f`. -/
theorem mapDiag_map_fst {w w' : (π₂ h s) ⊡ (π₂ h s)} (f : w ⟶ w') :
    ((mapDiag h s).map f).fst = (π₁ h s).map f.fst := rfl

/-- The second component of `(mapDiag h s).map f` is `r` applied to the second component
of `f`. -/
theorem mapDiag_map_snd {w w' : (π₂ h s) ⊡ (π₂ h s)} (f : w ⟶ w') :
    ((mapDiag h s).map f).snd = (π₁ h s).map f.snd := rfl

/-- The structural isomorphism `χ` of `mapDiag h s` at `w = (u₁, u₂, ψ)` satisfies
`χ ≫ u₂.iso = u₁.iso ≫ s(ψ)`; equivalently `χ = u₁.iso ∘ s(ψ) ∘ u₂.iso⁻¹`. -/
theorem mapDiag_iso_compat (w : (π₂ h s) ⊡ (π₂ h s)) :
    ((mapDiag h s).obj w).iso.hom ≫ w.snd.iso.hom = w.fst.iso.hom ≫ s.map w.iso.hom := by
  -- The two structural isomorphisms are reached through `π₁`/`π₂` of `w` on one side and
  -- directly on the other; the spellings agree only past a plain `def`, so the final
  -- cancellation is supplied as a separately stated identity.
  have key : w.fst.iso.hom ≫ s.map w.iso.hom ≫ w.snd.iso.inv ≫ w.snd.iso.hom
      = w.fst.iso.hom ≫ s.map w.iso.hom := by simp
  simp only [mapDiag, comparison]
  simp only [functorEquiv, Functor.id_obj, Functor.comp_obj,
    CatCommSqOver.toFunctorToCategoricalPullback_obj_obj_iso_hom, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.whiskerLeft_app, catCommSq_iso_hom_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, catCommSq_iso_inv_app,
    Category.comp_id, Category.id_comp, Category.assoc]
  exact key

variable {h s}

/-- The action of the relative diagonal on a morphism: `f ↦ (f, f)`. -/
@[simp] theorem relativeDiagonal_map {x y : X} (f : x ⟶ y) :
    (relativeDiagonal h).map f = CategoricalPullback.Hom.mk f f
      (by simp) := by
  apply CategoricalPullback.hom_ext <;> rfl

/-- For `e = (x, (u₁, u₂, ψ), f)` in `Δ_{X/Y} ⊡ (r × r)`, the isomorphism `u₁ ≅ u₂` in
`U = h ⊡ s` whose `V`-component is `ψ` and whose `X`-component is `f.snd ∘ f.fst⁻¹`, the two
projections of `f` being isomorphisms `x ≅ r u₁` and `x ≅ r u₂`. The compatibility square in `Y`
is the naturality of `f` combined with `mapDiag_iso_compat`, after cancelling `h(f.fst)`. -/
def baseChangeDiagonalTheta (e : (relativeDiagonal h) ⊡ (mapDiag h s)) :
    e.snd.fst ≅ e.snd.snd :=
  CategoricalPullback.mkIso
    (((π₁ h h).mapIso e.iso).symm ≪≫ (π₂ h h).mapIso e.iso)
    e.snd.iso
    (by
      have hw := e.iso.hom.w
      have hcompat := mapDiag_iso_compat h s e.snd
      simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv,
        Functor.mapIso_hom, π₁_map, π₂_map] at *
      have hid : ((relativeDiagonal h).obj e.fst).iso.hom = 𝟙 _ := rfl
      rw [hid, Category.id_comp] at hw
      have hinv : e.iso.inv.fst ≫ e.iso.hom.fst = 𝟙 _ := by
        have := CategoricalPullback.comp_fst e.iso.inv e.iso.hom
        rw [e.iso.inv_hom_id] at this
        simp only [CategoricalPullback.id_fst] at this
        exact this.symm
      rw [← hcompat, Functor.map_comp, ← hw, ← Functor.map_comp_assoc, hinv]
      have hmid : h.map (𝟙 ((mapDiag h s).obj e.snd).fst) = 𝟙 _ := h.map_id _
      rw [hmid, Category.id_comp ((mapDiag h s).obj e.snd).iso.hom])

/-- The `X`-component of `baseChangeDiagonalTheta e` is `f.snd ∘ f.fst⁻¹`, for `f = e.iso`. -/
@[simp] theorem baseChangeDiagonalTheta_hom_fst (e : (relativeDiagonal h) ⊡ (mapDiag h s)) :
    (baseChangeDiagonalTheta e).hom.fst = e.iso.inv.fst ≫ e.iso.hom.snd := by
  simp [baseChangeDiagonalTheta]

/-- The `V`-component of `baseChangeDiagonalTheta e` is the structural isomorphism `ψ` of the
`U ×_V U`-factor of `e`. -/
@[simp] theorem baseChangeDiagonalTheta_hom_snd (e : (relativeDiagonal h) ⊡ (mapDiag h s)) :
    (baseChangeDiagonalTheta e).hom.snd = e.snd.iso.hom := by
  simp [baseChangeDiagonalTheta]

/-- The `U`-component of the first factor of a morphism `f : e ⟶ e'` of `Δ_{X/Y} ⊡ (r × r)`,
transported by the structural isomorphisms of `e` and `e'`, is the `X`-component of `f`. This is
the `.fst`-projection of the coherence square of `f`, solved for `r (f.snd.fst)`. -/
theorem π₁_map_snd_fst {e e' : (relativeDiagonal h) ⊡ (mapDiag h s)} (f : e ⟶ e') :
    (π₁ h s).map f.snd.fst = e.iso.inv.fst ≫ f.fst ≫ e'.iso.hom.fst := by
  have hw : f.fst ≫ e'.iso.hom.fst = e.iso.hom.fst ≫ (π₁ h s).map f.snd.fst :=
    congrArg CategoricalPullback.Hom.fst f.w
  rw [hw, ← Category.assoc, Iso.inv_fst_comp_hom_fst, Category.id_comp]

variable (h s)

/-- The `X`-component of the comparison functor on objects is `r`. -/
@[simp] theorem baseChangeDiagonalComparison_obj_fst (u : h ⊡ s) :
    ((baseChangeDiagonalComparison h s).obj u).fst = (π₁ h s).obj u := rfl

/-- The `U ×_V U`-component of the comparison functor on objects is `Δ_{U/V}`. -/
@[simp] theorem baseChangeDiagonalComparison_obj_snd (u : h ⊡ s) :
    ((baseChangeDiagonalComparison h s).obj u).snd = (relativeDiagonal (π₂ h s)).obj u := rfl

/-- The `X`-component of the comparison functor on morphisms is `r`. -/
@[simp] theorem baseChangeDiagonalComparison_map_fst {u u' : h ⊡ s} (g : u ⟶ u') :
    ((baseChangeDiagonalComparison h s).map g).fst = (π₁ h s).map g := rfl

/-- The `U ×_V U`-component of the comparison functor on morphisms is `Δ_{U/V}`. -/
@[simp] theorem baseChangeDiagonalComparison_map_snd {u u' : h ⊡ s} (g : u ⟶ u') :
    ((baseChangeDiagonalComparison h s).map g).snd = (relativeDiagonal (π₂ h s)).map g := rfl

/-- The `.fst`-projection of the structural isomorphism of the comparison functor is the
identity. -/
theorem baseChangeDiagonalComparison_iso_hom_fst (u : h ⊡ s) :
    ((baseChangeDiagonalComparison h s).obj u).iso.hom.fst = 𝟙 _ := rfl

/-- The `.snd`-projection of the structural isomorphism of the comparison functor is the
identity. -/
theorem baseChangeDiagonalComparison_iso_hom_snd (u : h ⊡ s) :
    ((baseChangeDiagonalComparison h s).obj u).iso.hom.snd = 𝟙 _ := rfl

/-- The `(g ⊡ g)`-component of the counit at `e`: the isomorphism `(u₁, u₁, 𝟙) ≅ (u₁, u₂, ψ)`
which is the identity on the first factor and `baseChangeDiagonalTheta e` on the second. -/
def baseChangeDiagonalCounitIsoSnd
    (e : (relativeDiagonal h) ⊡ (mapDiag h s)) :
    ((baseChangeDiagonalInverse h s ⋙ baseChangeDiagonalComparison h s).obj e).snd ≅ e.snd :=
  CategoricalPullback.mkIso (Iso.refl e.snd.fst) (baseChangeDiagonalTheta e) (by
    have hid : ((baseChangeDiagonalInverse h s ⋙
      baseChangeDiagonalComparison h s).obj e).snd.iso.hom = 𝟙 _ := rfl
    rw [hid]
    simp only [π₂_map, Iso.refl_hom, CategoricalPullback.id_snd, Category.id_comp,
      baseChangeDiagonalTheta, mkIso_hom_snd]
    exact Category.id_comp _)

/-- The `X`-factor of `baseChangeDiagonalCounitIsoSnd` is the identity. -/
@[simp] theorem baseChangeDiagonalCounitIsoSnd_hom_fst
    (e : (relativeDiagonal h) ⊡ (mapDiag h s)) :
    (baseChangeDiagonalCounitIsoSnd h s e).hom.fst = 𝟙 e.snd.fst := by
  simp [baseChangeDiagonalCounitIsoSnd]

/-- The `V`-factor of `baseChangeDiagonalCounitIsoSnd` is `baseChangeDiagonalTheta`. -/
@[simp] theorem baseChangeDiagonalCounitIsoSnd_hom_snd
    (e : (relativeDiagonal h) ⊡ (mapDiag h s)) :
    (baseChangeDiagonalCounitIsoSnd h s e).hom.snd = (baseChangeDiagonalTheta e).hom := by
  simp [baseChangeDiagonalCounitIsoSnd]

/-- The object component of the counit isomorphism: on the `X`-factor it is `f.fst⁻¹` and on the
`(g ⊡ g)`-factor it is `baseChangeDiagonalCounitIsoSnd`. -/
def baseChangeDiagonalCounitIsoObj
    (e : (relativeDiagonal h) ⊡ (mapDiag h s)) :
    (baseChangeDiagonalInverse h s ⋙ baseChangeDiagonalComparison h s).obj e ≅ e :=
  CategoricalPullback.mkIso
    (((π₁ h h).mapIso e.iso).symm)
    (baseChangeDiagonalCounitIsoSnd h s e)
    (by
      apply CategoricalPullback.hom_ext
      · simp [baseChangeDiagonalComparison_iso_hom_fst, mapDiag_map_fst, mapDiag_obj_fst_fst]
      · simp [baseChangeDiagonalComparison_iso_hom_snd, mapDiag_map_snd])

/-- The `X`-factor of the counit isomorphism at `e` is `f.fst⁻¹`, for `f = e.iso`. -/
@[simp] theorem baseChangeDiagonalCounitIsoObj_hom_fst
    (e : (relativeDiagonal h) ⊡ (mapDiag h s)) :
    (baseChangeDiagonalCounitIsoObj h s e).hom.fst = e.iso.inv.fst := by
  simp [baseChangeDiagonalCounitIsoObj]

/-- The `(g ⊡ g)`-factor of the counit isomorphism at `e` is
`baseChangeDiagonalCounitIsoSnd`. -/
@[simp] theorem baseChangeDiagonalCounitIsoObj_hom_snd
    (e : (relativeDiagonal h) ⊡ (mapDiag h s)) :
    (baseChangeDiagonalCounitIsoObj h s e).hom.snd
      = (baseChangeDiagonalCounitIsoSnd h s e).hom := by
  simp [baseChangeDiagonalCounitIsoObj]

/-- Naturality of `baseChangeDiagonalTheta`: a morphism `f : e ⟶ e'` of `Δ_{X/Y} ⊡ (r × r)`
intertwines `θ e` with `θ e'`. On the `X`-factor this is the coherence square of `f` after
cancelling the isomorphism `e.iso.hom.fst`; on the `V`-factor it is the compatibility condition
defining a morphism of `U ×_V U`. -/
theorem baseChangeDiagonalTheta_naturality {e e' : (relativeDiagonal h) ⊡ (mapDiag h s)}
    (f : e ⟶ e') :
    f.snd.fst ≫ (baseChangeDiagonalTheta e').hom
      = (baseChangeDiagonalTheta e).hom ≫ f.snd.snd := by
  have hwfsnd : f.fst ≫ e'.iso.hom.snd = e.iso.hom.snd ≫ (π₁ h s).map f.snd.snd :=
    congrArg CategoricalPullback.Hom.snd f.w
  apply CategoricalPullback.hom_ext
  · rw [CategoricalPullback.comp_fst, CategoricalPullback.comp_fst,
      baseChangeDiagonalTheta_hom_fst, baseChangeDiagonalTheta_hom_fst,
      show f.snd.fst.fst = (π₁ h s).map f.snd.fst from rfl,
      show f.snd.snd.fst = (π₁ h s).map f.snd.snd from rfl,
      π₁_map_snd_fst f, Category.assoc, Category.assoc, Category.assoc,
      show e'.iso.hom.fst ≫ e'.iso.inv.fst ≫ e'.iso.hom.snd = e'.iso.hom.snd from by
        rw [← Category.assoc, Iso.hom_fst_comp_inv_fst, Category.id_comp],
      hwfsnd, ← Category.assoc]
  · rw [CategoricalPullback.comp_snd, CategoricalPullback.comp_snd,
      baseChangeDiagonalTheta_hom_snd, baseChangeDiagonalTheta_hom_snd]
    simpa using f.snd.w

/-- The counit isomorphism of the equivalence, `baseChangeDiagonalInverse ⋙
baseChangeDiagonalComparison ≅ 𝟭`. This is where the mathematical content of Stacks 04YR sits:
naturality is checked componentwise, reducing on the `X`-factor to the naturality of the
structural isomorphisms and on the `V`-factor to `baseChangeDiagonalTheta_naturality`. -/
def baseChangeDiagonalCounitIso :
    baseChangeDiagonalInverse h s ⋙ baseChangeDiagonalComparison h s ≅
      𝟭 ((relativeDiagonal h) ⊡ (mapDiag h s)) := by
  refine NatIso.ofComponents (fun e => baseChangeDiagonalCounitIsoObj h s e) ?_
  intro e e' f
  apply CategoricalPullback.hom_ext
  · have := π₁_map_snd_fst f
    simp only [π₁_map] at this
    simp [this]
  · apply CategoricalPullback.hom_ext
    · simp only [Functor.comp_map, π₂_map, π₁_map, comp_snd, comp_fst,
        baseChangeDiagonalCounitIsoObj_hom_snd, baseChangeDiagonalCounitIsoSnd_hom_fst,
        baseChangeDiagonalComparison_map_snd, relativeDiagonal_map_fst, Functor.id_map]
      -- `f.snd.fst` is elaborated against `π₂`-spelled endpoints; restate it on `e.snd.fst`.
      change f.snd.fst ≫ 𝟙 e'.snd.fst = 𝟙 e.snd.fst ≫ f.snd.fst
      rw [Category.comp_id, Category.id_comp]
    · simpa using baseChangeDiagonalTheta_naturality h s f

/-- **Stacks 04YR.** The diagonal is stable under base change: for `h : X ⥤ Y` and `s : V ⥤ Y`,
with `U = X ×_Y V`, `r = π₁ h s` and `g = π₂ h s`, the square
`Δ_{U/V} : U ⥤ U ×_V U`, `r : U ⥤ X` over `Δ_{X/Y} : X ⥤ X ×_Y X`, `r × r : U ×_V U ⥤ X ×_Y X`
is 2-cartesian, i.e. its comparison functor `U ⥤ Δ_{X/Y} ⊡ (r × r)` is an equivalence of
categories. The quasi-inverse is `baseChangeDiagonalInverse`, the unit is an identity by
`baseChangeDiagonalComparison_comp_inverse`, and the counit is
`baseChangeDiagonalCounitIso`. -/
@[stacks 04YR]
theorem isEquivalence_baseChangeDiagonalComparison :
    Functor.IsEquivalence (comparison (relativeDiagonal h) (mapDiag h s)
      (baseChangeDiagonalSquare h s)) :=
  Functor.IsEquivalence.mk' (baseChangeDiagonalInverse h s)
    (eqToIso (baseChangeDiagonalComparison_comp_inverse h s).symm)
    (baseChangeDiagonalCounitIso h s)

end CategoryTheory.Limits.CategoricalPullback
