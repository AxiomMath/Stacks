module

public import Mathlib.AlgebraicTopology.SimplexCategory.Truncated
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# One-step extension of a truncated simplicial object

An `M`-truncated simplicial object of `A` is a functor `(SimplexCategory.Truncated M)ᵒᵖ ⥤ A`, and
`SimplexCategory.Truncated (M + 1)` has exactly one object more than `SimplexCategory.Truncated M`,
namely `⦋M + 1⦌`. This file constructs an `(M + 1)`-truncated simplicial object out of an
`M`-truncated one `Y`, a chosen object in degree `M + 1`, and the data of the morphisms into and
out of that object, and shows that its `M`-truncation is `Y` *on the nose*.

This is the construction that is unavailable in Mathlib and that an induction on the truncation
level needs when the degree-`M + 1` term is not free to be chosen by a universal property. The
one-step extension that Mathlib does have,
`CategoryTheory.SimplicialObject.Truncated.exists_isRightKanExtension_of_matchingFamily`, produces
the *coskeleton*, whose degree-`M + 1` term is the matching object; there is no way to replace that
object by a prescribed one mapping to it.

## The shape of the data

A functor out of `(SimplexCategory.Truncated (M + 1))ᵒᵖ` extending a given functor out of
`(SimplexCategory.Truncated M)ᵒᵖ` is not determined by its values on the generating faces
`δ i : ⦋M⦌ ⟶ ⦋M + 1⦌` and degeneracies `σ i : ⦋M + 1⦌ ⟶ ⦋M⦌` subject to the simplicial identities,
because `SimplexCategory.Truncated (M + 1)` has no presentation by generators and relations in
Mathlib: `SimplexCategoryGenRel` presents the *whole* simplex category and its comparison functor
`SimplexCategoryGenRel.toSimplexCategory` is not yet known to be an equivalence. Accordingly
`ExtensionData` takes the *whole families*

* `face x m : pt ⟶ Y.obj (op x)`, one morphism for every `m : x.obj ⟶ ⦋M + 1⦌` with `x`
  `M`-truncated, subject to `face x (g ≫ m) = face y m ≫ Y.map g.op`; and
* `degen x e : Y.obj (op x) ⟶ pt`, one morphism for every `e : ⦋M + 1⦌ ⟶ x.obj`, subject to
  `degen y (e ≫ g) = Y.map g.op ≫ degen x e`,

together with the single mixed law `degen x e ≫ face y m = Y.map (m ≫ e).op`. The first family is
a cone over the matching diagram and the second a cocone under the latching diagram, written out
element-wise so that neither the limit nor the colimit has to exist in `A`. This is the Reedy
one-step extension for `SimplexCategory` in a form that needs no (co)completeness of `A`.

Nothing here derives those two families from `δ`- and `σ`-data: for `face` that is the matching
object, and for `degen` it is the Eilenberg-Zilber decomposition of the degenerate part, which is
exactly the content the identities `s_i s_j = s_{j+1} s_i` cannot be made to supply when the
comparison morphism in degree `M + 1` is not a monomorphism. A consumer that has a map to a
matching object gets `face` from it, and a consumer whose degenerate part in degree `M + 1` is free
on the surjections `⦋M + 1⦌ ↠ ⦋m⦌` gets `degen` from that.

## Main definitions

* `CategoryTheory.SimplicialObject.Truncated.ExtensionData`: the data above.
* `CategoryTheory.SimplicialObject.Truncated.ExtensionData.obj` and `.map`: the object and
  morphism parts of the extension, by cases on whether the degree is at most `M`.
* `CategoryTheory.SimplicialObject.Truncated.ExtensionData.endo`: the action on an endomorphism of
  `⦋M + 1⦌`, read off the canonical epi-mono factorization. This is the only part of the functor
  that is not immediately one of the two families, since an endomorphism of `⦋M + 1⦌` other than
  the identity factors through a strictly smaller object but not in a unique way.
* `CategoryTheory.SimplicialObject.Truncated.ExtensionData.extend`: the resulting
  `(M + 1)`-truncated simplicial object.
* `CategoryTheory.SimplicialObject.Truncated.ExtensionData.ofSimplicialObject`: the extension data
  carried by a genuine simplicial object.

## Main results

* `CategoryTheory.SimplicialObject.Truncated.ExtensionData.endo_eq_of_fac`: *any* factorization of
  an endomorphism of `⦋M + 1⦌` through an `M`-truncated object computes `endo`. This is the
  well-definedness statement that makes the construction work, and it is where the uniqueness of
  epi-mono factorizations in `SimplexCategory` is used.
* `CategoryTheory.SimplicialObject.Truncated.ExtensionData.trunc_extend`: the `M`-truncation of
  the extension is `Y`, as an equality of functors.
* `CategoryTheory.SimplicialObject.Truncated.exists_extend`: the existence statement in the shape
  an induction on the truncation level consumes, with the degree-`M + 1` term identified.
* `SimplexCategory.image_len_lt_of_ne_id`: an endomorphism of an object of `SimplexCategory` other
  than the identity has strictly smaller image.

## Implementation notes

`obj` is defined by a dependent `if` on `x.obj.len ≤ M`, so neither `obj_of_le` nor
`obj_of_not_le` is definitional and every clause of `map` is conjugated by two `eqToHom`s. Those
cancel in pairs in each of the eight cases of `map_comp`, which is why each case is
`simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]` followed by one
structural rewrite. The `eqToHom`s in `SimplexCategory` itself, which appear because an object of
`SimplexCategory.Truncated (M + 1)` that is not `M`-truncated is only *equal* to `⦋M + 1⦌` rather
than identical to it, are cleared by the same `simp only` inside the arguments of `face`, `degen`
and `endo`.

The three compatibilities of `ExtensionData` are used only through the restatements `face_comp'`,
`degen_comp'`, `degen_face'` and their `reassoc` forms, because the goals in `map_comp` are
right-associated and a structure field carries no `reassoc` variant.

No universe is narrowed: `A : Type u` with `[Category.{v} A]` throughout, as in
`Mathlib.AlgebraicTopology.SimplicialObject.Basic`.

## References

Truncated simplicial objects are defined in
[Stacks, Tag 0180](https://stacks.math.columbia.edu/tag/0180) and the one-step extension producing
the coskeleton is [Stacks, Tag 0187](https://stacks.math.columbia.edu/tag/0187). The Stacks project
states no result of the present shape -- it builds such extensions by hand from explicit splitting
data wherever it needs them, calling the compatibilities "straightforward but cumbersome" -- so no
declaration here carries a Stacks tag. In particular the skeleton and coskeleton tags 017Z-018Q
and the definition 0180 do not cover this construction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe v u

namespace SimplexCategory

/-- An object of the `(n + 1)`-truncated simplex category which is not `n`-truncated is `⦋n + 1⦌`.
-/
theorem Truncated.obj_eq_mk_of_not_le {n : ℕ} {a : SimplexCategory.Truncated (n + 1)}
    (ha : ¬ a.obj.len ≤ n) : a.obj = ⦋n + 1⦌ :=
  SimplexCategory.ext (by have := a.property; change a.obj.len = n + 1; omega)

/-- The image of an endomorphism of `x` other than the identity is strictly smaller than `x`. -/
theorem image_len_lt_of_ne_id {x : SimplexCategory} {f : x ⟶ x} (hf : f ≠ 𝟙 x) :
    (image f).len < x.len := by
  rcases lt_or_eq_of_le (len_le_of_mono (image.ι f)) with h | h
  · exact h
  · have h₂ : IsIso (image.ι f) := (isIso_iff_of_mono (image.ι f)).2 h
    have h₃ : IsIso (factorThruImage f) := (isIso_iff_of_epi (factorThruImage f)).2 h.symm
    have h₄ : IsIso f := by rw [← image.fac f]; infer_instance
    exact absurd (eq_id_of_isIso f) hf

/-- An endomorphism of `⦋n + 1⦌` other than the identity has `n`-truncated image. -/
theorem image_len_le_of_ne_id {n : ℕ} {f : (⦋n + 1⦌ : SimplexCategory) ⟶ ⦋n + 1⦌}
    (hf : f ≠ 𝟙 _) : (image f).len ≤ n :=
  Nat.lt_succ_iff.1 (image_len_lt_of_ne_id hf)

end SimplexCategory

namespace CategoryTheory.SimplicialObject.Truncated

variable {A : Type u} [Category.{v} A] {M : ℕ}

/-- The data of a one-step extension of an `M`-truncated simplicial object `Y` of `A`. -/
structure ExtensionData (Y : SimplicialObject.Truncated A M) where
  /-- The object sitting in degree `M + 1`. -/
  pt : A
  /-- The face data: a morphism out of `pt` for every morphism of `SimplexCategory` from an
  `M`-truncated object into `⦋M + 1⦌`. -/
  face (x : SimplexCategory.Truncated M) (m : x.obj ⟶ ⦋M + 1⦌) : pt ⟶ Y.obj (op x)
  /-- The degeneracy data: a morphism into `pt` for every morphism of `SimplexCategory` from
  `⦋M + 1⦌` into an `M`-truncated object. -/
  degen (x : SimplexCategory.Truncated M) (e : (⦋M + 1⦌ : SimplexCategory) ⟶ x.obj) :
    Y.obj (op x) ⟶ pt
  /-- The face data is a cone: precomposing with a morphism of `SimplexCategory` is applying `Y`
  to it. -/
  face_comp (x y : SimplexCategory.Truncated M) (g : x.obj ⟶ y.obj) (m : y.obj ⟶ ⦋M + 1⦌) :
    face x (g ≫ m) = face y m ≫ Y.map (ObjectProperty.homMk g).op
  /-- The degeneracy data is a cocone: postcomposing with a morphism of `SimplexCategory` is
  applying `Y` to it. -/
  degen_comp (x y : SimplexCategory.Truncated M) (e : (⦋M + 1⦌ : SimplexCategory) ⟶ x.obj)
      (g : x.obj ⟶ y.obj) :
    degen y (e ≫ g) = Y.map (ObjectProperty.homMk g).op ≫ degen x e
  /-- A face after a degeneracy is computed inside `Y`. -/
  degen_face (x y : SimplexCategory.Truncated M) (e : (⦋M + 1⦌ : SimplexCategory) ⟶ x.obj)
      (m : y.obj ⟶ ⦋M + 1⦌) :
    degen x e ≫ face y m = Y.map (ObjectProperty.homMk (m ≫ e)).op

namespace ExtensionData

variable {Y : SimplicialObject.Truncated A M} (D : ExtensionData Y)

/-- Moving a morphism of `SimplexCategory` across from the degeneracy side to the face side. -/
theorem slide (x y : SimplexCategory.Truncated M) (e : (⦋M + 1⦌ : SimplexCategory) ⟶ x.obj)
    (g : x.obj ⟶ y.obj) (m : y.obj ⟶ ⦋M + 1⦌) :
    D.face y m ≫ D.degen y (e ≫ g) = D.face x (g ≫ m) ≫ D.degen x e := by
  rw [D.degen_comp x y e g, ← Category.assoc, D.face_comp x y g m]

/-- `face_comp` in the direction and shape in which it is rewritten. -/
@[reassoc]
theorem face_comp' (x y : SimplexCategory.Truncated M) (g : x.obj ⟶ y.obj)
    (m : y.obj ⟶ ⦋M + 1⦌) :
    D.face y m ≫ Y.map (ObjectProperty.homMk g).op = D.face x (g ≫ m) :=
  (D.face_comp x y g m).symm

/-- `degen_comp` in the direction and shape in which it is rewritten. -/
@[reassoc]
theorem degen_comp' (x y : SimplexCategory.Truncated M)
    (e : (⦋M + 1⦌ : SimplexCategory) ⟶ x.obj) (g : x.obj ⟶ y.obj) :
    Y.map (ObjectProperty.homMk g).op ≫ D.degen x e = D.degen y (e ≫ g) :=
  (D.degen_comp x y e g).symm

/-- `degen_face`, restated so that it can be used after `Category.assoc`. -/
@[reassoc]
theorem degen_face' (x y : SimplexCategory.Truncated M)
    (e : (⦋M + 1⦌ : SimplexCategory) ⟶ x.obj) (m : y.obj ⟶ ⦋M + 1⦌) :
    D.degen x e ≫ D.face y m = Y.map (ObjectProperty.homMk (m ≫ e)).op :=
  D.degen_face x y e m

/-- The object of the extension in degree `x`. -/
def obj (x : SimplexCategory.Truncated (M + 1)) : A :=
  if h : x.obj.len ≤ M then Y.obj (op ⟨x.obj, h⟩) else D.pt

/-- In degree at most `M` the object of the extension is that of `Y`. -/
theorem obj_of_le {x : SimplexCategory.Truncated (M + 1)} (h : x.obj.len ≤ M) :
    D.obj x = Y.obj (op ⟨x.obj, h⟩) := dite_eq_left h

/-- In degree `M + 1` the object of the extension is `pt`. -/
theorem obj_of_not_le {x : SimplexCategory.Truncated (M + 1)} (h : ¬ x.obj.len ≤ M) :
    D.obj x = D.pt := dite_eq_right h

/-- The action of the extension on an endomorphism of `⦋M + 1⦌`, read off the canonical epi-mono
factorization. -/
noncomputable def endo (f : (⦋M + 1⦌ : SimplexCategory) ⟶ ⦋M + 1⦌) : D.pt ⟶ D.pt :=
  if h : (image f).len ≤ M then
    D.face ⟨image f, h⟩ (image.ι f) ≫ D.degen ⟨image f, h⟩ (factorThruImage f)
  else 𝟙 D.pt

/-- An epi-mono factorization of an endomorphism of `⦋M + 1⦌` through an `M`-truncated object
computes `endo`. -/
theorem endo_eq_of_epi_mono_fac {w : SimplexCategory} (hw : w.len ≤ M)
    {f : (⦋M + 1⦌ : SimplexCategory) ⟶ ⦋M + 1⦌} (e : (⦋M + 1⦌ : SimplexCategory) ⟶ w)
    (m : w ⟶ ⦋M + 1⦌) [Epi e] [Mono m] (hf : e ≫ m = f) :
    D.endo f = D.face ⟨w, hw⟩ m ≫ D.degen ⟨w, hw⟩ e := by
  obtain rfl : w = image f := (SimplexCategory.image_eq hf).symm
  rw [endo, dite_eq_left hw, SimplexCategory.factorThruImage_eq hf,
    SimplexCategory.image_ι_eq hf]

/-- *Any* factorization of an endomorphism of `⦋M + 1⦌` through an `M`-truncated object computes
`endo`; this is the well-definedness of the degenerate part of degree `M + 1`. -/
theorem endo_eq_of_fac {w : SimplexCategory} (hw : w.len ≤ M)
    {f : (⦋M + 1⦌ : SimplexCategory) ⟶ ⦋M + 1⦌} (e : (⦋M + 1⦌ : SimplexCategory) ⟶ w)
    (m : w ⟶ ⦋M + 1⦌) (hf : e ≫ m = f) :
    D.endo f = D.face ⟨w, hw⟩ m ≫ D.degen ⟨w, hw⟩ e := by
  have hv₀ : (image e).len ≤ M := (SimplexCategory.len_le_of_mono (image.ι e)).trans hw
  have hv₁ : (image (image.ι e ≫ m)).len ≤ M :=
    (SimplexCategory.len_le_of_epi (factorThruImage (image.ι e ≫ m))).trans hv₀
  have hA : D.face ⟨w, hw⟩ m ≫ D.degen ⟨w, hw⟩ e
      = D.face ⟨image e, hv₀⟩ (image.ι e ≫ m)
        ≫ D.degen ⟨image e, hv₀⟩ (factorThruImage e) := by
    rw [← D.slide ⟨image e, hv₀⟩ ⟨w, hw⟩ (factorThruImage e) (image.ι e) m, image.fac e]
  have hB : D.face ⟨image e, hv₀⟩ (image.ι e ≫ m) ≫ D.degen ⟨image e, hv₀⟩ (factorThruImage e)
      = D.face ⟨image (image.ι e ≫ m), hv₁⟩ (image.ι (image.ι e ≫ m))
        ≫ D.degen ⟨image (image.ι e ≫ m), hv₁⟩
            (factorThruImage e ≫ factorThruImage (image.ι e ≫ m)) := by
    rw [D.slide ⟨image e, hv₀⟩ ⟨image (image.ι e ≫ m), hv₁⟩ (factorThruImage e)
      (factorThruImage (image.ι e ≫ m)) (image.ι (image.ι e ≫ m)), image.fac]
  rw [hA, hB]
  refine D.endo_eq_of_epi_mono_fac hv₁
    (factorThruImage e ≫ factorThruImage (image.ι e ≫ m))
    (image.ι (image.ι e ≫ m)) ?_
  rw [Category.assoc, image.fac, ← Category.assoc, image.fac, hf]

/-- `endo` sends the identity of `⦋M + 1⦌` to the identity of `pt`. -/
theorem endo_id : D.endo (𝟙 (⦋M + 1⦌ : SimplexCategory)) = 𝟙 D.pt := by
  have h : image (𝟙 (⦋M + 1⦌ : SimplexCategory)) = ⦋M + 1⦌ :=
    SimplexCategory.image_eq (e := 𝟙 _) (i := 𝟙 _) (by simp)
  rw [endo, dite_eq_right (by rw [h]; change ¬ M + 1 ≤ M; omega)]

/-- `endo f` followed by a face is the face along the composite with `f`. -/
@[reassoc]
theorem endo_comp_face (x : SimplexCategory.Truncated M)
    (f : (⦋M + 1⦌ : SimplexCategory) ⟶ ⦋M + 1⦌) (m : x.obj ⟶ ⦋M + 1⦌) :
    D.endo f ≫ D.face x m = D.face x (m ≫ f) := by
  by_cases hf : f = 𝟙 _
  · subst hf; rw [D.endo_id]; simp
  · have hw := SimplexCategory.image_len_le_of_ne_id hf
    rw [D.endo_eq_of_fac hw (factorThruImage f) (image.ι f) (image.fac f), Category.assoc,
      D.degen_face ⟨image f, hw⟩ x (factorThruImage f) m,
      ← D.face_comp x ⟨image f, hw⟩ (m ≫ factorThruImage f) (image.ι f), Category.assoc,
      image.fac f]

/-- A degeneracy followed by `endo f` is the degeneracy along the composite with `f`. -/
@[reassoc]
theorem degen_comp_endo (x : SimplexCategory.Truncated M)
    (f : (⦋M + 1⦌ : SimplexCategory) ⟶ ⦋M + 1⦌)
    (e : (⦋M + 1⦌ : SimplexCategory) ⟶ x.obj) :
    D.degen x e ≫ D.endo f = D.degen x (f ≫ e) := by
  by_cases hf : f = 𝟙 _
  · subst hf; rw [D.endo_id]; simp
  · have hw := SimplexCategory.image_len_le_of_ne_id hf
    rw [D.endo_eq_of_fac hw (factorThruImage f) (image.ι f) (image.fac f), ← Category.assoc,
      D.degen_face x ⟨image f, hw⟩ e (image.ι f),
      ← D.degen_comp ⟨image f, hw⟩ x (factorThruImage f) (image.ι f ≫ e), ← Category.assoc,
      image.fac f]

/-- `endo` is contravariantly functorial: `endo (f ≫ g) = endo g ≫ endo f`. -/
theorem endo_comp (f g : (⦋M + 1⦌ : SimplexCategory) ⟶ ⦋M + 1⦌) :
    D.endo (f ≫ g) = D.endo g ≫ D.endo f := by
  by_cases hf : f = 𝟙 _
  · subst hf; rw [D.endo_id]; simp
  have hw := SimplexCategory.image_len_le_of_ne_id hf
  rw [D.endo_eq_of_fac hw (factorThruImage f) (image.ι f ≫ g)
      (by rw [← Category.assoc, image.fac]),
    D.endo_eq_of_fac hw (factorThruImage f) (image.ι f) (image.fac f), ← Category.assoc,
    D.endo_comp_face ⟨image f, hw⟩ g (image.ι f)]

/-- `endo_comp` in the direction and shape in which it is rewritten. -/
@[reassoc]
theorem endo_comp' (f g : (⦋M + 1⦌ : SimplexCategory) ⟶ ⦋M + 1⦌) :
    D.endo g ≫ D.endo f = D.endo (f ≫ g) :=
  (D.endo_comp f g).symm

/-- The action of the extension on a morphism of the `(M + 1)`-truncated simplex category. -/
noncomputable def map (a b : SimplexCategory.Truncated (M + 1)) (f : a.obj ⟶ b.obj) :
    D.obj b ⟶ D.obj a :=
  if ha : a.obj.len ≤ M then
    if hb : b.obj.len ≤ M then
      eqToHom (D.obj_of_le hb)
        ≫ Y.map (ObjectProperty.homMk (X := (⟨a.obj, ha⟩ : SimplexCategory.Truncated M))
          (Y := ⟨b.obj, hb⟩) f).op
        ≫ eqToHom (D.obj_of_le ha).symm
    else
      eqToHom (D.obj_of_not_le hb)
        ≫ D.face ⟨a.obj, ha⟩ (f ≫ eqToHom (SimplexCategory.Truncated.obj_eq_mk_of_not_le hb))
        ≫ eqToHom (D.obj_of_le ha).symm
  else
    if hb : b.obj.len ≤ M then
      eqToHom (D.obj_of_le hb)
        ≫ D.degen ⟨b.obj, hb⟩
            (eqToHom (SimplexCategory.Truncated.obj_eq_mk_of_not_le ha).symm ≫ f)
        ≫ eqToHom (D.obj_of_not_le ha).symm
    else
      eqToHom (D.obj_of_not_le hb)
        ≫ D.endo (eqToHom (SimplexCategory.Truncated.obj_eq_mk_of_not_le ha).symm ≫ f
            ≫ eqToHom (SimplexCategory.Truncated.obj_eq_mk_of_not_le hb))
        ≫ eqToHom (D.obj_of_not_le ha).symm

/-- `map` between two objects of degree at most `M` is the action of `Y`. -/
theorem map_of_le_le (a b : SimplexCategory.Truncated (M + 1)) (f : a.obj ⟶ b.obj)
    (ha : a.obj.len ≤ M) (hb : b.obj.len ≤ M) :
    D.map a b f = eqToHom (D.obj_of_le hb)
      ≫ Y.map (ObjectProperty.homMk (X := (⟨a.obj, ha⟩ : SimplexCategory.Truncated M))
          (Y := ⟨b.obj, hb⟩) f).op
      ≫ eqToHom (D.obj_of_le ha).symm := by
  rw [map, dite_eq_left ha, dite_eq_left hb]

/-- `map` from an object of degree at most `M` into `⦋M + 1⦌` is a face. -/
theorem map_of_le_not_le (a b : SimplexCategory.Truncated (M + 1)) (f : a.obj ⟶ b.obj)
    (ha : a.obj.len ≤ M) (hb : ¬ b.obj.len ≤ M) :
    D.map a b f = eqToHom (D.obj_of_not_le hb)
      ≫ D.face ⟨a.obj, ha⟩ (f ≫ eqToHom (SimplexCategory.Truncated.obj_eq_mk_of_not_le hb))
      ≫ eqToHom (D.obj_of_le ha).symm := by
  rw [map, dite_eq_left ha, dite_eq_right hb]

/-- `map` from `⦋M + 1⦌` into an object of degree at most `M` is a degeneracy. -/
theorem map_of_not_le_le (a b : SimplexCategory.Truncated (M + 1)) (f : a.obj ⟶ b.obj)
    (ha : ¬ a.obj.len ≤ M) (hb : b.obj.len ≤ M) :
    D.map a b f = eqToHom (D.obj_of_le hb)
      ≫ D.degen ⟨b.obj, hb⟩
          (eqToHom (SimplexCategory.Truncated.obj_eq_mk_of_not_le ha).symm ≫ f)
      ≫ eqToHom (D.obj_of_not_le ha).symm := by
  rw [map, dite_eq_right ha, dite_eq_left hb]

/-- `map` on an endomorphism of `⦋M + 1⦌` is `endo`. -/
theorem map_of_not_le_not_le (a b : SimplexCategory.Truncated (M + 1)) (f : a.obj ⟶ b.obj)
    (ha : ¬ a.obj.len ≤ M) (hb : ¬ b.obj.len ≤ M) :
    D.map a b f = eqToHom (D.obj_of_not_le hb)
      ≫ D.endo (eqToHom (SimplexCategory.Truncated.obj_eq_mk_of_not_le ha).symm ≫ f
          ≫ eqToHom (SimplexCategory.Truncated.obj_eq_mk_of_not_le hb))
      ≫ eqToHom (D.obj_of_not_le ha).symm := by
  rw [map, dite_eq_right ha, dite_eq_right hb]

/-- `map` sends identities to identities. -/
theorem map_id (a : SimplexCategory.Truncated (M + 1)) :
    D.map a a (𝟙 a.obj) = 𝟙 (D.obj a) := by
  by_cases ha : a.obj.len ≤ M
  · rw [D.map_of_le_le a a _ ha ha]
    have h : ObjectProperty.homMk (X := (⟨a.obj, ha⟩ : SimplexCategory.Truncated M))
        (Y := ⟨a.obj, ha⟩) (𝟙 a.obj) = 𝟙 _ := rfl
    rw [h, op_id, Y.map_id]
    simp
  · rw [D.map_of_not_le_not_le a a _ ha ha]
    simp only [Category.id_comp, eqToHom_trans, eqToHom_refl]
    rw [D.endo_id]
    simp

/-- `map` sends a composite to the composite in the opposite order. -/
theorem map_comp (a b c : SimplexCategory.Truncated (M + 1)) (f : a.obj ⟶ b.obj)
    (g : b.obj ⟶ c.obj) : D.map a c (f ≫ g) = D.map b c g ≫ D.map a b f := by
  by_cases ha : a.obj.len ≤ M <;> by_cases hb : b.obj.len ≤ M <;> by_cases hc : c.obj.len ≤ M <;>
    simp only [map, ha, hb, hc, ↓reduceDIte, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
  · have h : ObjectProperty.homMk (X := (⟨a.obj, ha⟩ : SimplexCategory.Truncated M))
        (Y := ⟨c.obj, hc⟩) (f ≫ g)
        = ObjectProperty.homMk (X := (⟨a.obj, ha⟩ : SimplexCategory.Truncated M))
            (Y := ⟨b.obj, hb⟩) f
          ≫ ObjectProperty.homMk (X := (⟨b.obj, hb⟩ : SimplexCategory.Truncated M))
            (Y := ⟨c.obj, hc⟩) g := rfl
    rw [h, op_comp, Y.map_comp]
    simp
  · rw [D.face_comp'_assoc]
  · rw [D.degen_face'_assoc]
    simp
  · rw [D.endo_comp_face_assoc]
    simp
  · rw [D.degen_comp'_assoc]
    simp
  · rw [D.endo_eq_of_fac hb (eqToHom
        (SimplexCategory.Truncated.obj_eq_mk_of_not_le ha).symm ≫ f)
      (g ≫ eqToHom (SimplexCategory.Truncated.obj_eq_mk_of_not_le hc)) (by simp)]
    simp
  · rw [D.degen_comp_endo_assoc]
    simp
  · rw [D.endo_comp'_assoc]
    simp

/-- The `(M + 1)`-truncated simplicial object extending `Y` by the data `D`. -/
@[simps obj]
noncomputable def extend : SimplicialObject.Truncated A (M + 1) where
  obj x := D.obj x.unop
  map u := D.map _ _ u.unop.hom
  map_id x := D.map_id x.unop
  map_comp u v := D.map_comp _ _ _ v.unop.hom u.unop.hom

/-- The action of `extend` on a morphism is `map`. -/
theorem extend_map {x y : (SimplexCategory.Truncated (M + 1))ᵒᵖ} (u : x ⟶ y) :
    D.extend.map u = D.map y.unop x.unop u.unop.hom := rfl

/-- The degree-`M + 1` term of `extend` is `pt`. -/
theorem extend_obj_mk : D.extend.obj (op ⟨⦋M + 1⦌, le_rfl⟩) = D.pt :=
  D.obj_of_not_le (by change ¬ M + 1 ≤ M; omega)

/-- The `M`-truncation of the extension is `Y`, on the nose. -/
theorem trunc_extend : (SimplicialObject.Truncated.trunc A (M + 1) M).obj D.extend = Y := by
  refine Functor.ext (fun x => D.obj_of_le (x := ⟨x.unop.obj, _⟩) x.unop.property)
    (fun x y u => ?_)
  rw [show (((SimplicialObject.Truncated.trunc A (M + 1) M).obj D.extend).map u)
      = D.map ⟨y.unop.obj, y.unop.property.trans (Nat.le_succ M)⟩
          ⟨x.unop.obj, x.unop.property.trans (Nat.le_succ M)⟩ u.unop.hom from rfl,
    D.map_of_le_le _ _ _ y.unop.property x.unop.property]
  rfl

end ExtensionData

/-- The one-step extension data carried by a genuine simplicial object: the faces and the
degeneracies in degree `M + 1` are just the action of the simplicial object on morphisms into and
out of `⦋M + 1⦌`. This says that the three compatibilities of `ExtensionData` are exactly the
functoriality available in that situation, so the notion is not vacuous. -/
def ExtensionData.ofSimplicialObject (K : SimplicialObject A) :
    ExtensionData ((SimplicialObject.truncation M).obj K) where
  pt := K.obj (op ⦋M + 1⦌)
  face _ m := K.map m.op
  degen _ e := K.map e.op
  face_comp _ _ g m := K.map_comp m.op g.op
  degen_comp _ _ e g := K.map_comp g.op e.op
  degen_face _ _ e m := (K.map_comp e.op m.op).symm

/-- **One-step extension of a truncated simplicial object.** From the data of an object in degree
`M + 1` together with compatible face and degeneracy families, there is an `(M + 1)`-truncated
simplicial object whose `M`-truncation is `Y` on the nose and whose degree-`M + 1` term is the
given object. -/
theorem exists_extend {Y : SimplicialObject.Truncated A M} (D : ExtensionData Y) :
    ∃ Z : SimplicialObject.Truncated A (M + 1),
      (SimplicialObject.Truncated.trunc A (M + 1) M).obj Z = Y ∧
        Z.obj (op ⟨⦋M + 1⦌, le_rfl⟩) = D.pt :=
  ⟨D.extend, D.trunc_extend, D.extend_obj_mk⟩

end CategoryTheory.SimplicialObject.Truncated
