module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.SecondDiagonal

/-!
# The morphisms of a base change of a diagonal (Stacks 07WG)

Fix a base category `𝒞`, two categories `p𝒮 : 𝒮 ⥤ 𝒞` and `p𝒮' : 𝒮' ⥤ 𝒞` over `𝒞` and a
1-morphism `G : 𝒮 ⥤ 𝒮'` over `𝒞`, and write `Δ_G : 𝒮 ⥤ 𝒮 ×_{𝒮'} 𝒮` for its diagonal. For a
further category `p𝒱 : 𝒱 ⥤ 𝒞` over `𝒞` and a 1-morphism `g : 𝒱 ⥤ 𝒮 ×_{𝒮'} 𝒮` this file
describes the morphisms of the base change

`𝒴 = 𝒮 ×_{Δ_G, 𝒮 ×_{𝒮'} 𝒮, g} 𝒱`.

An object of `𝒴` over `T` is a quadruple `(z, v, α, β)` with `z` an object of `𝒮` over `T`, `v`
an object of `𝒱` over `T` and `α : z ≅ g(v)₁`, `β : z ≅ g(v)₂` the two components of the
comparison isomorphism `Δ_G z ≅ g(v)` — the two components of an isomorphism of `𝒮 ×_{𝒮'} 𝒮`
whose source has both components equal to `z`. They are `fstIso` and `sndIso` below.

The point of the file is the following description of a morphism
`(z₁, v₁, α₁, β₁) ⟶ (z₂, v₂, α₂, β₂)` of `𝒴`, which is the formal content of the proof of
Stacks 07WG:

> a morphism of `𝒴` is **determined** by its `𝒱`-component `n : v₁ ⟶ v₂`, and a `𝒱`-morphism `n`
> is the `𝒱`-component of a morphism of `𝒴` **exactly when the two morphisms `z₁ ⟶ z₂` that `n`
> induces through `α` and through `β` agree**:
> `α₁ ∘ g(n)₁ ∘ α₂⁻¹ = β₁ ∘ g(n)₂ ∘ β₂⁻¹`.

In the situation of Stacks 07WG, `𝒮 = 𝒳` is a category fibred in groupoids over the big fppf
site, `G` is its structure functor (so `Δ_G` is the absolute diagonal `Δ : 𝒳 ⟶ 𝒳 × 𝒳`), `𝒱` is
the category represented by a scheme `V` and `g` is a pair `(x, y)` of objects of `𝒳` over `V`.
The description then reads: an isomorphism of `𝒴` over `V'` is a morphism `V' ⟶ V` over which the
two pullbacks `α` and `β` of the given pair of isomorphisms agree — which is the source's
sentence *"condition (2) now says that the condition `α = β` defines an algebraic space"*.
Comparing it with the source's reading of condition (1), *"the condition `α = id` defines an
algebraic space"*, is then the substitution `α ↦ α⁻¹ ∘ β`.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.DiagonalBaseChange.Total`: the base change `𝒴`.
* `CategoryTheory.TwoFibreProductOver.DiagonalBaseChange.fstIso`,
  `CategoryTheory.TwoFibreProductOver.DiagonalBaseChange.sndIso`: the two components `α`, `β` of
  the comparison isomorphism of an object of `𝒴`.
* `CategoryTheory.TwoFibreProductOver.DiagonalBaseChange.vertHomOfB`: the morphism of `𝒴` over an
  identity of `𝒞` determined by a vertical `𝒱`-morphism satisfying the compatibility.

## Main results

* `CategoryTheory.TwoFibreProductOver.DiagonalBaseChange.compat`: the compatibility is necessary.
* `CategoryTheory.TwoFibreProductOver.DiagonalBaseChange.hom_ext_of_b`,
  `CategoryTheory.TwoFibreProductOver.DiagonalBaseChange.hom_injective_b` and
  `CategoryTheory.TwoFibreProductOver.DiagonalBaseChange.subsingleton_hom`: a morphism of `𝒴` is
  determined by its `𝒱`-component.
* `CategoryTheory.TwoFibreProductOver.DiagonalBaseChange.exists_hom_b_eq_iff`: the two together,
  for a vertical `𝒱`-morphism — the characterization displayed above.

## Implementation notes

`CategoryTheory.TwoFibreProductOver.diagonal` is a plain `def`, and the two components of
`Δ_G z` are the same object `z` of `𝒮`; as in
`StacksFrontier/CategoryTheory/FiberedInGroupoids/Diagonal.lean` and
`StacksFrontier/CategoryTheory/FiberedInGroupoids/SecondDiagonal.lean`, the composites of components
below need that at instance transparency, which the `attribute [local instance_reducible]` line
supplies.

Both halves of the characterization are proved by reading off the comparison square `Hom.w` of a
morphism of the 2-fibre product in the two components of `𝒮 ×_{𝒮'} 𝒮`: in the first component it
*defines* the `𝒮`-component of the morphism, because `Δ_G` is the identity there, and in the
second it is the compatibility. Nothing is assumed fibred in groupoids: the `𝒮`-component is
produced from the given data, not lifted.

The existence half is stated for a morphism over an identity of `𝒞` — the one case a presheaf of
isomorphisms needs — because the base morphism of the resulting morphism of `𝒴` has then a closed
form, and the factorization `IsHomLift.fac'` of its `𝒮`-component reduces to an identity of
`eqToHom`s. For that reduction to go through, the two spellings `(g.obj v).base` and
`(g ⋙ structureFunctor …).obj v` of one object have to be made to agree, which is what
`CategoryTheory.TwoFibreProductOver.DiagonalBaseChange.base_obj_eq` is for: `eqToHom` is matched
syntactically by `simp`, and the lemmas that compose two of them do not fire across the two
spellings.

## References

* [Stacks Project, Tag 07WG](https://stacks.math.columbia.edu/tag/07WG)
* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.TwoFibreProductOver.DiagonalBaseChange

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮]
  {𝒮' : Type u₃} [Category.{v₃} 𝒮'] {𝒱 : Type u₄} [Category.{v₄} 𝒱]
  {p𝒮 : 𝒮 ⥤ 𝒞} {p𝒮' : 𝒮' ⥤ 𝒞} {p𝒱 : 𝒱 ⥤ 𝒞} {G : 𝒮 ⥤ 𝒮'}

attribute [local instance_reducible] diagonal

/-- The base change `𝒮 ×_{Δ_G, 𝒮 ×_{𝒮'} 𝒮, g} 𝒱` of the diagonal of `G` along a 1-morphism `g`
into the 2-product `𝒮 ×_{𝒮'} 𝒮`. -/
abbrev Total (p𝒱 : 𝒱 ⥤ 𝒞) (hG : G ⋙ p𝒮' = p𝒮)
    (g : 𝒱 ⥤ TwoFibreProductOver p𝒮 p𝒮 p𝒮' G G) : Type _ :=
  TwoFibreProductOver p𝒮 p𝒱 (structureFunctor p𝒮 p𝒮 p𝒮' G G) (diagonal hG) g

variable (hG : G ⋙ p𝒮' = p𝒮) {g : 𝒱 ⥤ TwoFibreProductOver p𝒮 p𝒮 p𝒮' G G}

/-- The first component `α` of the comparison isomorphism of an object `(z, v, α, β)` of the base
change: an isomorphism of `z` with the first component of `g v`. -/
@[simps]
def fstIso (t : Total p𝒱 hG g) : t.x ≅ (g.obj t.y).x where
  hom := t.iso.hom.a
  inv := t.iso.inv.a
  hom_inv_id := by
    simpa only [comp_a, id_a, diagonal_obj_x] using congrArg Hom.a t.iso.hom_inv_id
  inv_hom_id := by
    simpa only [comp_a, id_a, diagonal_obj_x] using congrArg Hom.a t.iso.inv_hom_id

/-- The second component `β` of the comparison isomorphism of an object `(z, v, α, β)` of the
base change: an isomorphism of `z` with the second component of `g v`. -/
@[simps]
def sndIso (t : Total p𝒱 hG g) : t.x ≅ (g.obj t.y).y where
  hom := t.iso.hom.b
  inv := t.iso.inv.b
  hom_inv_id := by
    simpa only [comp_b, id_b, diagonal_obj_y] using congrArg Hom.b t.iso.hom_inv_id
  inv_hom_id := by
    simpa only [comp_b, id_b, diagonal_obj_y] using congrArg Hom.b t.iso.inv_hom_id

section Hom

variable {t₁ t₂ : Total p𝒱 hG g}

/-- The comparison square of a morphism of the base change, in the first component. -/
lemma a_comp_fstIso (u : t₁ ⟶ t₂) :
    u.a ≫ (fstIso hG t₂).hom = (fstIso hG t₁).hom ≫ (g.map u.b).a := by
  simpa only [fstIso_hom, comp_a, diagonal_map_a] using congrArg Hom.a u.w

/-- The comparison square of a morphism of the base change, in the second component. -/
lemma a_comp_sndIso (u : t₁ ⟶ t₂) :
    u.a ≫ (sndIso hG t₂).hom = (sndIso hG t₁).hom ≫ (g.map u.b).b := by
  simpa only [sndIso_hom, comp_b, diagonal_map_b] using congrArg Hom.b u.w

/-- The `𝒮`-component of a morphism of the base change is the morphism its `𝒱`-component induces
through the first components of the two comparison isomorphisms. -/
lemma a_eq (u : t₁ ⟶ t₂) :
    u.a = (fstIso hG t₁).hom ≫ (g.map u.b).a ≫ (fstIso hG t₂).inv := by
  rw [← Category.assoc, ← a_comp_fstIso hG u, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The `𝒮`-component of a morphism of the base change is also the morphism its `𝒱`-component
induces through the second components of the two comparison isomorphisms. -/
lemma a_eq' (u : t₁ ⟶ t₂) :
    u.a = (sndIso hG t₁).hom ≫ (g.map u.b).b ≫ (sndIso hG t₂).inv := by
  rw [← Category.assoc, ← a_comp_sndIso hG u, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **The compatibility.** The `𝒱`-component of a morphism of the base change induces the same
morphism `z₁ ⟶ z₂` through the first components of the comparison isomorphisms as through the
second. In the situation of Stacks 07WG this is the condition `α = β`. -/
lemma compat (u : t₁ ⟶ t₂) :
    (fstIso hG t₁).hom ≫ (g.map u.b).a ≫ (fstIso hG t₂).inv
      = (sndIso hG t₁).hom ≫ (g.map u.b).b ≫ (sndIso hG t₂).inv :=
  (a_eq hG u).symm.trans (a_eq' hG u)

/-- A morphism of the base change is determined by its `𝒱`-component. -/
lemma hom_ext_of_b {u u' : t₁ ⟶ t₂} (h : u.b = u'.b) : u = u' :=
  Hom.ext' (by rw [a_eq hG u, a_eq hG u', h]) h

/-- Taking the `𝒱`-component is injective on the morphisms of the base change. -/
lemma hom_injective_b : Function.Injective (fun u : t₁ ⟶ t₂ => Hom.b u) :=
  fun _ _ h => hom_ext_of_b hG h

/-- There is at most one morphism of the base change between two objects as soon as there is at
most one morphism between their `𝒱`-components. For `𝒱` fibred in setoids — in particular for `𝒱`
represented by a scheme, which is the case of Stacks 07WG — this makes the presheaf of
isomorphisms of the base change a subobject of the final presheaf, and so a target for
`CategoryTheory.presheafIsoOfSubsingleton`. -/
lemma subsingleton_hom (h : Subsingleton (t₁.y ⟶ t₂.y)) : Subsingleton (t₁ ⟶ t₂) :=
  ⟨fun _ _ => hom_ext_of_b hG (h.allEq _ _)⟩

end Hom

section Base

/-- The base of the value of `g` at the `𝒱`-component of an object of the base change is the base
of that object: the comparison isomorphism is vertical. -/
lemma base_eq (t : Total p𝒱 hG g) : (g.obj t.y).base = t.base := by
  have := t.vertical
  exact IsHomLift.codomain_eq (structureFunctor p𝒮 p𝒮 p𝒮' G G) (𝟙 t.base) t.iso.hom

/-- The base morphism of the comparison isomorphism of an object of the base change is the
canonical identification of the two bases. -/
lemma iso_hom_hbase (t : Total p𝒱 hG g) :
    t.iso.hom.hbase = eqToHom t.hx ≫ eqToHom (base_eq hG t).symm := by
  have := t.vertical
  have h := IsHomLift.fac' (structureFunctor p𝒮 p𝒮 p𝒮' G G) (𝟙 t.base) t.iso.hom
  rw [structureFunctor_map] at h
  rw [h]
  simp only [Category.id_comp, eqToHom_trans]
  rfl

variable (t : Total p𝒱 hG g)

/-- The first component of the comparison isomorphism lies over the canonical identification of
the bases. -/
lemma map_fstIso_hom :
    p𝒮.map (fstIso hG t).hom
      = eqToHom t.hx ≫ eqToHom ((g.obj t.y).hx.trans (base_eq hG t)).symm := by
  have := t.iso.hom.ha
  have h := IsHomLift.fac' p𝒮 t.iso.hom.hbase t.iso.hom.a
  rw [fstIso_hom, h]
  simp only [iso_hom_hbase hG t, eqToHom_trans]

/-- The second component of the comparison isomorphism lies over the canonical identification of
the bases. -/
lemma map_sndIso_hom :
    p𝒮.map (sndIso hG t).hom
      = eqToHom t.hx ≫ eqToHom ((g.obj t.y).hy.trans (base_eq hG t)).symm := by
  have := t.iso.hom.hb
  have h := IsHomLift.fac' p𝒮 t.iso.hom.hbase t.iso.hom.b
  rw [sndIso_hom, h]
  simp only [iso_hom_hbase hG t, eqToHom_trans]

/-- The inverse of the first component lies over the inverse identification. -/
lemma map_fstIso_inv :
    p𝒮.map (fstIso hG t).inv
      = eqToHom ((g.obj t.y).hx.trans (base_eq hG t)) ≫ eqToHom t.hx.symm := by
  rw [← cancel_epi (p𝒮.map (fstIso hG t).hom), ← p𝒮.map_comp, Iso.hom_inv_id, p𝒮.map_id,
    map_fstIso_hom hG t]
  simp

/-- The inverse of the second component lies over the inverse identification. -/
lemma map_sndIso_inv :
    p𝒮.map (sndIso hG t).inv
      = eqToHom ((g.obj t.y).hy.trans (base_eq hG t)) ≫ eqToHom t.hx.symm := by
  rw [← cancel_epi (p𝒮.map (sndIso hG t).hom), ← p𝒮.map_comp, Iso.hom_inv_id, p𝒮.map_id,
    map_sndIso_hom hG t]
  simp

end Base

/-- The first component of a morphism of the 2-product `𝒮 ×_{𝒮'} 𝒮` lies over its base
morphism. -/
lemma map_g_a {v₁ v₂ : 𝒱} (n : v₁ ⟶ v₂) :
    p𝒮.map (g.map n).a
      = eqToHom (g.obj v₁).hx ≫ (g.map n).hbase ≫ eqToHom (g.obj v₂).hx.symm := by
  rw [Hom.hbase_eq (g.map n)]
  simp

/-- The second component of a morphism of the 2-product `𝒮 ×_{𝒮'} 𝒮` lies over its base
morphism. -/
lemma map_g_b {v₁ v₂ : 𝒱} (n : v₁ ⟶ v₂) :
    p𝒮.map (g.map n).b
      = eqToHom (g.obj v₁).hy ≫ (g.map n).hbase ≫ eqToHom (g.obj v₂).hy.symm := by
  have h : (g.map n).hbase = eqToHom (g.obj v₁).hy.symm ≫ p𝒮.map (g.map n).b
      ≫ eqToHom (g.obj v₂).hy := by
    have := (g.map n).hb
    rw [IsHomLift.fac' p𝒮 (g.map n).hbase (g.map n).b]
    simp
  rw [h]
  simp

section OneMorphism

variable (hg : g ⋙ structureFunctor p𝒮 p𝒮 p𝒮' G G = p𝒱)

include hg in
/-- `g` being a 1-morphism over `𝒞`, the base of the value of `g` at an object of `𝒱` is the base
of that object. Stated at this spelling of the two objects, rather than at the one
`CategoryTheory.Functor.congr_obj` produces, so that `eqToHom`s built from it compose with those
built from the fields of an object of the 2-product. -/
lemma base_obj_eq (v : 𝒱) : (g.obj v).base = p𝒱.obj v := Functor.congr_obj hg v

/-- `g` being a 1-morphism over `𝒞`, the base morphism of `g n` is the image of `n` in `𝒞`. -/
lemma map_hbase_eq {v₁ v₂ : 𝒱} (n : v₁ ⟶ v₂) :
    (g.map n).hbase = eqToHom (base_obj_eq hg v₁) ≫ p𝒱.map n
      ≫ eqToHom (base_obj_eq hg v₂).symm := by
  rw [show (g.map n).hbase = (g ⋙ structureFunctor p𝒮 p𝒮 p𝒮' G G).map n from rfl,
    Functor.congr_hom hg n]
  rfl

variable {t₁ t₂ : Total p𝒱 hG g}

/-- **The morphism of the base change determined by a vertical `𝒱`-morphism satisfying the
compatibility.** Its `𝒮`-component is the morphism the `𝒱`-component induces through the first
components of the two comparison isomorphisms; the compatibility is what makes the comparison
square commute in the second component as well. -/
def vertHomOfB (hb : t₁.base = t₂.base)
    (n : t₁.y ⟶ t₂.y) (hn : p𝒱.IsHomLift (eqToHom hb) n)
    (hcompat : (fstIso hG t₁).hom ≫ (g.map n).a ≫ (fstIso hG t₂).inv
      = (sndIso hG t₁).hom ≫ (g.map n).b ≫ (sndIso hG t₂).inv) : t₁ ⟶ t₂ where
  hbase := eqToHom hb
  a := (fstIso hG t₁).hom ≫ (g.map n).a ≫ (fstIso hG t₂).inv
  b := n
  ha := by
    refine IsHomLift.of_fac' p𝒮 (eqToHom hb) _ t₁.hx t₂.hx ?_
    have hv := IsHomLift.fac' p𝒱 (eqToHom hb) n
    simp only [Functor.map_comp, map_fstIso_hom hG t₁, map_fstIso_inv hG t₂,
      map_g_a n, map_hbase_eq hg n, hv]
    simp only [eqToHom_trans]
  hb := hn
  w := by
    have hfst : ((fstIso hG t₁).hom ≫ (g.map n).a ≫ (fstIso hG t₂).inv) ≫ (fstIso hG t₂).hom
        = (fstIso hG t₁).hom ≫ (g.map n).a := by
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hsnd : ((fstIso hG t₁).hom ≫ (g.map n).a ≫ (fstIso hG t₂).inv) ≫ (sndIso hG t₂).hom
        = (sndIso hG t₁).hom ≫ (g.map n).b := by
      rw [hcompat]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact Hom.ext' hfst hsnd

/-- The `𝒱`-component of `vertHomOfB` is the given `𝒱`-morphism. -/
@[simp] lemma vertHomOfB_b (hb : t₁.base = t₂.base)
    (n : t₁.y ⟶ t₂.y) (hn : p𝒱.IsHomLift (eqToHom hb) n)
    (hcompat : (fstIso hG t₁).hom ≫ (g.map n).a ≫ (fstIso hG t₂).inv
      = (sndIso hG t₁).hom ≫ (g.map n).b ≫ (sndIso hG t₂).inv) :
    (vertHomOfB hG hg hb n hn hcompat).b = n := rfl

/-- The `𝒮`-component of `vertHomOfB` is the morphism the `𝒱`-component induces through the first
components of the two comparison isomorphisms. -/
@[simp] lemma vertHomOfB_a (hb : t₁.base = t₂.base)
    (n : t₁.y ⟶ t₂.y) (hn : p𝒱.IsHomLift (eqToHom hb) n)
    (hcompat : (fstIso hG t₁).hom ≫ (g.map n).a ≫ (fstIso hG t₂).inv
      = (sndIso hG t₁).hom ≫ (g.map n).b ≫ (sndIso hG t₂).inv) :
    (vertHomOfB hG hg hb n hn hcompat).a
      = (fstIso hG t₁).hom ≫ (g.map n).a ≫ (fstIso hG t₂).inv := rfl

include hg in
/-- **The morphisms of a base change of a diagonal, Stacks 07WG.** A vertical `𝒱`-morphism
`n : v₁ ⟶ v₂` is the `𝒱`-component of a morphism `(z₁, v₁, α₁, β₁) ⟶ (z₂, v₂, α₂, β₂)` of the
base change if and only if the morphism `z₁ ⟶ z₂` it induces through the first components of the
two comparison isomorphisms agrees with the one it induces through the second components. Such a
morphism is then unique, by
`CategoryTheory.TwoFibreProductOver.DiagonalBaseChange.hom_ext_of_b`. -/
theorem exists_hom_b_eq_iff (hb : t₁.base = t₂.base) (n : t₁.y ⟶ t₂.y)
    (hn : p𝒱.IsHomLift (eqToHom hb) n) :
    (∃ u : t₁ ⟶ t₂, u.b = n) ↔
      (fstIso hG t₁).hom ≫ (g.map n).a ≫ (fstIso hG t₂).inv
        = (sndIso hG t₁).hom ≫ (g.map n).b ≫ (sndIso hG t₂).inv := by
  constructor
  · rintro ⟨u, rfl⟩
    exact compat hG u
  · intro h
    exact ⟨vertHomOfB hG hg hb n hn h, rfl⟩

end OneMorphism

end CategoryTheory.TwoFibreProductOver.DiagonalBaseChange

end
