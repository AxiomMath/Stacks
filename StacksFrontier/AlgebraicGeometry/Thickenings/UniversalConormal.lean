module

public import StacksFrontier.AlgebraicGeometry.Thickenings.Conormal
public import StacksFrontier.AlgebraicGeometry.Thickenings.Universal

/-!
# The conormal module of a universal first-order thickening

Let `h : Z ⟶ X` be a morphism of schemes admitting a universal first-order thickening
`Z ⟶ Z'` over `X`. Following [Stacks Project, Tag 04F4], the conormal sheaf `𝒞_{Z/X}` of `h` is
the conormal sheaf of the inclusion `Z ⟶ Z'`. A commutative square
```
Z --h--→ X
|        |
f        g
↓        ↓
W --h'-→ Y
```
and universal first-order thickenings `Z ⟶ Z'` of `h` and `W ⟶ W'` of `h'` determine the
canonical morphism `Z' ⟶ W'` of `Stacks.Thickenings.universalFirstOrderThickeningMap`, and this
morphism of thickenings induces the canonical map of conormal sheaves
`f^*𝒞_{W/Y} → 𝒞_{Z/X}`. That is the second assertion of [Stacks Project, Tag 04F7].

This file proves the uniqueness assertion of the section [Stacks Project, Tag 04F2]: a universal
first-order thickening is unique up to unique isomorphism, a consequence of the uniqueness clause
of Tag 04F7. It also constructs the induced map of conormal modules for an affine ambient
thickening, the specialization of `Stacks.Thickenings.conormalMap` to the canonical morphism of
universal thickenings, and shows that the conormal module of `h` is, up to canonical isomorphism,
independent of the chosen universal first-order thickening.

## Main definitions

* `Stacks.Thickenings.UniversalFirstOrderThickening.canonicalMap` is the canonical morphism
  between the ambient schemes of two universal first-order thickenings of the *same* morphism.
* `Stacks.Thickenings.UniversalFirstOrderThickening.canonicalIso` is the resulting isomorphism.
* `Stacks.Thickenings.universalConormalMap` is the map of conormal modules induced by the
  canonical morphism of universal first-order thickenings attached to a commutative square, for
  affine ambient thickenings.

## Main results

* `Stacks.Thickenings.UniversalFirstOrderThickening.existsUnique_canonicalMap`: a universal
  first-order thickening is unique up to unique isomorphism — there is exactly one morphism
  between the ambient schemes of two universal first-order thickenings of the same morphism
  which is compatible with the inclusions and the structure morphisms, and it is an isomorphism
  (`Stacks.Thickenings.UniversalFirstOrderThickening.isIso_of_inclusion_of_toBase`).
* `Stacks.Thickenings.universalFirstOrderThickeningMap_comp`: the canonical morphism of
  thickenings is functorial in the commutative square.
* `Stacks.Thickenings.universalConormalMap_apply`: on underlying sections the induced map of
  conormal modules is the ring map of the canonical morphism of universal thickenings. This is
  the affine characterization of [Stacks Project, Tag 01R4] for this square.
* `Stacks.Thickenings.universalConormalMap_comp_apply`: the induced map of conormal modules is
  functorial.
* `Stacks.Thickenings.bijective_conormalMap_canonicalMap`: the conormal module of a morphism does
  not depend on the choice of universal first-order thickening.

## Implementation notes

`Stacks.Thickenings.UniversalFirstOrderThickening.canonicalMap` is
`Stacks.Thickenings.universalFirstOrderThickeningMap` at the identity square, so the three
lemmas about it are the three clauses of Tag 04F7 with `Category.id_comp` and
`Category.comp_id` applied. Nothing in this section is tagged: Tag 04F2 is a section of the
Stacks Project, not a numbered lemma, so it has no audit entity, and the content is the already
tagged uniqueness clause of Tag 04F7 rather than a new assertion.

What is tagged `04F7` here is the *module-level* induced map on an affine ambient thickening, not
the morphism of conormal sheaves `f^*𝒞_{W/Y} → 𝒞_{Z/X}` that the tag asserts. The clause text
says so. The sheaf-level statement needs the conormal sheaf of an immersion
([Stacks Project, Tag 01R2]) and its affine description ([Stacks Project, Tag 01R3]), neither of
which is in the library; see the module docstring of
`StacksFrontier.AlgebraicGeometry.Thickenings.Conormal` for what the affine statement is and is
not. Since the tag sits on partial coverage, the `04F7` audit entry stays marked as not
faithful.

The affineness hypotheses are on the *ambient* schemes `Z'` and `W'`, which is what makes the
defining ideal of the thickening a module over `Γ(Z, ⊤)`; affineness of `Z` and `W` follows, a
closed subscheme of an affine scheme being affine.

## References

* [Stacks Project, Tag 04F7](https://stacks.math.columbia.edu/tag/04F7)
* [Stacks Project, Tag 04F4](https://stacks.math.columbia.edu/tag/04F4)
* [Stacks Project, Tag 04F2](https://stacks.math.columbia.edu/tag/04F2)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Thickenings

variable {Z X W Y : Scheme.{u}} {h : Z ⟶ X} {h' : W ⟶ Y}

/-! ### Functoriality of the canonical morphism of universal thickenings -/

/-- The canonical morphism between the ambient schemes of two universal first-order thickenings
is functorial: a vertical composite of commutative squares induces the composite morphism. -/
theorem universalFirstOrderThickeningMap_comp {V V' : Scheme.{u}} {h'' : V ⟶ V'}
    (tZ : UniversalFirstOrderThickening h) (tW : UniversalFirstOrderThickening h')
    (tV : UniversalFirstOrderThickening h'')
    (f : Z ⟶ W) (g : X ⟶ Y) (comm : h ≫ g = f ≫ h')
    (f' : W ⟶ V) (g' : Y ⟶ V') (comm' : h' ≫ g' = f' ≫ h'') :
    universalFirstOrderThickeningMap tZ tW f g comm ≫
        universalFirstOrderThickeningMap tW tV f' g' comm' =
      universalFirstOrderThickeningMap tZ tV (f ≫ f') (g ≫ g') (comm_comp comm comm') :=
  universalFirstOrderThickeningMap_unique tZ tV (f ≫ f') (g ≫ g') (comm_comp comm comm') _
    (by rw [← Category.assoc, universalFirstOrderThickeningMap_inclusion, Category.assoc,
      universalFirstOrderThickeningMap_inclusion, ← Category.assoc])
    (by rw [Category.assoc, universalFirstOrderThickeningMap_toBase, ← Category.assoc,
      universalFirstOrderThickeningMap_toBase, Category.assoc])

/-! ### Uniqueness of the universal first-order thickening -/

namespace UniversalFirstOrderThickening

/-- The canonical morphism between the ambient schemes of two universal first-order thickenings of
the *same* morphism `h : Z ⟶ X`: the canonical morphism of
`Stacks.Thickenings.universalFirstOrderThickeningMap` attached to the identity square on `h`. -/
noncomputable def canonicalMap (t₁ t₂ : UniversalFirstOrderThickening h) :
    t₁.ambient ⟶ t₂.ambient :=
  universalFirstOrderThickeningMap t₁ t₂ (𝟙 Z) (𝟙 X) (by simp)

/-- The canonical morphism between two universal first-order thickenings of `h` is compatible with
the inclusions of `Z`. -/
theorem canonicalMap_inclusion (t₁ t₂ : UniversalFirstOrderThickening h) :
    t₁.inclusion ≫ canonicalMap t₁ t₂ = t₂.inclusion := by
  rw [canonicalMap, universalFirstOrderThickeningMap_inclusion, Category.id_comp]

/-- The canonical morphism between two universal first-order thickenings of `h` is a morphism
over `X`. -/
theorem canonicalMap_toBase (t₁ t₂ : UniversalFirstOrderThickening h) :
    canonicalMap t₁ t₂ ≫ t₂.toBase = t₁.toBase := by
  rw [canonicalMap, universalFirstOrderThickeningMap_toBase, Category.comp_id]

/-- Any morphism between the ambient schemes of two universal first-order thickenings of `h` which
is compatible with the inclusions of `Z` and with the structure morphisms to `X` is the canonical
one. -/
theorem eq_canonicalMap (t₁ t₂ : UniversalFirstOrderThickening h) (k : t₁.ambient ⟶ t₂.ambient)
    (hk₁ : t₁.inclusion ≫ k = t₂.inclusion) (hk₂ : k ≫ t₂.toBase = t₁.toBase) :
    k = canonicalMap t₁ t₂ :=
  universalFirstOrderThickeningMap_unique t₁ t₂ (𝟙 Z) (𝟙 X) (by simp) k
    (by rw [hk₁, Category.id_comp]) (by rw [hk₂, Category.comp_id])

/-- **A universal first-order thickening is unique up to unique isomorphism.** Between the ambient
schemes of two universal first-order thickenings of `h : Z ⟶ X` there is exactly one morphism
compatible with the inclusions of `Z` and with the structure morphisms to `X`.

This is the uniqueness assertion of the section [Stacks Project, Tag 04F2]. That the unique
morphism is an isomorphism is
`Stacks.Thickenings.UniversalFirstOrderThickening.isIso_of_inclusion_of_toBase`. -/
theorem existsUnique_canonicalMap (t₁ t₂ : UniversalFirstOrderThickening h) :
    ∃! k : t₁.ambient ⟶ t₂.ambient,
      (t₁.inclusion ≫ k = t₂.inclusion) ∧ (k ≫ t₂.toBase = t₁.toBase) :=
  ⟨canonicalMap t₁ t₂, ⟨canonicalMap_inclusion t₁ t₂, canonicalMap_toBase t₁ t₂⟩,
    fun _ hk ↦ eq_canonicalMap t₁ t₂ _ hk.1 hk.2⟩

/-- The canonical morphism from a universal first-order thickening to itself is the identity. -/
theorem canonicalMap_self (t : UniversalFirstOrderThickening h) :
    canonicalMap t t = 𝟙 t.ambient :=
  universalFirstOrderThickeningMap_id t

/-- The canonical morphisms between universal first-order thickenings of `h` compose. -/
theorem canonicalMap_comp (t₁ t₂ t₃ : UniversalFirstOrderThickening h) :
    canonicalMap t₁ t₂ ≫ canonicalMap t₂ t₃ = canonicalMap t₁ t₃ :=
  universalFirstOrderThickeningMap_comp t₁ t₂ t₃ (𝟙 Z) (𝟙 X) (by simp) (𝟙 Z) (𝟙 X) (by simp)

/-- The canonical morphisms between two universal first-order thickenings of `h` are mutually
inverse. -/
theorem canonicalMap_comp_canonicalMap (t₁ t₂ : UniversalFirstOrderThickening h) :
    canonicalMap t₁ t₂ ≫ canonicalMap t₂ t₁ = 𝟙 t₁.ambient := by
  rw [canonicalMap_comp, canonicalMap_self]

/-- **Two universal first-order thickenings of the same morphism are canonically isomorphic.** -/
noncomputable def canonicalIso (t₁ t₂ : UniversalFirstOrderThickening h) :
    t₁.ambient ≅ t₂.ambient where
  hom := canonicalMap t₁ t₂
  inv := canonicalMap t₂ t₁
  hom_inv_id := canonicalMap_comp_canonicalMap t₁ t₂
  inv_hom_id := canonicalMap_comp_canonicalMap t₂ t₁

/-- Any morphism of thickenings over `X` between two universal first-order thickenings of `h` is
an isomorphism. -/
theorem isIso_of_inclusion_of_toBase (t₁ t₂ : UniversalFirstOrderThickening h)
    (k : t₁.ambient ⟶ t₂.ambient) (hk₁ : t₁.inclusion ≫ k = t₂.inclusion)
    (hk₂ : k ≫ t₂.toBase = t₁.toBase) : IsIso k := by
  rw [eq_canonicalMap t₁ t₂ k hk₁ hk₂]
  exact (canonicalIso t₁ t₂).isIso_hom

end UniversalFirstOrderThickening

/-! ### The induced map of conormal modules -/

open UniversalFirstOrderThickening in
/-- **The map of conormal modules induced by the canonical morphism of universal first-order
thickenings.** For universal first-order thickenings `tZ` of `h : Z ⟶ X` and `tW` of
`h' : W ⟶ Y` with affine ambient schemes, and a commutative square `h ≫ g = f ≫ h'`, the
canonical morphism `tZ.ambient ⟶ tW.ambient` of
`Stacks.Thickenings.universalFirstOrderThickeningMap` carries the conormal module of `tW` into
the conormal module of `tZ`, linearly over `Γ(W, ⊤)` acting through `f`.

This is the affine, module-level avatar of the morphism of conormal sheaves
`f^*𝒞_{W/Y} → 𝒞_{Z/X}` asserted by [Stacks Project, Tag 04F7]; it is not that morphism, which
lives on all of `Z` and is `Stacks.Thickenings.universalConormalSheafPullbackMap`. -/
noncomputable def universalConormalMap (tZ : UniversalFirstOrderThickening h)
    (tW : UniversalFirstOrderThickening h') [IsAffine tZ.ambient] [IsAffine tW.ambient]
    (f : Z ⟶ W) (g : X ⟶ Y) (comm : h ≫ g = f ≫ h') :
    letI := Smooth.thickeningKerModule tW.isUniversal.isFirstOrderThickening
    letI := conormalModuleAlong tZ.isUniversal.isFirstOrderThickening f
    RingHom.ker tW.inclusion.appTop.hom →ₗ[Γ(W, (⊤ : W.Opens))]
      RingHom.ker tZ.inclusion.appTop.hom :=
  conormalMap tZ.isUniversal.isFirstOrderThickening tW.isUniversal.isFirstOrderThickening
    (universalFirstOrderThickeningMap_inclusion tZ tW f g comm)

/-- **The affine characterization of the induced map of conormal modules.** On underlying sections
the map of `Stacks.Thickenings.universalConormalMap` is the ring map of the canonical morphism
`tZ.ambient ⟶ tW.ambient` of universal first-order thickenings.

This is the characterizing property of [Stacks Project, Tag 01R4] for the square
`(Z ⊂ Z') → (W ⊂ W')`: a section of the defining ideal of `W` in `W'` goes to its image under
the ambient ring map. For a first-order thickening the defining ideal is already its own conormal
module, so there is no quotient by the square of the ideal. -/
theorem universalConormalMap_apply (tZ : UniversalFirstOrderThickening h)
    (tW : UniversalFirstOrderThickening h') [IsAffine tZ.ambient] [IsAffine tW.ambient]
    (f : Z ⟶ W) (g : X ⟶ Y) (comm : h ≫ g = f ≫ h')
    (x : RingHom.ker tW.inclusion.appTop.hom) :
    ((universalConormalMap tZ tW f g comm x : RingHom.ker tZ.inclusion.appTop.hom) :
        Γ(tZ.ambient, (⊤ : tZ.ambient.Opens)))
      = (universalFirstOrderThickeningMap tZ tW f g comm).appTop.hom
          (x : Γ(tW.ambient, (⊤ : tW.ambient.Opens))) :=
  rfl

/-- The induced map of conormal modules is functorial in the commutative square: a vertical
composite of squares induces the composite map, in the opposite order. -/
theorem universalConormalMap_comp_apply {V V' : Scheme.{u}} {h'' : V ⟶ V'}
    (tZ : UniversalFirstOrderThickening h) (tW : UniversalFirstOrderThickening h')
    (tV : UniversalFirstOrderThickening h'') [IsAffine tZ.ambient] [IsAffine tW.ambient]
    [IsAffine tV.ambient] (f : Z ⟶ W) (g : X ⟶ Y) (comm : h ≫ g = f ≫ h')
    (f' : W ⟶ V) (g' : Y ⟶ V') (comm' : h' ≫ g' = f' ≫ h'')
    (x : RingHom.ker tV.inclusion.appTop.hom) :
    ((universalConormalMap tZ tV (f ≫ f') (g ≫ g') (comm_comp comm comm') x :
          RingHom.ker tZ.inclusion.appTop.hom) : Γ(tZ.ambient, (⊤ : tZ.ambient.Opens)))
      = ((universalConormalMap tZ tW f g comm (universalConormalMap tW tV f' g' comm' x) :
          RingHom.ker tZ.inclusion.appTop.hom) : Γ(tZ.ambient, (⊤ : tZ.ambient.Opens))) := by
  rw [universalConormalMap_apply, universalConormalMap_apply, universalConormalMap_apply,
    appTop_comp_apply, universalFirstOrderThickeningMap_comp]

/-- **The conormal module does not depend on the choice of universal first-order thickening.** For
two universal first-order thickenings `t₁`, `t₂` of the same morphism `h : Z ⟶ X` with affine
ambient schemes, the map of conormal modules induced by the canonical isomorphism
`t₁.ambient ≅ t₂.ambient` is bijective.

Together with
`Stacks.Thickenings.UniversalFirstOrderThickening.existsUnique_canonicalMap` this is what makes
"the" conormal module of `h` of [Stacks Project, Tag 04F4] well defined. -/
theorem bijective_conormalMap_canonicalMap (t₁ t₂ : UniversalFirstOrderThickening h)
    [IsAffine t₁.ambient] [IsAffine t₂.ambient] :
    Function.Bijective (conormalMap t₁.isUniversal.isFirstOrderThickening
      t₂.isUniversal.isFirstOrderThickening
      (f := 𝟙 Z) (k := UniversalFirstOrderThickening.canonicalMap t₁ t₂)
      (by rw [UniversalFirstOrderThickening.canonicalMap_inclusion, Category.id_comp])) :=
  bijective_conormalMap _ _ _
    ((UniversalFirstOrderThickening.canonicalMap_inclusion t₂ t₁).trans
      (Category.id_comp _).symm)
    (UniversalFirstOrderThickening.canonicalMap_comp_canonicalMap t₂ t₁)
    (UniversalFirstOrderThickening.canonicalMap_comp_canonicalMap t₁ t₂)

end Stacks.Thickenings

end
