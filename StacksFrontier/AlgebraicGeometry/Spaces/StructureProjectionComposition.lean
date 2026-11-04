module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureProjectionChartSquare

/-!
# The composition law for the canonical morphism `𝒪_Y ⟶ f_*𝒪_X` of modules

For a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` contained in a big fppf site
`B`, `AlgebraicGeometry.Space.structureProjectionOfHom` is the canonical morphism
`𝒪_Y ⟶ f_*𝒪_X` of `𝒪_Y`-modules: the structure map `f♯` of [Stacks Project, Tag 03G8] with its
ring structure forgotten.  This file proves that it **composes**, in the only sense available —
the direct images along `f` and along `g` compose only up to the comparison
`AlgebraicGeometry.Space.modulePushforwardCompIso` of [Stacks Project, Tag 03LU] — and that it
is **invertible at an isomorphism** of algebraic spaces.

The composition law is proved by transposing along the adjunction of [Stacks Project, Tag 03D7].
The canonical morphism is the transpose of the comparison `f^*𝒪_Y ⟶ 𝒪_X` of
`AlgebraicGeometry.Space.structureModulePullbackMap`: both have the structure map
`f♯ : 𝒪_Y ⟶ f_*𝒪_X` as their underlying morphism of sheaves of sets, by
`AlgebraicGeometry.Space.moduleSheafFunctor_map_structureProjectionOfHom` and
`AlgebraicGeometry.Space.moduleSheafFunctor_map_homEquiv_structureModulePullbackMap`, and a
morphism of sheaves of modules is determined by that.  The composition law for the comparison of
inverse images is `AlgebraicGeometry.Space.structureModulePullbackMap_comp`, and
transposing a composite is `AlgebraicGeometry.Space.homEquiv_modulePullbackCompIso_inv_app_comp`
together with the two naturalities of an adjunction's `homEquiv`.

Invertibility at an isomorphism `e` is proved on underlying sheaves of sets, where
[Stacks Project, Tag 03G8] is already available both for a composite
(`AlgebraicGeometry.Space.structureSharpSet_comp`) and for an identity
(`AlgebraicGeometry.Space.structureSharpSet_id`): the composition law at `(e.inv, e.hom)` makes
`e.hom♯` the left factor of an invertible composite, and the composition law at `(e.hom, e.inv)`
makes `e.inv♯` a split monomorphism, hence makes the remaining factor — the direct image along
`e.hom` of `e.inv♯` followed by the comparison of direct images — a split monomorphism too.  A
split monomorphism that becomes invertible when a morphism is prefixed to it is an epimorphism,
hence invertible, and then so is the prefixed morphism `e.hom♯`.  The passage back to modules is
that the underlying-sheaf functor reflects isomorphisms.

## Main results

* `AlgebraicGeometry.Space.moduleSheafFunctor_map_structureProjectionOfHom`: the canonical
  morphism `𝒪_Y ⟶ f_*𝒪_X` of modules is, on underlying sheaves of sets, the structure map
  `f♯` of [Stacks Project, Tag 03G8].
* `AlgebraicGeometry.Space.structureProjectionOfHom_eq_homEquiv_structureModulePullbackMap`: it
  is the transpose along the adjunction of [Stacks Project, Tag 03D7] of the canonical
  comparison `f^*𝒪_Y ⟶ 𝒪_X`.
* `AlgebraicGeometry.Space.structureProjectionOfHom_comp`: **the composition law.**  For
  `f : X ⟶ Y` and `g : Y ⟶ Z` the canonical morphism of the composite is the canonical morphism
  of `g`, followed by the direct image along `g` of the canonical morphism of `f`, followed by
  the composition comparison of direct images of [Stacks Project, Tag 03LU].
* `AlgebraicGeometry.Space.isIso_structureSharpSet`: the structure map of an isomorphism of
  algebraic spaces is invertible on underlying sheaves of sets.
* `AlgebraicGeometry.Space.isIso_structureProjectionOfHom`: **the canonical morphism
  `𝒪_Y ⟶ e_*𝒪_X` of an isomorphism `e` of algebraic spaces is invertible.**

## Implementation notes

Every step of the composition law is taken in the category of `𝒪`-modules.  The route through
underlying sheaves of sets — rewriting the composite under
`CategoryTheory.Sheaf.moduleSheafFunctor` and appealing to
`AlgebraicGeometry.Space.structureSharpSet_comp` — does not survive the kernel:
the underlying sheaf of a direct image of modules and the direct image of the underlying sheaf
are two spellings of one sheaf of sets, and a congruence that substitutes all three factors of
the composite at once has to reconcile them inside the implicit object arguments of `≫`.  The
natural spellings of that reconciliation — `congrArg₂` on the composite, three- and
four-factor `CategoryTheory.whisker_eq`/`CategoryTheory.eq_whisker` chains in both orders of
substitution, the chain split one factor per declaration, and a congruence lemma stated at
variable objects — each either exhaust the kernel's budget or move the cost to the next
declaration.  The transpose route below has no such reconciliation in it and costs under a
second.

For the same reason no statement here writes `.val.app` of a *composite* of morphisms of
modules: elaborating that forces the coercion of a composite's sections, which is exactly the
reconciliation above.  The sections of the individual factors are affordable, and the
composition law is never read on sections.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS}

/-! ### The canonical morphism of modules on underlying sheaves of sets -/

/-- **The canonical morphism `𝒪_Y ⟶ f_*𝒪_X` of modules is the structure map `f♯` of
[Stacks Project, Tag 03G8]** on underlying sheaves of sets.

`AlgebraicGeometry.Space.structureProjectionOfHom` is built from the structure map by forgetting
its ring structure, so this is a definitional identity once the underlying sheaf of the direct
image of modules is read as the direct image of the underlying sheaf; the type ascription is
what performs that reading. -/
theorem moduleSheafFunctor_map_structureProjectionOfHom (f : X ⟶ Y) :
    (show structureSetSheaf B S hS Y ⟶
        (smallEtaleDirectImage B S hS f).obj (structureSetSheaf B S hS X) from
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
        (structureProjectionOfHom B S hS f)) =
      structureSharpSet B S hS f :=
  rfl

/-- **The canonical morphism `𝒪_Y ⟶ f_*𝒪_X` of modules is the transpose of the canonical
comparison `f^*𝒪_Y ⟶ 𝒪_X`** along the adjunction of [Stacks Project, Tag 03D7].

Both morphisms have the structure map `f♯` of [Stacks Project, Tag 03G8] as their underlying
morphism of sheaves of sets — the first by
`AlgebraicGeometry.Space.moduleSheafFunctor_map_structureProjectionOfHom`, the second by
`AlgebraicGeometry.Space.moduleSheafFunctor_map_homEquiv_structureModulePullbackMap` — and a
morphism of sheaves of modules is determined by that. -/
theorem structureProjectionOfHom_eq_homEquiv_structureModulePullbackMap (f : X ⟶ Y) :
    structureProjectionOfHom B S hS f =
      (modulePullbackAdjunction B S hS f).homEquiv _ _
        (structureModulePullbackMap B S hS f) :=
  Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor
    (R := structureRingSheaf B S hS Y)
    ((moduleSheafFunctor_map_structureProjectionOfHom B S hS f).trans
      (moduleSheafFunctor_map_homEquiv_structureModulePullbackMap B S hS f).symm)

/-! ### The composition law -/

/-- **[Stacks Project, Tag 03G8], compatibility with composition, at the level of modules.**  For
`f : X ⟶ Y` and `g : Y ⟶ Z` the canonical morphism `𝒪_Z ⟶ (f ≫ g)_*𝒪_X` of `𝒪_Z`-modules is the
canonical morphism `𝒪_Z ⟶ g_*𝒪_Y` of `g`, followed by the direct image along `g` of the
canonical morphism `𝒪_Y ⟶ f_*𝒪_X` of `f`, followed by the composition comparison
`g_*(f_*𝒪_X) ⟶ (f ≫ g)_*𝒪_X` of direct images of [Stacks Project, Tag 03LU].

The proof is the transposed one: by
`AlgebraicGeometry.Space.structureProjectionOfHom_eq_homEquiv_structureModulePullbackMap` each
of the three canonical morphisms is a transpose along the adjunction of
[Stacks Project, Tag 03D7], the composition law for the comparison of inverse images is
`AlgebraicGeometry.Space.structureModulePullbackMap_comp`, and transposing the resulting
composite is `AlgebraicGeometry.Space.homEquiv_modulePullbackCompIso_inv_app_comp` followed by
the two naturalities of `CategoryTheory.Adjunction.homEquiv`. -/
@[stacks 03G8 "compatibility with composition at the level of modules"]
theorem structureProjectionOfHom_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    structureProjectionOfHom B S hS (f ≫ g) =
      structureProjectionOfHom B S hS g ≫
        (modulePushforward B S hS g).map (structureProjectionOfHom B S hS f) ≫
        (modulePushforwardCompIso B S hS f g).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS X)) := by
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine Eq.trans
    (structureProjectionOfHom_eq_homEquiv_structureModulePullbackMap B S hS (f ≫ g)) ?_
  refine Eq.trans (congrArg ((modulePullbackAdjunction B S hS (f ≫ g)).homEquiv _ _)
    (structureModulePullbackMap_comp B S hS f g)) ?_
  refine Eq.trans (homEquiv_modulePullbackCompIso_inv_app_comp B S hS f g _ _ _) ?_
  refine eq_whisker ?_ _
  refine Eq.trans (congrArg ((modulePullbackAdjunction B S hS g).homEquiv _ _)
    ((modulePullbackAdjunction B S hS f).homEquiv_naturality_left
      (structureModulePullbackMap B S hS g) (structureModulePullbackMap B S hS f))) ?_
  refine Eq.trans ((modulePullbackAdjunction B S hS g).homEquiv_naturality_right
    (structureModulePullbackMap B S hS g)
    ((modulePullbackAdjunction B S hS f).homEquiv _ _
      (structureModulePullbackMap B S hS f))) ?_
  refine Eq.trans (eq_whisker
    (structureProjectionOfHom_eq_homEquiv_structureModulePullbackMap B S hS g).symm _) ?_
  exact whisker_eq _ (congrArg (modulePushforward B S hS g).map
    (structureProjectionOfHom_eq_homEquiv_structureModulePullbackMap B S hS f).symm)

/-! ### Invertibility at an isomorphism -/

/-- A morphism with an invertible composite on its right is a split monomorphism. -/
private theorem isSplitMono_of_isIso_comp {D : Type*} [Category D] {A A' A'' : D} (m : A ⟶ A')
    (n : A' ⟶ A'') [IsIso (m ≫ n)] : IsSplitMono m :=
  IsSplitMono.mk' ⟨n ≫ inv (m ≫ n), by rw [← Category.assoc, IsIso.hom_inv_id]⟩

/-- A morphism whose composite with a split monomorphism is invertible is itself invertible: the
split monomorphism is an epimorphism, being the right factor of an epimorphism, hence
invertible. -/
private theorem isIso_of_isIso_comp_of_isSplitMono {D : Type*} [Category D] {A A' A'' : D}
    (m : A ⟶ A') (n : A' ⟶ A'') [IsIso (m ≫ n)] [IsSplitMono n] : IsIso m :=
  let : Epi n := epi_of_epi m n
  let : IsIso n := isIso_of_epi_of_isSplitMono n
  IsIso.of_isIso_comp_right m n

/-- `AlgebraicGeometry.Space.isIso_of_isIso_comp_of_isSplitMono` for a threefold composite whose
last factor is invertible: there the middle factor need only be a split monomorphism.  The
assembly of the two into a split monomorphism is taken here, at variable objects, because the
instance `CategoryTheory.IsSplitMono.comp` is not found at the concrete morphisms of sheaves on
the small étale site. -/
private theorem isIso_of_isIso_comp3_of_isSplitMono {D : Type*} [Category D]
    {A A' A'' A''' : D} (m : A ⟶ A') (n : A' ⟶ A'') (p : A'' ⟶ A''')
    (hmnp : IsIso (m ≫ n ≫ p)) (hn : IsSplitMono n) (hp : IsIso p) : IsIso m :=
  let := hmnp
  let := hn
  let := hp
  let : IsSplitMono (n ≫ p) := inferInstance
  isIso_of_isIso_comp_of_isSplitMono m (n ≫ p)

/-- **The structure map of an identity is invertible on underlying sheaves of sets.**  It is the
canonical identification of `𝒪_X` with `(𝟙 X)_*𝒪_X`, by
`AlgebraicGeometry.Space.structureSharpSet_id`. -/
private theorem isIso_structureSharpSet_id (W : AlgebraicSpaces B S hS) :
    IsIso (structureSharpSet B S hS (𝟙 W)) := by
  rw [structureSharpSet_id B S hS W]
  exact ((smallEtaleDirectImageIdIso B S hS W).app (structureSetSheaf B S hS W)).isIso_inv

/-- The composition law of [Stacks Project, Tag 03G8] on underlying sheaves of sets, read at
`(e.inv, e.hom)` for an isomorphism `e` of algebraic spaces: the composite it computes is the
structure map of an identity, hence invertible. -/
private theorem isIso_structureSharpSet_comp_inv_hom (e : X ≅ Y) :
    IsIso (structureSharpSet B S hS e.hom ≫
      (smallEtaleDirectImage B S hS e.hom).map (structureSharpSet B S hS e.inv) ≫
      (smallToposMorphismTypeU_comp B S hS e.inv e.hom).hom.app
        (structureSetSheaf B S hS Y)) := by
  rw [structureSharpSet_comp B S hS e.inv e.hom, e.inv_hom_id]
  exact isIso_structureSharpSet_id B S hS Y

/-- The structure map of the inverse of an isomorphism of algebraic spaces is a split
monomorphism on underlying sheaves of sets: the composition law of [Stacks Project, Tag 03G8] at
`(e.hom, e.inv)` exhibits an invertible composite with it as the left factor. -/
private theorem isSplitMono_structureSharpSet_inv (e : X ≅ Y) :
    IsSplitMono (structureSharpSet B S hS e.inv) :=
  let : IsIso (structureSharpSet B S hS e.inv ≫
      (smallEtaleDirectImage B S hS e.inv).map (structureSharpSet B S hS e.hom) ≫
      (smallToposMorphismTypeU_comp B S hS e.hom e.inv).hom.app
        (structureSetSheaf B S hS X)) :=
    isIso_structureSharpSet_comp_inv_hom B S hS e.symm
  isSplitMono_of_isIso_comp (structureSharpSet B S hS e.inv)
    ((smallEtaleDirectImage B S hS e.inv).map (structureSharpSet B S hS e.hom) ≫
      (smallToposMorphismTypeU_comp B S hS e.hom e.inv).hom.app
        (structureSetSheaf B S hS X))

/-- **The structure map `e♯ : 𝒪_Y ⟶ e_*𝒪_X` of an isomorphism of algebraic spaces is invertible
on underlying sheaves of sets.**

The composition law of [Stacks Project, Tag 03G8] at `(e.inv, e.hom)` makes `e.hom♯` a factor of
an invertible morphism, and the same law at `(e.hom, e.inv)`, pushed forward along `e.hom`,
makes the other factor a split monomorphism; a morphism whose composite with a split
monomorphism is invertible is invertible. -/
theorem isIso_structureSharpSet (e : X ≅ Y) : IsIso (structureSharpSet B S hS e.hom) :=
  let : IsSplitMono (structureSharpSet B S hS e.inv) :=
    isSplitMono_structureSharpSet_inv B S hS e
  isIso_of_isIso_comp3_of_isSplitMono (structureSharpSet B S hS e.hom)
    ((smallEtaleDirectImage B S hS e.hom).map (structureSharpSet B S hS e.inv))
    ((smallToposMorphismTypeU_comp B S hS e.inv e.hom).hom.app
      (structureSetSheaf B S hS Y))
    (isIso_structureSharpSet_comp_inv_hom B S hS e) inferInstance
    ((smallToposMorphismTypeU_comp B S hS e.inv e.hom).app
      (structureSetSheaf B S hS Y)).isIso_hom

/-- **The canonical morphism `𝒪_Y ⟶ e_*𝒪_X` of modules of an isomorphism `e` of algebraic spaces
is invertible.**

Its underlying morphism of sheaves of sets is the structure map `e.hom♯`
(`AlgebraicGeometry.Space.moduleSheafFunctor_map_structureProjectionOfHom`), which is invertible
by `AlgebraicGeometry.Space.isIso_structureSharpSet`, and the underlying-sheaf functor reflects
isomorphisms. -/
@[stacks 03G8 "the canonical morphism of modules of an isomorphism is an isomorphism"]
theorem isIso_structureProjectionOfHom (e : X ≅ Y) :
    IsIso (structureProjectionOfHom B S hS e.hom) :=
  let : IsIso ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
      (structureProjectionOfHom B S hS e.hom)) :=
    isIso_structureSharpSet B S hS e
  isIso_of_reflects_iso (structureProjectionOfHom B S hS e.hom)
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y))

end AlgebraicGeometry.Space

end
