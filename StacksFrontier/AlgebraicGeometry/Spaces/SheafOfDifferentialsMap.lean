module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivationsIntoDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsComp

/-!
# The comparison map of sheaves of differentials of a commutative square

Let

```
X' --f--> X
|         |
p'        p
v         v
Y' --q--> Y
```

be a commutative square of algebraic spaces over a scheme `S`.  Stacks 04CX attaches to it a
canonical morphism `c_f : f^*Ω_{X/Y} ⟶ Ω_{X'/Y'}` of `𝒪_{X'}`-modules, characterized by the
requirement that its adjoint transpose carry the universal differential `d_{X/Y}(t)` of a local
section `t` of `𝒪_X` to `d_{X'/Y'}(f♯ t)`.  This file constructs it.

The construction is the one the source indicates.  The composite
`D := f_*d_{X'/Y'} ∘ f♯ : 𝒪_X ⟶ f_*Ω_{X'/Y'}` of the structure map of `f` with the direct image
of the universal `Y'`-derivation is a `Y`-derivation: additivity and the Leibniz rule hold
because `f♯` is a homomorphism of sheaves of rings and `d_{X'/Y'}` is a derivation, and `D`
annihilates the image of `p♯ : p^{-1}𝒪_Y ⟶ 𝒪_X` because the square commutes, so that `f♯ ∘ p♯`
factors through `(p')♯`.  By Equation 0619 a `Y`-derivation of `𝒪_X` with values in
`f_*Ω_{X'/Y'}` is the same thing as a morphism `f^*Ω_{X/Y} ⟶ Ω_{X'/Y'}` of `𝒪_{X'}`-modules, and
`c_f` is the morphism corresponding to `D`.

## Main definitions

* `AlgebraicGeometry.Space.pushforwardUniversalDerivation` is the `Y`-derivation
  `f_*d_{X'/Y'} ∘ f♯ : 𝒪_X ⟶ f_*Ω_{X'/Y'}` of a commutative square.
* `AlgebraicGeometry.Space.sheafOfDifferentialsMap` is the comparison map
  `c_f : f^*Ω_{X/Y} ⟶ Ω_{X'/Y'}` of **Stacks 04CX**, the derivation above read through
  Equation 0619.

## Main results

* `AlgebraicGeometry.Space.pushforwardUniversalDerivation_d`: the derivation really is the
  composite of the structure map with the direct image of the universal derivation, on local
  sections.
* `AlgebraicGeometry.Space.isSheafOfDifferentialsMap_sheafOfDifferentialsMap`: **Stacks 04CX**,
  the comparison map has the characterizing property
  `AlgebraicGeometry.Space.IsSheafOfDifferentialsMap`.  Together with
  `AlgebraicGeometry.Space.eq_of_isSheafOfDifferentialsMap` this identifies it with any morphism
  satisfying that property, so a statement quantifying over such a morphism applies to it.

## Implementation notes

Sections over an étale chart `U` of `X` of a direct image `f_*F` are the value at `U` of a
composite of three functors, none of which evaluates sections of `F` at a single object, so the
additive and multiplicative structures on them are not those of a module of sections of `F`:
they are the structures transported along the direct image through its product comparison,
`CategoryTheory.Sheaf.ringAddObj`, `CategoryTheory.Sheaf.moduleAddObj` and
`CategoryTheory.Sheaf.moduleSMulObj`.  So the Leibniz rule for `f_*d_{X'/Y'}` is not a
sectionwise computation: it is obtained by first recording additivity and the Leibniz rule for
`d_{X'/Y'}` as identities of morphisms out of `𝒪_{X'} ⨯ 𝒪_{X'}`
(`AlgebraicGeometry.Space.ringAddHom_comp_derivationHom` and `.ringMulHom_comp_derivationHom`)
and then transporting those identities along a finite-product-preserving functor to types.

The vanishing of the derivation on the base is not a sectionwise computation either: the
sections of `p^{-1}𝒪_Y` are not described by a formula.  It is proved in the direct-image form
of the structure map, where Stacks 03G8's compatibility with composition is available, and
carried back along the adjunction `p^{-1} ⊣ p_*` for sheaves of sets, under which the two forms
of the structure map are adjunct
(`AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget_homEquiv`).  Both directions of that
transport are used: `AlgebraicGeometry.Space.structureSharpSetComp_of_structureSharpInverseImage`
turns the vanishing clause of `d_{X'/Y'}` into a direct-image identity, and
`AlgebraicGeometry.Space.structureSharpInverseImage_of_structureSharpSetComp` turns the
direct-image identity for the outer square back into the vanishing clause for `D`.

## References

* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX)
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619)
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf CategoryTheory.Functor

namespace AlgebraicGeometry.Space

universe t₀ w₀ v₀ u₀ u

universe w₁ v₁ u₁

/-! Instance search for binary products and the terminal object of sheaves of sets tries the
default-priority `HasLimit` instances before the low-priority one through `HasLimitsOfShape`,
and under the current imports those time out; the shortcut instances below go there directly. -/

local instance (priority := high) hasLimit_pair_sheafType {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} (X Y : Sheaf J (Type w₁)) : HasLimit (pair X Y) :=
  HasLimitsOfShape.has_limit _

local instance (priority := high) hasLimit_empty_sheafType {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} : HasLimit (Functor.empty.{0} (Sheaf J (Type w₁))) :=
  HasLimitsOfShape.has_limit _

/-! ### Derivations of sheaves of rings as morphisms out of a product -/

section Transport

variable {C : Type u₀} [Category.{v₀} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget RingCat.{w₀})] [J.HasSheafCompose (forget AddCommGrpCat.{w₀})]
    {R : Sheaf J RingCat.{w₀}} {G : SheafOfModules.{w₀} R}

/-- The zero morphism from the sheaf of sets underlying a sheaf of rings to the sheaf of sets
underlying a sheaf of modules over it. -/
noncomputable def zeroDerivationHom (R : Sheaf J RingCat.{w₀}) (G : SheafOfModules.{w₀} R) :
    ringSheaf R ⟶ moduleSheaf R G :=
  terminal.from (ringSheaf R) ≫ moduleZeroHom R G

/-- **Additivity of a derivation as an identity of morphisms out of a product.**  A morphism of
the underlying sheaves of sets which is additive on sections commutes with the addition
morphisms. -/
theorem ringAddHom_comp_derivationHom (δ : ringSheaf R ⟶ moduleSheaf R G)
    (hadd : ∀ (U : Cᵒᵖ) (a b : (sectionsFunctor J U).obj (ringSheaf R)),
      (sectionsFunctor J U).map δ (a + b) =
        (sectionsFunctor J U).map δ a + (sectionsFunctor J U).map δ b) :
    ringAddHom R ≫ δ = prod.map δ δ ≫ moduleAddHom R G := by
  refine hom_ext_sections (fun U s ↦ ?_)
  rw [(sectionsFunctor J U).map_comp_apply, (sectionsFunctor J U).map_comp_apply,
    ← prodObjMk_map_fst_map_snd (P := sectionsFunctor J U) s, sectionsFunctor_map_ringAddHom,
    map_prodMap_apply, map_fst_prodObjMk, map_snd_prodObjMk, sectionsFunctor_map_moduleAddHom]
  exact hadd U _ _

/-- **The Leibniz rule as an identity of morphisms out of a product.**  A morphism of the
underlying sheaves of sets which satisfies the Leibniz rule on sections factors the
multiplication morphism through the two scalar multiplications and the addition. -/
theorem ringMulHom_comp_derivationHom (δ : ringSheaf R ⟶ moduleSheaf R G)
    (hmul : ∀ (U : Cᵒᵖ) (a b : (sectionsFunctor J U).obj (ringSheaf R)),
      (sectionsFunctor J U).map δ (a * b) =
        a • (sectionsFunctor J U).map δ b + b • (sectionsFunctor J U).map δ a) :
    ringMulHom R ≫ δ =
      prod.lift (prod.lift prod.fst (prod.snd ≫ δ) ≫ moduleSMulHom R G)
          (prod.lift prod.snd (prod.fst ≫ δ) ≫ moduleSMulHom R G) ≫ moduleAddHom R G := by
  refine hom_ext_sections (fun U s ↦ ?_)
  rw [(sectionsFunctor J U).map_comp_apply, (sectionsFunctor J U).map_comp_apply,
    ← prodObjMk_map_fst_map_snd (P := sectionsFunctor J U) s, sectionsFunctor_map_ringMulHom,
    map_lift_apply, sectionsFunctor_map_moduleAddHom,
    (sectionsFunctor J U).map_comp_apply, (sectionsFunctor J U).map_comp_apply,
    map_lift_apply, map_lift_apply, (sectionsFunctor J U).map_comp_apply,
    (sectionsFunctor J U).map_comp_apply, map_fst_prodObjMk, map_snd_prodObjMk,
    sectionsFunctor_map_moduleSMulHom, sectionsFunctor_map_moduleSMulHom]
  exact hmul U _ _

variable (R G) in
/-- Additivity of a derivation transports along a finite-product-preserving functor to types. -/
theorem map_ringAddObj_derivationHom (P : Sheaf J (Type w₀) ⥤ Type t₀)
    [PreservesFiniteProducts P] (δ : ringSheaf R ⟶ moduleSheaf R G)
    (hδ : ringAddHom R ≫ δ = prod.map δ δ ≫ moduleAddHom R G)
    (x y : P.obj (ringSheaf R)) :
    P.map δ (ringAddObj R P x y) = moduleAddObj R G P (P.map δ x) (P.map δ y) := by
  rw [ringAddObj, ← P.map_comp_apply, hδ, P.map_comp_apply, map_prodMap_apply,
    map_fst_prodObjMk, map_snd_prodObjMk, moduleAddObj]

variable (R G) in
/-- The Leibniz rule transports along a finite-product-preserving functor to types. -/
theorem map_ringMulObj_derivationHom (P : Sheaf J (Type w₀) ⥤ Type t₀)
    [PreservesFiniteProducts P] (δ : ringSheaf R ⟶ moduleSheaf R G)
    (hδ : ringMulHom R ≫ δ =
      prod.lift (prod.lift prod.fst (prod.snd ≫ δ) ≫ moduleSMulHom R G)
          (prod.lift prod.snd (prod.fst ≫ δ) ≫ moduleSMulHom R G) ≫ moduleAddHom R G)
    (x y : P.obj (ringSheaf R)) :
    P.map δ (ringMulObj R P x y) =
      moduleAddObj R G P (moduleSMulObj R G P x (P.map δ y))
        (moduleSMulObj R G P y (P.map δ x)) := by
  rw [ringMulObj, ← P.map_comp_apply, hδ, P.map_comp_apply, map_lift_apply,
    P.map_comp_apply, P.map_comp_apply, map_lift_apply, map_lift_apply,
    P.map_comp_apply, P.map_comp_apply, map_fst_prodObjMk, map_snd_prodObjMk,
    moduleAddObj, moduleSMulObj, moduleSMulObj]

variable (R G) in
/-- The zero morphism transports to the zero section along a finite-product-preserving functor
to types. -/
theorem map_zeroDerivationHom (P : Sheaf J (Type w₀) ⥤ Type t₀) [PreservesFiniteProducts P]
    (x : P.obj (ringSheaf R)) :
    P.map (zeroDerivationHom R G) x = moduleZeroObj R G P := by
  rw [zeroDerivationHom, P.map_comp_apply, map_terminalFrom_apply, moduleZeroObj]

end Transport

/-! ### A piece of category algebra -/

section CategoryAlgebra

variable {C : Type u₀} [Category.{v₀} C]

/-- A morphism whose composite with an isomorphism is known is that composite followed by the
inverse isomorphism. -/
private theorem eq_comp_inv_of_comp_eq {A T₁ T₂ : C} (x : A ⟶ T₁) (c : T₁ ⟶ T₂) (cinv : T₂ ⟶ T₁)
    (hcc : c ≫ cinv = 𝟙 T₁) {d : A ⟶ T₂} (h : x ≫ c = d) : x = d ≫ cinv :=
  ((Category.comp_id x).symm.trans (congrArg (fun m ↦ x ≫ m) hcc.symm)).trans
    ((Category.assoc x c cinv).symm.trans (congrArg (fun m ↦ m ≫ cinv) h))

end CategoryAlgebra

/-! ### The two forms of the structure map -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section StructureMap

variable {Z W V : AlgebraicSpaces B S hS}

/-- The inverse-image form `r♯ : r^{-1}𝒪_W ⟶ 𝒪_Z` of the structure map of a morphism of
algebraic spaces, on underlying sheaves of sets. -/
noncomputable def structureSharpInverseImageSet (r : Z ⟶ W) :
    (smallEtaleRingedToposHom B S hS r).toToposHom.inverseImage.obj
        (structureSetSheaf B S hS W) ⟶ structureSetSheaf B S hS Z :=
  (smallEtaleRingedTopos B S hS Z).forgetRing.map (structureSharpInverseImage B S hS r)

/-- **Stacks 03G8.**  The two forms of the structure map are adjunct: the transpose of
`r♯ : r^{-1}𝒪_W ⟶ 𝒪_Z` under `r^{-1} ⊣ r_*` for sheaves of sets is `r♯ : 𝒪_W ⟶ r_*𝒪_Z`. -/
theorem homEquiv_structureSharpInverseImageSet (r : Z ⟶ W) :
    (smallEtaleRingedToposHom B S hS r).toToposHom.adj.homEquiv
        (structureSetSheaf B S hS W) (structureSetSheaf B S hS Z)
        (structureSharpInverseImageSet B S hS r) =
      structureSharpSet B S hS r :=
  (congrArg ((smallEtaleRingedToposHom B S hS r).toToposHom.adj.homEquiv
      (structureSetSheaf B S hS W) (structureSetSheaf B S hS Z))
    ((RingedToposHom.fSharpInverseImage_forget_homEquiv
        (smallEtaleRingedToposHom B S hS r)).trans
      (congrArg ((smallEtaleRingedToposHom B S hS r).toToposHom.adj.homEquiv
          (structureSetSheaf B S hS W) (structureSetSheaf B S hS Z)).symm
        (forgetRing_map_fSharp B S hS r)))).trans
    (Equiv.apply_symm_apply _ _)

/-- Two morphisms out of `𝒪_Z` agree after `r♯ : r^{-1}𝒪_W ⟶ 𝒪_Z` as soon as their direct
images agree after `r♯ : 𝒪_W ⟶ r_*𝒪_Z`. -/
theorem structureSharpInverseImage_of_structureSharpSetComp (r : Z ⟶ W)
    {E : Sheaf (SmallEtale.topology B S hS Z.1) (Type u)}
    (ε ε' : structureSetSheaf B S hS Z ⟶ E)
    (h : structureSharpSet B S hS r ≫ (smallEtaleDirectImage B S hS r).map ε =
      structureSharpSet B S hS r ≫ (smallEtaleDirectImage B S hS r).map ε') :
    structureSharpInverseImageSet B S hS r ≫ ε =
      structureSharpInverseImageSet B S hS r ≫ ε' := by
  refine ((smallEtaleRingedToposHom B S hS r).toToposHom.adj.homEquiv
    (structureSetSheaf B S hS W) E).injective ?_
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right,
    homEquiv_structureSharpInverseImageSet]
  exact h

/-- The direct images of two morphisms out of `𝒪_Z` agree after `r♯ : 𝒪_W ⟶ r_*𝒪_Z` as soon as
the morphisms agree after `r♯ : r^{-1}𝒪_W ⟶ 𝒪_Z`. -/
theorem structureSharpSetComp_of_structureSharpInverseImage (r : Z ⟶ W)
    {E : Sheaf (SmallEtale.topology B S hS Z.1) (Type u)}
    (ε ε' : structureSetSheaf B S hS Z ⟶ E)
    (h : structureSharpInverseImageSet B S hS r ≫ ε =
      structureSharpInverseImageSet B S hS r ≫ ε') :
    structureSharpSet B S hS r ≫ (smallEtaleDirectImage B S hS r).map ε =
      structureSharpSet B S hS r ≫ (smallEtaleDirectImage B S hS r).map ε' := by
  have key : ∀ ψ : structureSetSheaf B S hS Z ⟶ E,
      (smallEtaleRingedToposHom B S hS r).toToposHom.adj.homEquiv
          (structureSetSheaf B S hS W) E (structureSharpInverseImageSet B S hS r ≫ ψ) =
        structureSharpSet B S hS r ≫ (smallEtaleDirectImage B S hS r).map ψ := by
    intro ψ
    rw [Adjunction.homEquiv_naturality_right, homEquiv_structureSharpInverseImageSet]
    rfl
  exact (key ε).symm.trans ((congrArg
    ((smallEtaleRingedToposHom B S hS r).toToposHom.adj.homEquiv
      (structureSetSheaf B S hS W) E) h).trans (key ε'))

/-- The structure map of `k` followed by the direct image of the structure map of `g` and of a
morphism out of `𝒪_Z` is the structure map of `g ≫ k` followed by its direct image of that
morphism, through the comparison of iterated direct images. -/
theorem structureSharpSet_comp_map (g : Z ⟶ W) (k : W ⟶ V)
    {E : Sheaf (SmallEtale.topology B S hS Z.1) (Type u)}
    (ε : structureSetSheaf B S hS Z ⟶ E) :
    structureSharpSet B S hS k ≫ (smallEtaleDirectImage B S hS k).map
        (structureSharpSet B S hS g ≫ (smallEtaleDirectImage B S hS g).map ε) =
      structureSharpSet B S hS (g ≫ k) ≫
        (smallEtaleDirectImage B S hS (g ≫ k)).map ε ≫
          (smallToposMorphismTypeU_comp B S hS g k).inv.app E := by
  have hc := eq_comp_inv_of_comp_eq
    (structureSharpSet B S hS k ≫
      (smallEtaleDirectImage B S hS k).map (structureSharpSet B S hS g))
    ((smallToposMorphismTypeU_comp B S hS g k).hom.app (structureSetSheaf B S hS Z))
    ((smallToposMorphismTypeU_comp B S hS g k).inv.app (structureSetSheaf B S hS Z))
    (Iso.hom_inv_id_app _ _)
    ((Category.assoc _ _ _).trans (structureSharpSet_comp B S hS g k))
  refine Eq.trans (congrArg (fun m ↦ structureSharpSet B S hS k ≫ m)
    ((smallEtaleDirectImage B S hS k).map_comp _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun m ↦ m ≫ (smallEtaleDirectImage B S hS k).map
      ((smallEtaleDirectImage B S hS g).map ε)) hc) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact congrArg (fun m ↦ structureSharpSet B S hS (g ≫ k) ≫ m)
    ((smallToposMorphismTypeU_comp B S hS g k).inv.naturality ε).symm

/-- Two morphisms out of `𝒪_Z` agree after the structure map of `g ≫ k` and its direct image
exactly when their direct images along `g` agree after the structure map of `k` and its direct
image. -/
private theorem structureSharpSet_comp_map_eq_iff (g : Z ⟶ W) (k : W ⟶ V)
    {E : Sheaf (SmallEtale.topology B S hS Z.1) (Type u)}
    (ε ε' : structureSetSheaf B S hS Z ⟶ E) :
    structureSharpSet B S hS k ≫ (smallEtaleDirectImage B S hS k).map
        (structureSharpSet B S hS g ≫ (smallEtaleDirectImage B S hS g).map ε) =
      structureSharpSet B S hS k ≫ (smallEtaleDirectImage B S hS k).map
        (structureSharpSet B S hS g ≫ (smallEtaleDirectImage B S hS g).map ε') ↔
    structureSharpSet B S hS (g ≫ k) ≫ (smallEtaleDirectImage B S hS (g ≫ k)).map ε =
      structureSharpSet B S hS (g ≫ k) ≫ (smallEtaleDirectImage B S hS (g ≫ k)).map ε' := by
  rw [structureSharpSet_comp_map, structureSharpSet_comp_map]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact (cancel_mono ((smallToposMorphismTypeU_comp B S hS g k).inv.app E)).mp h
  · exact congrArg (· ≫ (smallToposMorphismTypeU_comp B S hS g k).inv.app E) h

end StructureMap

/-! ### The pushed-forward universal derivation -/

variable {X Y X' Y' : AlgebraicSpaces B S hS}

/-- Sections over an étale chart `U` of `X` of the direct image along `f : X' ⟶ X`, as a functor
on sheaves of sets on the small étale site of `X'`. -/
noncomputable def smallEtaleDirectImageSections (f : X' ⟶ X) (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    Sheaf (SmallEtale.topology B S hS X'.1) (Type u) ⥤ Type u :=
  smallEtaleDirectImage B S hS f ⋙ sectionsFunctor (SmallEtale.topology B S hS X.1) U

/-- Taking sections over `U` of the direct image along `f` preserves finite products. -/
instance smallEtaleDirectImageSections_preservesFiniteProducts (f : X' ⟶ X)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    PreservesFiniteProducts (smallEtaleDirectImageSections B S hS f U) := by
  unfold smallEtaleDirectImageSections
  infer_instance

/-- Additivity of the universal derivation, as an identity of morphisms out of a product. -/
theorem ringAddHom_comp_universalDerivationHom (p' : X' ⟶ Y') :
    ringAddHom (structureRingSheaf B S hS X') ≫ universalDerivationHom B S hS p' =
      prod.map (universalDerivationHom B S hS p') (universalDerivationHom B S hS p') ≫
        moduleAddHom (structureRingSheaf B S hS X') (sheafOfDifferentials B S hS p') :=
  ringAddHom_comp_derivationHom (universalDerivationHom B S hS p')
    (fun V a b ↦ _root_.map_add ((universalDerivation B S hS p').d (X := V)) a b)

/-- The Leibniz rule for the universal derivation, as an identity of morphisms out of a
product. -/
theorem ringMulHom_comp_universalDerivationHom (p' : X' ⟶ Y') :
    ringMulHom (structureRingSheaf B S hS X') ≫ universalDerivationHom B S hS p' =
      prod.lift
          (prod.lift prod.fst (prod.snd ≫ universalDerivationHom B S hS p') ≫
            moduleSMulHom (structureRingSheaf B S hS X') (sheafOfDifferentials B S hS p'))
          (prod.lift prod.snd (prod.fst ≫ universalDerivationHom B S hS p') ≫
            moduleSMulHom (structureRingSheaf B S hS X') (sheafOfDifferentials B S hS p')) ≫
        moduleAddHom (structureRingSheaf B S hS X') (sheafOfDifferentials B S hS p') :=
  ringMulHom_comp_derivationHom (universalDerivationHom B S hS p')
    (fun V a b ↦ (universalDerivation B S hS p').d_mul (X := V) a b)

/-- The composite `f_*d_{X'/Y'} ∘ f♯` is additive on sections. -/
theorem pushforwardUniversalDerivationHom_add (f : X' ⟶ X) (p' : X' ⟶ Y')
    (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (a b : (sectionsFunctor (SmallEtale.topology B S hS X.1) U).obj
      (structureSetSheaf B S hS X)) :
    (sectionsFunctor (SmallEtale.topology B S hS X.1) U).map
        (pushforwardUniversalDerivationHom B S hS f p') (a + b) =
      moduleAddObj (structureRingSheaf B S hS X') (sheafOfDifferentials B S hS p')
        (smallEtaleDirectImageSections B S hS f U)
        ((sectionsFunctor (SmallEtale.topology B S hS X.1) U).map
          (pushforwardUniversalDerivationHom B S hS f p') a)
        ((sectionsFunctor (SmallEtale.topology B S hS X.1) U).map
          (pushforwardUniversalDerivationHom B S hS f p') b) :=
  (congrArg ((smallEtaleDirectImageSections B S hS f U).map (universalDerivationHom B S hS p'))
      (_root_.map_add ((structureSharp B S hS f).hom.app U).hom a b)).trans
    (map_ringAddObj_derivationHom (structureRingSheaf B S hS X')
      (sheafOfDifferentials B S hS p') (smallEtaleDirectImageSections B S hS f U)
      (universalDerivationHom B S hS p') (ringAddHom_comp_universalDerivationHom B S hS p') _ _)

/-- The composite `f_*d_{X'/Y'} ∘ f♯` satisfies the Leibniz rule on sections. -/
theorem pushforwardUniversalDerivationHom_mul (f : X' ⟶ X) (p' : X' ⟶ Y')
    (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (a b : (sectionsFunctor (SmallEtale.topology B S hS X.1) U).obj
      (structureSetSheaf B S hS X)) :
    (sectionsFunctor (SmallEtale.topology B S hS X.1) U).map
        (pushforwardUniversalDerivationHom B S hS f p') (a * b) =
      moduleAddObj (structureRingSheaf B S hS X') (sheafOfDifferentials B S hS p')
        (smallEtaleDirectImageSections B S hS f U)
        (moduleSMulObj (structureRingSheaf B S hS X') (sheafOfDifferentials B S hS p')
          (smallEtaleDirectImageSections B S hS f U)
          ((sectionsFunctor (SmallEtale.topology B S hS X.1) U).map
            (structureSharpSet B S hS f) a)
          ((sectionsFunctor (SmallEtale.topology B S hS X.1) U).map
            (pushforwardUniversalDerivationHom B S hS f p') b))
        (moduleSMulObj (structureRingSheaf B S hS X') (sheafOfDifferentials B S hS p')
          (smallEtaleDirectImageSections B S hS f U)
          ((sectionsFunctor (SmallEtale.topology B S hS X.1) U).map
            (structureSharpSet B S hS f) b)
          ((sectionsFunctor (SmallEtale.topology B S hS X.1) U).map
            (pushforwardUniversalDerivationHom B S hS f p') a)) :=
  (congrArg ((smallEtaleDirectImageSections B S hS f U).map (universalDerivationHom B S hS p'))
      (_root_.map_mul ((structureSharp B S hS f).hom.app U).hom a b)).trans
    (map_ringMulObj_derivationHom (structureRingSheaf B S hS X')
      (sheafOfDifferentials B S hS p') (smallEtaleDirectImageSections B S hS f U)
      (universalDerivationHom B S hS p') (ringMulHom_comp_universalDerivationHom B S hS p') _ _)

/-- The zero `Y`-derivation of `𝒪_X` with values in `f_*Ω_{X'/Y'}`, written as the structure map
of `f` followed by the direct image of the zero morphism, so that it has the same shape as
`AlgebraicGeometry.Space.pushforwardUniversalDerivationHom`. -/
noncomputable def pushforwardZeroDerivationHom (f : X' ⟶ X) (p' : X' ⟶ Y') :
    structureSetSheaf B S hS X ⟶
      moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X)
        ((modulePushforward B S hS f).obj (sheafOfDifferentials B S hS p')) :=
  structureSharpSet B S hS f ≫ (smallEtaleDirectImage B S hS f).map
    (zeroDerivationHom (structureRingSheaf B S hS X') (sheafOfDifferentials B S hS p'))

/-- The zero derivation vanishes on sections. -/
theorem pushforwardZeroDerivationHom_app (f : X' ⟶ X) (p' : X' ⟶ Y')
    (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (a : (sectionsFunctor (SmallEtale.topology B S hS X.1) U).obj
      (structureSetSheaf B S hS X)) :
    (sectionsFunctor (SmallEtale.topology B S hS X.1) U).map
        (pushforwardZeroDerivationHom B S hS f p') a =
      moduleZeroObj (structureRingSheaf B S hS X') (sheafOfDifferentials B S hS p')
        (smallEtaleDirectImageSections B S hS f U) :=
  map_zeroDerivationHom (structureRingSheaf B S hS X') (sheafOfDifferentials B S hS p')
    (smallEtaleDirectImageSections B S hS f U) _

/-- The universal derivation and the zero morphism agree after the inverse-image form of the
structure map of `p'`: this is the vanishing clause of `d_{X'/Y'}`. -/
theorem structureSharpInverseImageSet_comp_universalDerivationHom (p' : X' ⟶ Y') :
    structureSharpInverseImageSet B S hS p' ≫ universalDerivationHom B S hS p' =
      structureSharpInverseImageSet B S hS p' ≫
        zeroDerivationHom (structureRingSheaf B S hS X') (sheafOfDifferentials B S hS p') := by
  refine hom_ext_sections (fun V s ↦ ?_)
  rw [(sectionsFunctor (SmallEtale.topology B S hS X'.1) V).map_comp_apply,
    (sectionsFunctor (SmallEtale.topology B S hS X'.1) V).map_comp_apply]
  refine Eq.trans ((universalDerivation B S hS p').d_app _) ?_
  exact (map_zeroDerivationHom (structureRingSheaf B S hS X')
    (sheafOfDifferentials B S hS p')
    (sectionsFunctor (SmallEtale.topology B S hS X'.1) V) _).symm

/-- **The vanishing clause for the pushed-forward universal derivation, in direct-image form.**
If a morphism `r : X' ⟶ Y` factors through `p' : X' ⟶ Y'`, then the universal `Y'`-derivation
and the zero morphism agree after the structure map of `r`. -/
theorem structureSharpSet_comp_universalDerivationHom (p' : X' ⟶ Y') (q : Y' ⟶ Y)
    (r : X' ⟶ Y) (hr : r = p' ≫ q) :
    structureSharpSet B S hS r ≫
        (smallEtaleDirectImage B S hS r).map (universalDerivationHom B S hS p') =
      structureSharpSet B S hS r ≫ (smallEtaleDirectImage B S hS r).map
        (zeroDerivationHom (structureRingSheaf B S hS X')
          (sheafOfDifferentials B S hS p')) := by
  subst hr
  exact (structureSharpSet_comp_map_eq_iff B S hS p' q _ _).mp (congrArg
    (fun m ↦ structureSharpSet B S hS q ≫ (smallEtaleDirectImage B S hS q).map m)
    (structureSharpSetComp_of_structureSharpInverseImage B S hS p' _ _
      (structureSharpInverseImageSet_comp_universalDerivationHom B S hS p')))

/-- **The vanishing clause for the pushed-forward universal derivation, in direct-image form.**
For a commutative square, the composite `f_*d_{X'/Y'} ∘ f♯` and the zero morphism agree after
the structure map of `p : X ⟶ Y`. -/
theorem structureSharpSet_comp_pushforwardUniversalDerivationHom (f : X' ⟶ X) (p : X ⟶ Y)
    (p' : X' ⟶ Y') (q : Y' ⟶ Y) (hcomm : f ≫ p = p' ≫ q) :
    structureSharpSet B S hS p ≫ (smallEtaleDirectImage B S hS p).map
        (pushforwardUniversalDerivationHom B S hS f p') =
      structureSharpSet B S hS p ≫ (smallEtaleDirectImage B S hS p).map
        (pushforwardZeroDerivationHom B S hS f p') :=
  (structureSharpSet_comp_map_eq_iff B S hS f p _ _).mpr
    (structureSharpSet_comp_universalDerivationHom B S hS p' q (f ≫ p) hcomm)

/-- **The vanishing clause for the pushed-forward universal derivation.**  For a commutative
square, the composite `f_*d_{X'/Y'} ∘ f♯` and the zero morphism agree after the inverse-image
form of the structure map of `p : X ⟶ Y`. -/
theorem structureSharpInverseImageSet_comp_pushforwardUniversalDerivationHom (f : X' ⟶ X)
    (p : X ⟶ Y) (p' : X' ⟶ Y') (q : Y' ⟶ Y) (hcomm : f ≫ p = p' ≫ q) :
    structureSharpInverseImageSet B S hS p ≫ pushforwardUniversalDerivationHom B S hS f p' =
      structureSharpInverseImageSet B S hS p ≫ pushforwardZeroDerivationHom B S hS f p' :=
  structureSharpInverseImage_of_structureSharpSetComp B S hS p _ _
    (structureSharpSet_comp_pushforwardUniversalDerivationHom B S hS f p p' q hcomm)

/-- **The pushed-forward universal derivation vanishes on the base.**  For a commutative square,
the composite `f_*d_{X'/Y'} ∘ f♯` kills the image of `p♯ : p^{-1}𝒪_Y ⟶ 𝒪_X`. -/
theorem pushforwardUniversalDerivationHom_app_eq_zero (f : X' ⟶ X) (p : X ⟶ Y) (p' : X' ⟶ Y')
    (q : Y' ⟶ Y) (hcomm : f ≫ p = p' ≫ q) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (a : (sectionsFunctor (SmallEtale.topology B S hS X.1) U).obj
      ((smallEtaleRingedToposHom B S hS p).toToposHom.inverseImage.obj
        (structureSetSheaf B S hS Y))) :
    (sectionsFunctor (SmallEtale.topology B S hS X.1) U).map
        (structureSharpInverseImageSet B S hS p ≫
          pushforwardUniversalDerivationHom B S hS f p') a =
      moduleZeroObj (structureRingSheaf B S hS X') (sheafOfDifferentials B S hS p')
        (smallEtaleDirectImageSections B S hS f U) := by
  refine Eq.trans (congrArg
    (fun m ↦ (sectionsFunctor (SmallEtale.topology B S hS X.1) U).map m a)
    (structureSharpInverseImageSet_comp_pushforwardUniversalDerivationHom
      B S hS f p p' q hcomm)) ?_
  exact pushforwardZeroDerivationHom_app B S hS f p' U
    ((sectionsFunctor (SmallEtale.topology B S hS X.1) U).map
      (structureSharpInverseImageSet B S hS p) a)

/-- **Stacks 04CX.**  For a commutative square with top edge `f : X' ⟶ X`, the composite
`D = f_*d_{X'/Y'} ∘ f♯ : 𝒪_X ⟶ f_*Ω_{X'/Y'}` is a `Y`-derivation of `𝒪_X` with values in the
direct image of the sheaf of differentials of `p'`. -/
@[stacks 04CX "the composite `f_*d_{X'/Y'} ∘ f♯` is a `Y`-derivation"]
noncomputable def pushforwardUniversalDerivation (f : X' ⟶ X) (p : X ⟶ Y) (p' : X' ⟶ Y')
    (q : Y' ⟶ Y) (hcomm : f ≫ p = p' ≫ q) :
    PresheafOfModulesOfCommRing.Derivation'
      ((modulePushforward B S hS f).obj (sheafOfDifferentials B S hS p')).val
      (structureSharpInverseImage B S hS p).hom where
  d {U} := AddMonoidHom.mk'
    (fun t ↦ (pushforwardUniversalDerivationHom B S hS f p').hom.app U t)
    (pushforwardUniversalDerivationHom_add B S hS f p' U)
  d_mul {U} a b := pushforwardUniversalDerivationHom_mul B S hS f p' U a b
  d_map {_U _V} g x :=
    (natTrans_app_map_apply (sectionsRestrict (J := SmallEtale.topology B S hS X.1) g)
      (pushforwardUniversalDerivationHom B S hS f p') x).symm
  d_app {U} a :=
    pushforwardUniversalDerivationHom_app_eq_zero B S hS f p p' q hcomm U a

/-- The `Y`-derivation of Stacks 04CX is the structure map of `f` followed by the direct image of
the universal `Y'`-derivation, on local sections. -/
theorem pushforwardUniversalDerivation_d (f : X' ⟶ X) (p : X ⟶ Y) (p' : X' ⟶ Y')
    (q : Y' ⟶ Y) (hcomm : f ≫ p = p' ≫ q) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (t : (structureRingSheaf B S hS X).obj.obj U) :
    (pushforwardUniversalDerivation B S hS f p p' q hcomm).d t =
      (pushforwardUniversalDerivationHom B S hS f p').hom.app U t :=
  rfl

/-! ### The comparison map -/

/-- **Stacks 04CX.**  The comparison map `c_f : f^*Ω_{X/Y} ⟶ Ω_{X'/Y'}` of a commutative square
of algebraic spaces: the `Y`-derivation `f_*d_{X'/Y'} ∘ f♯` read through Equation 0619. -/
@[stacks 04CX "the existence of the canonical map"]
noncomputable def sheafOfDifferentialsMap (f : X' ⟶ X) (p : X ⟶ Y) (p' : X' ⟶ Y') (q : Y' ⟶ Y)
    (hcomm : f ≫ p = p' ≫ q) :
    (modulePullback B S hS f).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p' :=
  (derivationDirectImageEquiv B S hS f p (sheafOfDifferentials B S hS p')).symm
    (pushforwardUniversalDerivation B S hS f p p' q hcomm)

/-- **Stacks 04CX.**  The comparison map has the characterizing property of Stacks 04CX: its
adjoint transpose carries the universal differential `d_{X/Y}(t)` of a local section `t` of
`𝒪_X` to `d_{X'/Y'}(f♯ t)`.

With `AlgebraicGeometry.Space.eq_of_isSheafOfDifferentialsMap` this identifies
`AlgebraicGeometry.Space.sheafOfDifferentialsMap` with any morphism having that property. -/
@[stacks 04CX "the canonical map has the characterizing property"]
theorem isSheafOfDifferentialsMap_sheafOfDifferentialsMap (f : X' ⟶ X) (p : X ⟶ Y)
    (p' : X' ⟶ Y') (q : Y' ⟶ Y) (hcomm : f ≫ p = p' ≫ q) :
    IsSheafOfDifferentialsMap B S hS f p p'
      (sheafOfDifferentialsMap B S hS f p p' q hcomm) := fun _U t ↦
  PresheafOfModulesOfCommRing.Derivation.congr_d
    ((derivationDirectImageEquiv B S hS f p (sheafOfDifferentials B S hS p')).apply_symm_apply
      (pushforwardUniversalDerivation B S hS f p p' q hcomm))
    t

end AlgebraicGeometry.Space

end
