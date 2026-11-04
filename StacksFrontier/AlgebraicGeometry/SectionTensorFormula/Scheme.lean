module

public import StacksFrontier.AlgebraicGeometry.SectionTensorFormula.Basic

/-!
# The monoidal product of `X.Modules` on sections

For a scheme `X`, two sheaves of modules `F G : X.Modules` and an open `U : X.Opens`, this file
supplies the map

  `Γ(F, U) ⊗_{Γ(X, U)} Γ(G, U) ⟶ Γ(F ⊗ G, U)`

for the monoidal product of `X.Modules`
(`Stacks.SheafInternalHom.schemeMonoidalCategory`), together with its formula on a pure tensor
and its compatibility with restriction and with germs. The sibling `Basic.lean` does the work at
the level of an arbitrary ringed site; everything here is that, read in the `Γ` notation of
`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean`.

Before this file the monoidal product of `X.Modules` could not be evaluated on sections at all.
It is built by localizing the sectionwise product of presheaves of modules, and a localized
tensor product is a lift through a universal property, not a formula; three separate docstrings
in this repository record statements they could not make for that reason. The underlying
identification is `Stacks.SectionTensorFormula.tensorSheafIsoTensorObj`.

## Main definitions

* `Stacks.SectionTensorFormula.tensorSectionLinear`: **the comparison**, a `Γ(X, U)`-linear map
  `Γ(F, U) ⊗ Γ(G, U) →ₗ Γ(F ⊗ G, U)`.
* `Stacks.SectionTensorFormula.tensorSection`: the image of a pure tensor, i.e. **the product of
  two sections**, written `m ⊗ₛ n` in the scoped notation.

## Main results

* `tensorSection_add_left`, `tensorSection_add_right`, `tensorSection_smul_left`,
  `tensorSection_smul_right`, `tensorSection_zero_left`, `tensorSection_zero_right`: the product
  of sections is `Γ(X, U)`-bilinear.
* `map_tensorSection`: **restriction compatibility.** The product of two sections restricts to the
  product of their restrictions.
* `germ_tensorSection`: **germ compatibility.** The germ of a product of sections is unchanged by
  first restricting both factors to a smaller open containing the point.

## Implementation notes

**The comparison is a bare `LinearMap`, with no transport.** `Γ(F, U)` is by definition
`F.val.obj (op U)` and `Γ(X, U)` is `X.presheaf.obj (op U)`, and the module structure Mathlib
installs by `AlgebraicGeometry.Scheme.Modules.instModule` is the one the sectionwise tensor
product of presheaves of modules uses. So `tensorSectionLinear` is literally
`((toTensorSection ...).app (op U)).hom`: the `ModuleCat` morphism of the sibling file read as a
linear map. Linearity is therefore not proved here, it is inherited, and `TensorProduct.lift` is
never invoked.

**Why the general file is not stated elementwise.** At the general ringed-site level the scalar
ring has two spellings — `𝒪.obj U` carries the `CommRing` instance that `⊗ₜ` needs, while the
module structure on sections is keyed on `(structureSheaf 𝒪 h𝒪).obj.obj U` — and neither is found
from the other by instance search. `m ⊗ₜ[𝒪.obj U] n` elaborates when an expected type
drives it and fails in a bare statement. On a scheme the two coincide as `Γ(X, U)`, so the
elementwise API is stated here and not there.

**Restriction compatibility is one application of naturality.** `map_tensorSection` is
`PresheafOfModules.naturality_apply` at `toTensorSection`, with no rewriting: the restriction of a
pure tensor in the sectionwise tensor product is the pure tensor of the restrictions
(`PresheafOfModules.tensorObj_map_tmul`) by `rfl`, so the two sides meet definitionally and the
naturality square is the whole proof. The germ statement is that plus
`TopCat.Presheaf.germ_res_apply`.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)

## What is not done

No `@[stacks]` attribute is attached: nothing here is the statement of a tag.

**The comparison is not an isomorphism and nothing here says it is.** It is locally bijective
(`Stacks.SectionTensorFormula.isLocallySurjective_toSheafify_tensor` and its injective
companion); over a given open it is in general neither injective nor surjective, which is the
reason the tensor product is sheafified. In particular no statement here says that a section of
`F ⊗ G` over an affine open is a sum of pure tensors.

`(F ⊗ G)|_U ≅ F|_U ⊗ G|_U` is **not** proved, and it is not cheap. The
section modules and the scalars on both sides do agree definitionally — `Γ(M.restrict U.ι, V)` is
`Γ(M, U.ι ''ᵁ V)` and `Γ(U.toScheme, V)` is `Γ(X, U.ι ''ᵁ V)`, both by `rfl` — so the *data* of the
comparison is free, and `map_tensorSection` is exactly its naturality. What is not free is the
statement: `Γ(F|_U ⊗ G|_U, V)` and `Γ((F ⊗ G)|_U, V)` are sections of two different sheaves, built
by sheafifying over two different sites, and no equation between them can be written before the
isomorphism exists. So the isomorphism is the content rather than a consequence of the section
formula, and it remains a statement about the monoidal structure of `SheafOfModules.overFunctor` —
see the "What is not done" of `StacksFrontier/AlgebraicGeometry/TwistTensor/Basic.lean`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open TopologicalSpace Opposite Stacks.SheafOfModules.TensorSheafification

universe u

namespace Stacks.SectionTensorFormula

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory

variable {X : Scheme.{u}}

/-- The sheaf condition on the underlying presheaf of rings of a scheme, in the packaging the
general file is stated over. -/
abbrev schemeSheafCondition (X : Scheme.{u}) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (structureRingPresheaf X.presheaf) :=
  Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X

/-! ### The comparison -/

/-- **The monoidal product of `X.Modules` on sections.** For `F G : X.Modules` and an open `U`,
this is the canonical `Γ(X, U)`-linear map

  `Γ(F, U) ⊗_{Γ(X, U)} Γ(G, U) ⟶ Γ(F ⊗ G, U)`.

It is `Stacks.SectionTensorFormula.toTensorSection` evaluated at `U`: the sections of the
sectionwise tensor product of the underlying presheaves *are* the tensor product of the modules of
sections, by definition, and the comparison is the sheafification unit read in `F ⊗ G` through
`tensorSheafIsoTensorObj`.

It is **not** an isomorphism; see the module documentation. -/
def tensorSectionLinear (F G : X.Modules) (U : X.Opens) :
    TensorProduct Γ(X, U) Γ(F, U) Γ(G, U) →ₗ[Γ(X, U)] Γ(F ⊗ G, U) :=
  ((toTensorSection X.presheaf (schemeSheafCondition X) F G).app (op U)).hom

/-- **The product of two sections**, i.e. the formula for where a pure tensor goes: the image of
`m ⊗ₜ n` under `tensorSectionLinear`. -/
def tensorSection (F G : X.Modules) {U : X.Opens} (m : Γ(F, U)) (n : Γ(G, U)) : Γ(F ⊗ G, U) :=
  tensorSectionLinear F G U (m ⊗ₜ[Γ(X, U)] n)

@[inherit_doc] scoped notation:70 m:70 " ⊗ₛ " n:71 =>
  Stacks.SectionTensorFormula.tensorSection _ _ m n

variable (F G : X.Modules) {U : X.Opens}

/-- The map `tensorSectionLinear F G U` sends `m ⊗ₜ n` to `tensorSection F G m n`. -/
@[simp]
lemma tensorSectionLinear_tmul (m : Γ(F, U)) (n : Γ(G, U)) :
    tensorSectionLinear F G U (m ⊗ₜ[Γ(X, U)] n) = tensorSection F G m n :=
  rfl

/-- **The formula on sections, unfolded.** The product of two sections is their pure tensor pushed
through the sheafification unit of the sectionwise tensor product and read in `F ⊗ G` through the
identification `tensorSheafIsoTensorObj`. True by `rfl`. -/
lemma tensorSection_eq (m : Γ(F, U)) (n : Γ(G, U)) :
    tensorSection F G m n =
      (tensorSheafIsoTensorObj X.presheaf (schemeSheafCondition X) F G).hom.val.app (op U)
        ((toSheafify X.presheaf (schemeSheafCondition X) (F.val ⊗ G.val)).app (op U)
          (m ⊗ₜ[Γ(X, U)] n)) :=
  rfl

/-! ### Bilinearity -/

/-- The product of sections is additive in the first factor. -/
lemma tensorSection_add_left (m m' : Γ(F, U)) (n : Γ(G, U)) :
    tensorSection F G (m + m') n = tensorSection F G m n + tensorSection F G m' n :=
  (congrArg (tensorSectionLinear F G U) (TensorProduct.add_tmul m m' n)).trans (map_add _ _ _)

/-- The product of sections is additive in the second factor. -/
lemma tensorSection_add_right (m : Γ(F, U)) (n n' : Γ(G, U)) :
    tensorSection F G m (n + n') = tensorSection F G m n + tensorSection F G m n' :=
  (congrArg (tensorSectionLinear F G U) (TensorProduct.tmul_add m n n')).trans (map_add _ _ _)

/-- The product of sections is `Γ(X, U)`-linear in the first factor. -/
lemma tensorSection_smul_left (r : Γ(X, U)) (m : Γ(F, U)) (n : Γ(G, U)) :
    tensorSection F G (r • m) n = r • tensorSection F G m n :=
  (congrArg (tensorSectionLinear F G U) (TensorProduct.smul_tmul' r m n).symm).trans
    (map_smul _ _ _)

/-- The product of sections is `Γ(X, U)`-linear in the second factor. -/
lemma tensorSection_smul_right (r : Γ(X, U)) (m : Γ(F, U)) (n : Γ(G, U)) :
    tensorSection F G m (r • n) = r • tensorSection F G m n :=
  (congrArg (tensorSectionLinear F G U) (TensorProduct.tmul_smul r m n)).trans (map_smul _ _ _)

/-- The product of the zero section with any section is zero. -/
@[simp]
lemma tensorSection_zero_left (n : Γ(G, U)) : tensorSection F G (0 : Γ(F, U)) n = 0 :=
  (congrArg (tensorSectionLinear F G U) (TensorProduct.zero_tmul _ n)).trans (map_zero _)

/-- The product of any section with the zero section is zero. -/
@[simp]
lemma tensorSection_zero_right (m : Γ(F, U)) : tensorSection F G m (0 : Γ(G, U)) = 0 :=
  (congrArg (tensorSectionLinear F G U) (TensorProduct.tmul_zero _ m)).trans (map_zero _)

/-! ### Restriction and germs -/

/-- **Restriction compatibility.** The product of two sections over `U` restricts, along an
inclusion `V ⟶ U` of opens, to the product of their restrictions. One application of
`PresheafOfModules.naturality_apply`: the restriction of a pure tensor is the pure tensor of the
restrictions by `rfl`. -/
lemma map_tensorSection {V : X.Opens} (i : V ⟶ U) (m : Γ(F, U)) (n : Γ(G, U)) :
    (F ⊗ G).presheaf.map i.op (tensorSection F G m n) =
      tensorSection F G (F.presheaf.map i.op m) (G.presheaf.map i.op n) :=
  (PresheafOfModules.naturality_apply
    (toTensorSection X.presheaf (schemeSheafCondition X) F G) i.op (m ⊗ₜ[Γ(X, U)] n)).symm

/-- **Germ compatibility.** The germ at a point of the product of two sections does not change if
both factors are first restricted to a smaller open containing that point. -/
lemma germ_tensorSection {V : X.Opens} (i : V ⟶ U) (x : X) (hx : x ∈ V)
    (m : Γ(F, U)) (n : Γ(G, U)) :
    (F ⊗ G).presheaf.germ V x hx
        (tensorSection F G (F.presheaf.map i.op m) (G.presheaf.map i.op n)) =
      (F ⊗ G).presheaf.germ U x (i.le hx) (tensorSection F G m n) :=
  (congrArg ((F ⊗ G).presheaf.germ V x hx) (map_tensorSection F G i m n).symm).trans
    ((F ⊗ G).presheaf.germ_res_apply i x hx _)

end Stacks.SectionTensorFormula

end
