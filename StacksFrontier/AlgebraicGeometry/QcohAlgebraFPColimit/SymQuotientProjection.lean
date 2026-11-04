module

public import StacksFrontier.AlgebraicGeometry.Constructions.SymmetricAlgebraQuotientFunctorial
public import StacksFrontier.AlgebraicGeometry.FiniteTypeDominating.Basic
public import StacksFrontier.AlgebraicGeometry.QcohAlgebraFPColimit.SymmetricAlgebraLiftCompat

/-!
# The projection of `Spec_X(𝒜)` to the vector bundles of a directed system of modules

Let `X` be a scheme, `𝒜` a quasi-coherent sheaf of commutative `𝒪_X`-algebras, and let
`D : I ⥤ 𝒪_X-Mod` be a system of quasi-coherent modules with maps `φᵢ : ℱᵢ ⟶ 𝒜`. Each `φᵢ`
extends to a morphism of algebra sheaves `Sym(ℱᵢ) ⟶ 𝒜`, which under the universal property of
the relative spectrum is a morphism of schemes over `X`

`pᵢ : Spec_X(𝒜) ⟶ 𝐕(ℱᵢ)`,

and these morphisms are **compatible with the transition maps** of the system: `pⱼ` followed by
`𝐕(ℱⱼ) ⟶ 𝐕(ℱᵢ)` is `pᵢ`. That compatibility is what makes the quotients `Sym(ℱᵢ)/ℐ` of
[Stacks, Tag 05JS] into a system with a cocone over `𝒜`, and it is the content of this file.

## Main definitions

* `Stacks.SymQuotientSystem.symLift`: the morphism of algebra sheaves `Sym(ℱᵢ) ⟶ 𝒜` extending
  `φᵢ`.
* `Stacks.SymQuotientSystem.proj`: **the projection `pᵢ : Spec_X(𝒜) ⟶ 𝐕(ℱᵢ)`.**
* `Stacks.SymQuotientSystem.quotIncl`: the closed immersion `𝐙(ℐ) ⟶ 𝐕(ℱ)` as a morphism of
  schemes over `X`.

## Main results

* `Stacks.SymQuotientSystem.proj_comp`: **the projections are compatible with the transition
  maps.**
* `Stacks.SymQuotientSystem.vectorBundleMap_homOfLE_refl` and `vectorBundleMap_homOfLE_trans`:
  the transition morphisms of vector bundles are the identity at a reflexivity proof, and
  compose. They are stated at the spelling `𝐕(D.map (homOfLE h))` rather than behind an
  abbreviation: crossing an abbreviation of a vector-bundle morphism inside a substituted motive
  makes the kernel evaluate the glueing that builds the relative spectrum.
* `Stacks.SymQuotientSystem.quotIncl_comp_quotientAlgebraLift`: the morphism of algebra sheaves
  out of `Sym(ℱ)/ℐ` induced by a morphism `q` into `𝐕(ℱ)`, precomposed with the surjection from
  `Sym(ℱ)`, is the morphism induced by `q` itself.
* `Stacks.SymQuotientSystem.isAffineHom_proj_left` and `compactSpace_vectorBundle`,
  `quasiSeparatedSpace_vectorBundle`: the finiteness hypotheses the capture lemma of
  `Stacks.FiniteTypeIdealSheaf.exists_isFiniteType_le_mem` needs on `𝐕(ℱ)` and on `pᵢ`, derived
  from `X` being quasi-compact and quasi-separated along the affine projection `𝐕(ℱ) ⟶ X`.

## Implementation notes

**One spelling for the comparison isomorphism.** `𝐕(ℱ)` is the relative spectrum of `Sym(ℱ)`,
so `(𝐕(ℱ) ⟶ X)_* 𝒪 ≅ Sym(ℱ)` has two spellings — `vectorBundlePushforwardIso` and
`Stacks.AlgebraicGeometry.FiniteTypeDominating.relativeSpecOverIso` of `Sym(ℱ)`. Everything
below is phrased with the first, since the quotient API of
`StacksFrontier.AlgebraicGeometry.Constructions.SymmetricAlgebraQuotientFunctorial` is; a `rewrite`
whose motive mixes the two unfolds the glueing that builds the relative spectrum.

**Why `proj` needs a compatibility lemma and not a functor.** There is no functor `i ↦ 𝐕(ℱᵢ)`
with a cone over it: the relative spectrum has no map-on-morphisms in this library, which is why
`AlgebraicGeometry.Scheme.Modules.vectorBundleMap` is built from the hom-set bijection. The
compatibility `proj_comp` is then faithfulness of pushforward applied to
`Stacks.SymAlgSheaf.algebraLift_comp`, and the latter is *not* a consequence of the defining
degree-one equation of the lift; see
`StacksFrontier.AlgebraicGeometry.QcohAlgebraFPColimit.SymmetricAlgebraLiftCompat`.

**Quasi-coherence of `𝒜` is carried at the `Stacks.RelativeSpec.AlgebraSheaf` spelling**, which
is what the relative spectrum consumes;
`AlgebraicGeometry.Scheme.QuasicoherentAlgebra.IsQuasicoherent` is a second abbreviation of the
same proposition through a second copy of `underlyingModule`, and the two are crossed once, by
ascription, in `isQuasicoherentAlgebra`.

**No `@[stacks]` attribute.** Nothing below is the assertion of a tag; it is the cocone data of
the directed system of [Stacks, Tag 05JS].

## References

* [Stacks Project, Tag 05JS](https://stacks.math.columbia.edu/tag/05JS)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.AffineAlgebraEquivalence Stacks.AlgebraicGeometry.FiniteTypeDominating
open Stacks.SymQuotientAlgebra

universe u

namespace Stacks.SymQuotientSystem

/-! ### Finiteness of a vector bundle over a quasi-compact quasi-separated base -/

variable {X : Scheme.{u}}

/-- **A vector bundle over a quasi-compact base is quasi-compact**: the projection `𝐕(ℱ) ⟶ X`
is an affine morphism, hence quasi-compact. -/
theorem compactSpace_vectorBundle [CompactSpace ↥X] (E : SheafOfModules.{u} X.ringCatSheaf)
    [E.IsQuasicoherent] : CompactSpace ↥(Scheme.Modules.vectorBundle X E) :=
  have := Scheme.Modules.isAffineHom_vectorBundleToBase X E
  QuasiCompact.compactSpace_of_compactSpace (Scheme.Modules.vectorBundleToBase X E)

/-- **A vector bundle over a quasi-separated base is quasi-separated**: the projection
`𝐕(ℱ) ⟶ X` is affine, hence separated and so quasi-separated. -/
theorem quasiSeparatedSpace_vectorBundle [QuasiSeparatedSpace ↥X]
    (E : SheafOfModules.{u} X.ringCatSheaf) [E.IsQuasicoherent] :
    QuasiSeparatedSpace ↥(Scheme.Modules.vectorBundle X E) :=
  have := Scheme.Modules.isAffineHom_vectorBundleToBase X E
  quasiSeparatedSpace_of_quasiSeparated (Scheme.Modules.vectorBundleToBase X E)

/-! ### The closed subscheme as a scheme over the vector bundle -/

/-- **The closed immersion `𝐙(ℐ) ⟶ 𝐕(ℱ)` as a morphism of schemes over `X`.** -/
def quotIncl (E : SheafOfModules.{u} X.ringCatSheaf) [E.IsQuasicoherent]
    (I : (Scheme.Modules.vectorBundle X E).IdealSheafData) :
    symQuotientOver E I ⟶ Scheme.Modules.vectorBundleOver X (F := E) :=
  Over.homMk I.subschemeι rfl

/-- The factorisation of a morphism into `𝐕(ℱ)` killing `ℐ`, followed by the closed immersion,
is the morphism itself. -/
theorem liftOver_comp_quotIncl (E : SheafOfModules.{u} X.ringCatSheaf) [E.IsQuasicoherent]
    (I : (Scheme.Modules.vectorBundle X E).IdealSheafData) {Y : Over X}
    (q : Y ⟶ Scheme.Modules.vectorBundleOver X (F := E)) (hI : I ≤ q.left.ker) :
    liftOver E I q hI ≫ quotIncl E I = q :=
  Over.OverMorphism.ext (liftOver_left_subschemeι E I q hI)

/-- **The morphism of algebra sheaves out of `Sym(ℱ)/ℐ` induced by `q`, read on `Sym(ℱ)`**: the
surjection `Sym(ℱ) ⟶ Sym(ℱ)/ℐ` followed by it is the morphism induced by `q` itself.

This is what makes a section of `Sym(ℱ)` over an open visible in the quotient. -/
theorem quotIncl_comp_quotientAlgebraLift (E : SheafOfModules.{u} X.ringCatSheaf)
    [E.IsQuasicoherent] (I : (Scheme.Modules.vectorBundle X E).IdealSheafData) {Y : Over X}
    (q : Y ⟶ Scheme.Modules.vectorBundleOver X (F := E)) (hI : I ≤ q.left.ker) :
    pushforwardAlgebraMap (quotIncl E I) ≫ quotientAlgebraLift E I q hI =
      pushforwardAlgebraMap q :=
  (pushforwardAlgebraMap_comp (liftOver E I q hI) (quotIncl E I)).symm.trans
    (congrArg (fun t => pushforwardAlgebraMap t) (liftOver_comp_quotIncl E I q hI))

/-! ### The system -/

section Lift

variable (𝒜 : X.QuasicoherentAlgebra) {I : Type u} [Preorder I]
  {D : I ⥤ SheafOfModules.{u} X.ringCatSheaf}
  (φ : D ⟶ (Functor.const I).obj
    (Scheme.QuasicoherentAlgebra.underlyingModule 𝒜 : SheafOfModules.{u} X.ringCatSheaf))

/-- The components of a cocone over `D` with constant vertex compose with the transition maps:
`ℱᵢ ⟶ ℱⱼ ⟶ 𝒜` is `ℱᵢ ⟶ 𝒜`. -/
theorem map_comp_app {i j : I} (h : i ≤ j) : D.map (homOfLE h) ≫ φ.app j = φ.app i :=
  (φ.naturality (homOfLE h)).trans (Category.comp_id _)

/-- **The morphism of algebra sheaves `Sym(ℱᵢ) ⟶ 𝒜` extending `φᵢ`.** -/
def symLift (i : I) :
    (Scheme.Modules.symmetricAlgebraSheaf X (D.obj i) : X.QuasicoherentAlgebra) ⟶ 𝒜 :=
  Stacks.SymAlgSheaf.algebraLift 𝒜 (D.obj i) (φ.app i)

/-- **The extensions to the symmetric algebras form a cocone**: `Sym(ℱᵢ) ⟶ Sym(ℱⱼ) ⟶ 𝒜` is
`Sym(ℱᵢ) ⟶ 𝒜`. This is `Stacks.SymAlgSheaf.algebraLift_comp`. -/
theorem symLift_comp {i j : I} (h : i ≤ j) :
    Scheme.Modules.symmetricAlgebraSheafMap X (D.map (homOfLE h)) ≫ symLift 𝒜 φ j =
      symLift 𝒜 φ i :=
  (Stacks.SymAlgSheaf.algebraLift_comp 𝒜 (D.map (homOfLE h)) (φ.app j)).symm.trans
    (congrArg (Stacks.SymAlgSheaf.algebraLift 𝒜 (D.obj i)) (map_comp_app 𝒜 φ h))

end Lift

section Trans

variable {I : Type u} [Preorder I] {D : I ⥤ SheafOfModules.{u} X.ringCatSheaf}
  [∀ i, (D.obj i).IsQuasicoherent]

/-- **The transition morphism `𝐕(ℱⱼ) ⟶ 𝐕(ℱᵢ)` of vector bundles at a reflexivity proof is the
identity.** -/
theorem vectorBundleMap_homOfLE_refl (i : I) (h : i ≤ i) :
    Scheme.Modules.vectorBundleMap X (D.map (homOfLE h)) =
      𝟙 (Scheme.Modules.vectorBundleOver X (F := D.obj i)) := by
  have he : homOfLE h = 𝟙 i := Subsingleton.elim _ _
  have hid : D.map (homOfLE h) = 𝟙 (D.obj i) := by rw [he, D.map_id]
  rw [hid, Scheme.Modules.vectorBundleMap_id]

/-- **The transition morphisms of vector bundles compose**, contravariantly. -/
theorem vectorBundleMap_homOfLE_trans {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (hik : i ≤ k) :
    Scheme.Modules.vectorBundleMap X (D.map (homOfLE hik)) =
      Scheme.Modules.vectorBundleMap X (D.map (homOfLE hjk)) ≫
        Scheme.Modules.vectorBundleMap X (D.map (homOfLE hij)) := by
  have hcomp : D.map (homOfLE hik) = D.map (homOfLE hij) ≫ D.map (homOfLE hjk) := by
    rw [← D.map_comp]
    exact congrArg D.map (Subsingleton.elim _ _)
  rw [hcomp, Scheme.Modules.vectorBundleMap_comp]

end Trans

section Proj

variable (𝒜 : X.QuasicoherentAlgebra) [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent 𝒜]
  {I : Type u} [Preorder I] {D : I ⥤ SheafOfModules.{u} X.ringCatSheaf}
  [∀ i, (D.obj i).IsQuasicoherent]
  (φ : D ⟶ (Functor.const I).obj
    (Scheme.QuasicoherentAlgebra.underlyingModule 𝒜 : SheafOfModules.{u} X.ringCatSheaf))

/-- Quasi-coherence of `𝒜` at the `AlgebraicGeometry.Scheme.QuasicoherentAlgebra` spelling. The
two abbreviations unfold to the quasi-coherence of two copies of the underlying module, which are
the same object; this is the single crossing. -/
theorem isQuasicoherentAlgebra : Scheme.QuasicoherentAlgebra.IsQuasicoherent 𝒜 :=
  (inferInstance : Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent 𝒜)

/-- **The projection `Spec_X(𝒜) ⟶ 𝐕(ℱᵢ)`**, the morphism of schemes over `X` classified by
`Sym(ℱᵢ) ⟶ 𝒜` under the universal property of the relative spectrum. -/
def proj (i : I) : relativeSpecOver 𝒜 ⟶ Scheme.Modules.vectorBundleOver X (F := D.obj i) :=
  have := Scheme.Modules.isAffineHom_vectorBundleOver X (F := D.obj i)
  (overHomEquivAlgebraHom (relativeSpecOver 𝒜)
      (Scheme.Modules.vectorBundleOver X (F := D.obj i))).symm
    ((Scheme.Modules.vectorBundlePushforwardIso X (F := D.obj i)).hom ≫ symLift 𝒜 φ i ≫
      (relativeSpecOverIso 𝒜).inv)

/-- **The projection is classified by `Sym(ℱᵢ) ⟶ 𝒜`**: its canonical map on pushed-forward
structure sheaves is that morphism, read through the two comparison isomorphisms. This is the
equation that characterizes `proj`. -/
theorem pushforwardAlgebraMap_proj (i : I) :
    have := Scheme.Modules.isAffineHom_vectorBundleOver X (F := D.obj i)
    pushforwardAlgebraMap (proj 𝒜 φ i) =
      (Scheme.Modules.vectorBundlePushforwardIso X (F := D.obj i)).hom ≫ symLift 𝒜 φ i ≫
        (relativeSpecOverIso 𝒜).inv :=
  have := Scheme.Modules.isAffineHom_vectorBundleOver X (F := D.obj i)
  (overHomEquivAlgebraHom_apply (proj 𝒜 φ i)).symm.trans (Equiv.apply_symm_apply _ _)

/-- **The projections are compatible with the transition maps of the system**: `pⱼ` followed by
`𝐕(ℱⱼ) ⟶ 𝐕(ℱᵢ)` is `pᵢ`.

Both sides are morphisms over `X` into a scheme affine over `X`, so they agree as soon as their
canonical maps on pushed-forward structure sheaves do; there the statement is
`Stacks.SymQuotientSystem.symLift_comp` with the comparison isomorphisms cancelling. -/
theorem proj_comp {i j : I} (h : i ≤ j) :
    proj 𝒜 φ j ≫ Scheme.Modules.vectorBundleMap X (D.map (homOfLE h)) = proj 𝒜 φ i := by
  have := Scheme.Modules.isAffineHom_vectorBundleOver X (F := D.obj i)
  refine eq_of_pushforwardAlgebraMap_eq ?_
  rw [pushforwardAlgebraMap_comp, pushforwardAlgebraMap_proj,
    Scheme.Modules.pushforwardAlgebraMap_vectorBundleMap, pushforwardAlgebraMap_proj,
    ← symLift_comp 𝒜 φ h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-! ### Finiteness of the projection -/

/-- **The projection `Spec_X(𝒜) ⟶ 𝐕(ℱᵢ)` is an affine morphism.** Its composite with the
projection of the vector bundle is the structure morphism of the relative spectrum, which is
affine, and the projection of the vector bundle is affine and hence separated. -/
theorem isAffineHom_proj_left (i : I) : IsAffineHom (proj 𝒜 φ i).left := by
  have := Scheme.Modules.isAffineHom_vectorBundleOver X (F := D.obj i)
  have : IsSeparated (Scheme.Modules.vectorBundleOver X (F := D.obj i)).hom :=
    IsSeparated.of_isAffineHom (Scheme.Modules.vectorBundleOver X (F := D.obj i)).hom
  have : IsAffineHom ((proj 𝒜 φ i).left ≫
      (Scheme.Modules.vectorBundleOver X (F := D.obj i)).hom) := by
    rw [Over.w]
    exact isAffineHom_relativeSpecOver 𝒜
  exact IsAffineHom.of_comp (proj 𝒜 φ i).left
    (Scheme.Modules.vectorBundleOver X (F := D.obj i)).hom

/-- **The projection is quasi-compact**, which is what
`AlgebraicGeometry.Scheme.Hom.ker_apply` needs in order to compute its kernel ideal sheaf on an
affine open as the kernel of its map on sections. -/
theorem quasiCompact_proj_left (i : I) : QuasiCompact (proj 𝒜 φ i).left :=
  have := isAffineHom_proj_left 𝒜 φ i
  inferInstance

end Proj

end Stacks.SymQuotientSystem

end
