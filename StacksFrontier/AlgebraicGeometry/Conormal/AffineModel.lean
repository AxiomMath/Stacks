module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Cotangent
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.IdealSheafAffine
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.AlgebraicGeometry.Thickenings.ConormalSheaf

/-!
# The conormal sheaf of `Spec (R ⧸ I) ⟶ Spec R`

Let `R` be a commutative ring and `I ⊆ R` an ideal, and let `i : Spec (R ⧸ I) ⟶ Spec R` be the
associated closed immersion. This file computes the conormal sheaf
`𝒞 = i^* Ker(𝒪_{Spec R} ⟶ i_* 𝒪_{Spec (R ⧸ I)})` of `i`: it is the sheaf associated to the
`R ⧸ I`-module `(R ⧸ I) ⊗_R I`, and its global sections, read as an `R`-module through `i_*`, are
Mathlib's `Ideal.Cotangent I`, that is `I/I²`.

The identification is not asserted only up to an arbitrary automorphism: it is pinned by
`Stacks.ClosedImmersion.AffineConormal.conormalΓIso_unit_toOpen`, which says that the section of
the ideal sheaf determined by `x : I` goes, under the canonical map from the ideal sheaf to the
pushforward of the conormal sheaf — the unit of `i^* ⊣ i_*` — to the class `I.toCotangent x`.

This is the **affine model** of [Stacks Project, Tag 01R3] part (2), and only that. Tag 01R3 part
(2) is a statement about an arbitrary immersion `j : Z ⟶ X` of schemes and an affine open
`V ⊆ X` with `Z ∩ V = Spec (Γ(X, V) ⧸ I)`: its conclusion is about the sections of the conormal
sheaf of `j`, a sheaf on all of `Z`, over `j ⁻¹ᵁ V`. Deducing that from what is proved here needs
two comparisons that the library does not have, and neither is proved below:

* the restriction of the conormal sheaf of `j` to `j ⁻¹ᵁ V` is the conormal sheaf of the closed
  immersion `j ⁻¹ᵁ V ⟶ V` obtained by restricting a closed factorization of `j` — a base-change
  statement for `RingedSpaceModuleAdjunction.modulePullback` and
  `Stacks.ClosedImmersion.idealSheaf` along open immersions, which is also the first half of
  [Stacks Project, Tag 01R3] part (1);
* transport of the whole computation along the isomorphisms `V ≅ Spec Γ(X, V)` of
  `AlgebraicGeometry.IsAffineOpen.isoSpec` and `j ⁻¹ᵁ V ≅ Spec (Γ(X, V) ⧸ I)`.

Consequently **nothing here carries a `01R3` attribute**; the tag stays unplaced.

## Main definitions

* `Stacks.ClosedImmersion.AffineConormal.quotImmersion` is the closed immersion
  `Spec (R ⧸ I) ⟶ Spec R`.
* `Stacks.ClosedImmersion.AffineConormal.tildeIdealSheafIso` identifies `I^~` with the ideal
  sheaf of that closed immersion.
* `Stacks.ClosedImmersion.AffineConormal.conormalTildeIso` identifies its conormal sheaf with the
  sheaf associated to `(R ⧸ I) ⊗_R I`.
* `Stacks.ClosedImmersion.AffineConormal.conormalΓIso` identifies the global sections of the
  pushforward of the conormal sheaf with `I/I²`, as `R`-modules.

## Main results

* `Stacks.ClosedImmersion.AffineConormal.tildeIdealSheafIso_hom_comp_idealSheafι`: the
  identification of `I^~` with the ideal sheaf is compatible with the two inclusions into
  `𝒪_{Spec R}`, which determines it.
* `Stacks.ClosedImmersion.AffineConormal.conormalTildeIso_hom_unit_toOpen` and
  `Stacks.ClosedImmersion.AffineConormal.conormalΓIso_unit_toOpen`: the canonical quotient map
  from the ideal sheaf to the pushforward of the conormal sheaf sends the section determined by
  `x : I` to `1 ⊗ x`, respectively to `I.toCotangent x`.
* `Stacks.ClosedImmersion.AffineConormal.quotTensorEquivQuotSMul_one_tmul`: the algebraic core,
  `I ⊗_R R/I = I/I²` on the generator `1 ⊗ x`.

## Implementation notes

The three inputs are all already in the library, and the file is their composition.

* `Stacks.ClosedImmersion.IdealSheafAffine.exists_tilde_iso_kernel_quotUnitHom` (the affine case
  of [Stacks Project, Tag 01IN]) identifies `I^~` with the ideal sheaf. Its conclusion is stated
  for `CategoryTheory.Limits.kernel` of
  `CategoryTheory.SheafOfModules.unitToPushforwardObjUnit` of
  `AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom`, which is *definitionally*
  `Stacks.ClosedImmersion.idealSheaf` of the underlying morphism of ringed spaces; likewise
  `AlgebraicGeometry.Scheme.Modules.pullback` is definitionally
  `RingedSpaceModuleAdjunction.modulePullback` on the underlying ringed spaces. Both
  identifications hold by `rfl`, so the two vocabularies may be mixed freely in *terms* — but
  not in `rw`, see below.
* `AlgebraicGeometry.pullbackTildeIso` ([Stacks Project, Tag 01I9]) turns the pullback of `I^~`
  into the sheaf associated to `(R ⧸ I) ⊗_R I`, and
  `AlgebraicGeometry.pullbackTildeIso_hom_app_unit_toOpen` says it sends the image of `x` under
  the adjunction unit to `1 ⊗ x`. That normalization is what makes the generator formulas below
  provable rather than merely plausible.
* `TensorProduct.quotTensorEquivQuotSMul` is `(R ⧸ I) ⊗_R M ≃ₗ[R] M ⧸ I • ⊤`, which at `M = I` is
  `Ideal.Cotangent I` by definition.

Two elaboration points govern the shape of the proofs.

The target of `conormalΓIso` is a module over `R`, not over `R ⧸ I`. That is forced by the
statement being about the *pushforward* of the conormal sheaf, whose sections are `𝒪_{Spec R}`
modules, and it is also what [Stacks Project, Tag 01R3] part (2) asks for. It is fortunate: the
`R ⧸ I`-module structure on `Ideal.Cotangent I` is produced by `deriving instance`, so it is only
definitionally the one on `I ⧸ I • ⊤` that `TensorProduct.quotTensorEquivQuotSMul` lands in, and
an `R ⧸ I`-linear version of that equivalence cannot be assembled by `rw` without the
transparency flag that Mathlib's own `Ideal.Cotangent` lemmas use and this repository forbids.
Over `R` no such comparison is needed.

For the same reason the generator formulas are proved by `Eq.trans` chains over explicitly stated
intermediate equations rather than by rewriting: `AlgebraicGeometry.Scheme.Modules` carries its
own `CategoryTheory.Category` instance, so a goal mentioning
`Stacks.ClosedImmersion.conormalSheaf` — which is `CategoryTheory.SheafOfModules`-typed — under
`AlgebraicGeometry.Scheme.Modules.pushforward` is not type-correct at `implicit` transparency and
`rw` refuses to build its motive. Every step that crosses the two vocabularies is therefore
either `rfl` or a `congr(...)` congruence applied at default transparency.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 01IN](https://stacks.math.columbia.edu/tag/01IN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct
open RingedSpaceModuleAdjunction Stacks.ClosedImmersion.IdealSheafAffine
open scoped ChangeOfRings

universe u

namespace Stacks.ClosedImmersion.AffineConormal

variable (R : CommRingCat.{u}) (I : Ideal R)

/-- The closed immersion `Spec (R ⧸ I) ⟶ Spec R` cut out by an ideal `I` of `R`. -/
abbrev quotImmersion : Spec (quotRing I) ⟶ Spec R := Spec.map (quotHom I)

/-- The sheaf `I^~` associated to an ideal `I` of `R` is the ideal sheaf of the closed immersion
`Spec (R ⧸ I) ⟶ Spec R`.

This is `Stacks.ClosedImmersion.IdealSheafAffine.exists_tilde_iso_kernel_quotUnitHom`, the affine
case of [Stacks Project, Tag 01IN], read in the ringed-space vocabulary of
`Stacks.ClosedImmersion.idealSheaf`; the two spellings of the kernel are definitionally equal.
The isomorphism is pinned by
`Stacks.ClosedImmersion.AffineConormal.tildeIdealSheafIso_hom_comp_idealSheafι`. -/
def tildeIdealSheafIso :
    tilde (ModuleCat.of R I) ≅ idealSheaf (quotImmersion R I).toLRSHom.toShHom :=
  (exists_tilde_iso_kernel_quotUnitHom I).choose

/-- The identification of `I^~` with the ideal sheaf of `Spec (R ⧸ I) ⟶ Spec R` is compatible
with the two inclusions into `𝒪_{Spec R}`: the inclusion of the ideal sheaf pulls back to the
sheafification of the inclusion `I ⟶ R`. Since those inclusions are monomorphisms this
determines `Stacks.ClosedImmersion.AffineConormal.tildeIdealSheafIso`. -/
theorem tildeIdealSheafIso_hom_comp_idealSheafι :
    (tildeIdealSheafIso R I).hom ≫ idealSheafι (quotImmersion R I).toLRSHom.toShHom =
      tilde.map (ModuleCat.ofHom I.subtype) ≫ tildeSelf.hom :=
  (exists_tilde_iso_kernel_quotUnitHom I).choose_spec

/-- **The conormal sheaf of `Spec (R ⧸ I) ⟶ Spec R`.** It is the sheaf on `Spec (R ⧸ I)`
associated to the `R ⧸ I`-module `(R ⧸ I) ⊗_R I`.

This is the affine model of the first identification `𝒞_{Z/X} = (i')^* ℐ` of
[Stacks Project, Tag 01R3] part (1) composed with the affine computation of the pullback,
[Stacks Project, Tag 01I9]. -/
def conormalTildeIso :
    conormalSheaf (quotImmersion R I).toLRSHom.toShHom ≅
      tilde ((ModuleCat.extendScalars (quotHom I).hom).obj (ModuleCat.of R I)) :=
  (Scheme.Modules.pullback (quotImmersion R I)).mapIso (tildeIdealSheafIso R I).symm ≪≫
    (pullbackTildeIso R (quotRing I) (quotHom I)).app (ModuleCat.of R I)

/-- **The generator formula for the conormal sheaf of `Spec (R ⧸ I) ⟶ Spec R`.** The canonical
map from the ideal sheaf to the pushforward of the conormal sheaf — the unit of `i^* ⊣ i_*` —
carries the global section of the ideal sheaf determined by `x : I` to `1 ⊗ x`.

Since the unit is the map that [Stacks Project, Tag 01R3] part (1) exhibits as the quotient of
the ideal sheaf by the square of the ideal, this is what identifies
`Stacks.ClosedImmersion.AffineConormal.conormalTildeIso` as *the* canonical isomorphism rather
than one of many. -/
theorem conormalTildeIso_hom_unit_toOpen (x : ↥I) :
    (conormalTildeIso R I).hom.val.app (.op ⊤)
      (((Scheme.Modules.pullbackPushforwardAdjunction (quotImmersion R I)).unit.app
          (idealSheaf (quotImmersion R I).toLRSHom.toShHom)).val.app (.op ⊤)
        ((tildeIdealSheafIso R I).hom.val.app (.op ⊤)
          (tilde.toOpen (ModuleCat.of R I) ⊤ x))) =
      tilde.toOpen ((ModuleCat.extendScalars (quotHom I).hom).obj (ModuleCat.of R I)) ⊤
        ((1 : quotRing I) ⊗ₜ[R, (quotHom I).hom] x) := by
  have hinv : (tildeIdealSheafIso R I).inv.val.app (.op ⊤)
      ((tildeIdealSheafIso R I).hom.val.app (.op ⊤)
        (tilde.toOpen (ModuleCat.of R I) ⊤ x)) = tilde.toOpen (ModuleCat.of R I) ⊤ x :=
    congr($((tildeIdealSheafIso R I).hom_inv_id).val.app (.op ⊤)
      (tilde.toOpen (ModuleCat.of R I) ⊤ x))
  have hnat : ((Scheme.Modules.pullbackPushforwardAdjunction (quotImmersion R I)).unit.app
        (tilde (ModuleCat.of R I))).val.app (.op ⊤)
        ((tildeIdealSheafIso R I).inv.val.app (.op ⊤)
          ((tildeIdealSheafIso R I).hom.val.app (.op ⊤)
            (tilde.toOpen (ModuleCat.of R I) ⊤ x))) =
      ((Scheme.Modules.pullback (quotImmersion R I)).map
          (tildeIdealSheafIso R I).inv).val.app (.op ⊤)
        (((Scheme.Modules.pullbackPushforwardAdjunction (quotImmersion R I)).unit.app
            (idealSheaf (quotImmersion R I).toLRSHom.toShHom)).val.app (.op ⊤)
          ((tildeIdealSheafIso R I).hom.val.app (.op ⊤)
            (tilde.toOpen (ModuleCat.of R I) ⊤ x))) :=
    congr($((Scheme.Modules.pullbackPushforwardAdjunction (quotImmersion R I)).unit.naturality
        (tildeIdealSheafIso R I).inv).val.app (.op ⊤)
      ((tildeIdealSheafIso R I).hom.val.app (.op ⊤) (tilde.toOpen (ModuleCat.of R I) ⊤ x)))
  exact (congrArg (fun z => ((pullbackTildeIso R (quotRing I) (quotHom I)).hom.app
      (ModuleCat.of R I)).val.app (.op ⊤) z) (hnat.symm.trans (congrArg
        (fun z => ((Scheme.Modules.pullbackPushforwardAdjunction (quotImmersion R I)).unit.app
          (tilde (ModuleCat.of R I))).val.app (.op ⊤) z) hinv))).trans
    (pullbackTildeIso_hom_app_unit_toOpen R (quotRing I) (quotHom I) (ModuleCat.of R I) x)

/-- **`I ⊗_R R/I = I/I²` on generators.** The equivalence
`TensorProduct.quotTensorEquivQuotSMul` sends `1 ⊗ x` to the class of `x` in `Ideal.Cotangent I`.

This is the computation the proof of [Stacks Project, Tag 01R3] refers to as "given a ring `R`
and an ideal `I` of `R` we have `I/I² = I ⊗_R R/I`". -/
theorem quotTensorEquivQuotSMul_one_tmul (x : ↥I) :
    TensorProduct.quotTensorEquivQuotSMul (R := R) (↥I) I
      ((1 : R ⧸ I) ⊗ₜ[R] x) = I.toCotangent x := by
  show TensorProduct.quotTensorEquivQuotSMul (R := R) (↥I) I ((1 : R ⧸ I) ⊗ₜ[R] x) = _
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]
  rfl

/-- **The sections of the conormal sheaf of `Spec (R ⧸ I) ⟶ Spec R` are `I/I²`.** Pushed forward
along the closed immersion, so as `R`-modules, the global sections of the conormal sheaf are
Mathlib's `Ideal.Cotangent I`.

This is the affine model of [Stacks Project, Tag 01R3] part (2); see the module docstring for
what separates it from that statement. It is pinned by
`Stacks.ClosedImmersion.AffineConormal.conormalΓIso_unit_toOpen`. -/
def conormalΓIso :
    moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward (quotImmersion R I)).obj
        (conormalSheaf (quotImmersion R I).toLRSHom.toShHom)) ≅
      ModuleCat.of R I.Cotangent :=
  moduleSpecΓFunctor.mapIso
      ((Scheme.Modules.pushforward (quotImmersion R I)).mapIso (conormalTildeIso R I)) ≪≫
    (pushforwardΓIso R (quotRing I) (quotHom I)).app
      (tilde ((ModuleCat.extendScalars (quotHom I).hom).obj (ModuleCat.of R I))) ≪≫
    (ModuleCat.restrictScalars (quotHom I).hom).mapIso
      (tilde.isoTop ((ModuleCat.extendScalars (quotHom I).hom).obj (ModuleCat.of R I))).symm ≪≫
    LinearEquiv.toModuleIso (TensorProduct.quotTensorEquivQuotSMul (R := R) (↥I) I)

/-- **The canonical affine quotient formula.** Under
`Stacks.ClosedImmersion.AffineConormal.conormalΓIso`, the image of the global section of the
ideal sheaf determined by `x : I` under the canonical map to the pushforward of the conormal
sheaf is the class `I.toCotangent x` of `x` modulo `I²`.

Because that canonical map is an epimorphism of sheaves — the content of
[Stacks Project, Tag 01R3] part (1) — this formula determines the isomorphism. -/
theorem conormalΓIso_unit_toOpen (x : ↥I) :
    (conormalΓIso R I).hom.hom
      (((Scheme.Modules.pullbackPushforwardAdjunction (quotImmersion R I)).unit.app
          (idealSheaf (quotImmersion R I).toLRSHom.toShHom)).val.app (.op ⊤)
        ((tildeIdealSheafIso R I).hom.val.app (.op ⊤)
          (tilde.toOpen (ModuleCat.of R I) ⊤ x))) = I.toCotangent x := by
  have hC : (tilde.isoTop ((ModuleCat.extendScalars (quotHom I).hom).obj
        (ModuleCat.of R I))).inv.hom
      (tilde.toOpen ((ModuleCat.extendScalars (quotHom I).hom).obj (ModuleCat.of R I)) ⊤
        ((1 : quotRing I) ⊗ₜ[R, (quotHom I).hom] x)) =
      (1 : quotRing I) ⊗ₜ[R, (quotHom I).hom] x :=
    congr($((tilde.isoTop ((ModuleCat.extendScalars (quotHom I).hom).obj
        (ModuleCat.of R I))).hom_inv_id).hom ((1 : quotRing I) ⊗ₜ[R, (quotHom I).hom] x))
  have hΓ : (conormalΓIso R I).hom.hom
      (((Scheme.Modules.pullbackPushforwardAdjunction (quotImmersion R I)).unit.app
          (idealSheaf (quotImmersion R I).toLRSHom.toShHom)).val.app (.op ⊤)
        ((tildeIdealSheafIso R I).hom.val.app (.op ⊤)
          (tilde.toOpen (ModuleCat.of R I) ⊤ x))) =
      TensorProduct.quotTensorEquivQuotSMul (R := R) (↥I) I
        ((tilde.isoTop ((ModuleCat.extendScalars (quotHom I).hom).obj
            (ModuleCat.of R I))).inv.hom
          ((conormalTildeIso R I).hom.val.app (.op ⊤)
            (((Scheme.Modules.pullbackPushforwardAdjunction (quotImmersion R I)).unit.app
                (idealSheaf (quotImmersion R I).toLRSHom.toShHom)).val.app (.op ⊤)
              ((tildeIdealSheafIso R I).hom.val.app (.op ⊤)
                (tilde.toOpen (ModuleCat.of R I) ⊤ x))))) := rfl
  refine hΓ.trans ?_
  rw [conormalTildeIso_hom_unit_toOpen, hC]
  exact quotTensorEquivQuotSMul_one_tmul R I x

end Stacks.ClosedImmersion.AffineConormal

end
