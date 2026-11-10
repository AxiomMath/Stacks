module

public import StacksFrontier.AlgebraicGeometry.SymAlgebraQcohPieces.Restrict
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.BaseChange
public import StacksFrontier.AlgebraicGeometry.AffineSymmetricAlgebra.Basic

/-!
# The homogeneous pieces of `Sym(E)` are quasi-coherent, for `E` quasi-coherent

`AlgebraicGeometry.Scheme.Modules.symmetricAlgebra X E` is the degreewise sheafification of
the sectionwise symmetric algebra of an `𝒪_X`-module `E` on an arbitrary scheme. The relative
Proj data `Stacks.SymGraded.schemeSheafGradedAlgebra` and the projective bundle
`Stacks.SymGraded.schemeProjectiveBundle` take quasi-coherence of every homogeneous piece as the
hypothesis `Stacks.SymGraded.IsQuasicoherentPieces`. **This file proves that hypothesis for a
quasi-coherent `E`**.

The hypothesis cannot be dropped for an *arbitrary* module: the degree-one piece is the
sheafification of a presheaf isomorphic to `E`, so quasi-coherence of all the pieces implies
quasi-coherence of `E`. Quasi-coherence of `E` is therefore exactly the right hypothesis, and
this file shows it is sufficient.

## The argument

`Stacks.AlgebraicGeometry.SheafifyRestrict.isQuasicoherentPieces_of_restrict_sheafification`
reduces the statement to an affine base. The affine model of an affine open `V` of `X` is
`Spec Γ(X, V)`, reached by `AlgebraicGeometry.IsAffineOpen.fromSpec`, and over it the proof is a
comparison of two presheaves of `𝒪_{Spec Γ(X, V)}`-modules:

* the base-change presheaf `W ↦ Γ(Spec Γ(X, V), W) ⊗_{Γ(X, V)} Sym^n_{Γ(X, V)}(Γ(E, V))` of
  `Stacks.AffineBaseChange.presheaf`, whose sheafification is the associated sheaf
  `Sym^n_{Γ(X, V)}(Γ(E, V))~` because `Stacks.AffineBaseChange.toTilde` is locally bijective;
* the restriction along `fromSpec` of the sectionwise symmetric power
  `Stacks.SymGraded.siteGradedPiece E.val n`, whose sheafification is the restriction of the
  degree-`n` piece of `Sym(E)` by
  `Stacks.AlgebraicGeometry.ImmersionRestrict.restrictSheafificationIso`.

`Stacks.SymGraded.AffinePieces.toPiece` is the comparison between them, and it is bijective on
every basic open because the symmetric powers of the sections of a quasi-coherent module are a
base change, which is `Stacks.SymGraded.isBaseChange_gradedRestrictₗ_int`. Sheafification
inverts a locally bijective morphism, so the two sheafifications agree and the restricted piece
is an associated sheaf, hence quasi-coherent.

## Main definitions

* `Stacks.SymGraded.AffinePieces.toPieceₗ`: **the comparison on sections**,
  `a ⊗ x ↦ a · (x|_{f(W)})`, as a linear map over `Γ(Spec Γ(X, V), W)`.
* `Stacks.SymGraded.AffinePieces.toPiece`: **the comparison morphism** of presheaves of
  `𝒪_{Spec Γ(X, V)}`-modules.
* `Stacks.SymGraded.AffinePieces.sheafificationIsoTilde`: **the sheafification of the restricted
  sectionwise symmetric power is `Sym^n_{Γ(X, V)}(Γ(E, V))~`.** This is the third assertion of
  Tag 01CG over an affine base, in the form a quasi-coherence argument consumes.

## Main results

* `Stacks.SymGraded.AffinePieces.bijective_toPieceₗ_basicOpen`: **the comparison is bijective on
  a basic open**, and `isLocallySurjective_toPiece`, `isLocallyInjective_toPiece`: it is
  therefore locally bijective.
* `Stacks.SymGraded.AffinePieces.isQuasicoherent_restrict_fromSpec_piece`: the restriction to
  `Spec Γ(X, V)` of the degree-`n` piece of `Sym(E)` is quasi-coherent.
* `Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent`: **`Sym(E)` has quasi-coherent
  homogeneous pieces for every quasi-coherent `E` on an arbitrary scheme.**

## Implementation notes

**Why `fromSpec` and not the inclusion `V.ι`.** The comparison needs the base-change statement
`Stacks.SymGraded.isBaseChange_gradedRestrictₗ_int`, which is about affine opens *of `X`*, and
it needs the basic opens of `Spec Γ(X, V)` as a basis on which to check bijectivity. Restricting
along `fromSpec` puts both in the same place: the sections of the restricted presheaf over `W`
are the sections of the original over `fromSpec ''ᵁ W`, an open of `X`, and the basic open `D(g)`
has `fromSpec ''ᵁ D(g) = X.basicOpen g`, affine. The passage back to `V.ι`, which is what
`isQuasicoherentPieces_of_restrict_affineOpens` asks for, is
`Stacks.AlgebraicGeometry.ImmersionRestrict.isQuasicoherent_restrict_ι_of_fromSpec`.

**The one ring compatibility.** `Γ(Spec Γ(X, V), W)` acts on the sections of the restricted
presheaf through `(fromSpec.appIso W).inv`, while `Γ(X, V)` acts on the graded piece over
`fromSpec ''ᵁ W` through the restriction map of `𝒪_X`. That these agree on the image of
`Γ(X, V)` is `appIso_inv_algebraMap`, and it is the only genuinely geometric input besides the
base-change theorem; its proof is the ring identity inside
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.smul_restrict`, extracted so that it can be
used on the graded pieces rather than on the sections themselves.

**Bijectivity is routed through `IsLocalizedModule`, not through a ring isomorphism.** The
base-change theorem gives `IsBaseChange Γ(X, fromSpec ''ᵁ D(g))`, while the comparison is a base
change along `Γ(Spec Γ(X, V), D(g))`; the two rings are isomorphic but not equal. Transporting
an `IsBaseChange` along that isomorphism means a `TensorProduct.congr`, and the
elaboration of the resulting pointwise comparison exceeds the heartbeat budget. Both rings are
instead localizations of `Γ(X, V)` away from `g` — the first by
`AlgebraicGeometry.IsAffineOpen.isLocalization_of_eq_basicOpen`, which is stated for an open
merely *equal* to a basic open and so needs no transport of the open either — so
`isLocalizedModule_iff_isBaseChange` carries the statement from one to the other through the
ring-independent `IsLocalizedModule`, and the comparison is then literally
`IsBaseChange.equiv`.

**Naturality is proved in term mode.** The module structures here are three deep (a graded piece
of a symmetric algebra, with scalars restricted twice), and `rw` chains over them
time out at `isDefEq` while the same equalities composed with `Eq.trans` and `congrArg`
elaborate in seconds. `pieceRestrictAdd_toPieceₗ_tmul` is written that way for that reason.

## References

* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ImmersionRestrict
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange
open scoped TensorProduct

namespace Stacks.SymGraded.AffinePieces

universe u

variable {X : Scheme.{u}} (E : X.Modules) {V : X.Opens} (hV : IsAffineOpen V) (n : ℤ)

/-! ### The comparison on sections -/

/-- The degree-`n` graded piece of the symmetric algebra of the sections of `E` over `V`, as a
`Γ(X, V)`-module. -/
abbrev pieceAt (E : X.Modules) (V : X.Opens) (n : ℤ) : ModuleCat.{u} Γ(X, V) :=
  ModuleCat.of Γ(X, V) (gradedPiece (R := Γ(X, V)) Γ(E, V) n)

/-- **The comparison of structure sheaves carries the structure map of `Γ(Spec Γ(X, V), W)` to
the restriction map of `𝒪_X`**: the two `Γ(X, V)`-algebra structures on the sections over the
image of `W` agree. -/
theorem appIso_inv_algebraMap (W : (Spec Γ(X, V)).Opens) (r : Γ(X, V)) :
    (hV.fromSpec.appIso W).inv (algebraMap Γ(X, V) Γ(Spec Γ(X, V), W) r) =
      X.presheaf.map (homOfLE (fromSpec_image_le hV W)).op r := by
  have h : X.presheaf.map (homOfLE (fromSpec_image_le hV W)).op ≫ (hV.fromSpec.appIso W).hom =
      (Scheme.ΓSpecIso Γ(X, V)).inv ≫ (Spec Γ(X, V)).presheaf.map W.leTop.op := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE, Scheme.Hom.appLE, hV.fromSpec_app_self,
      Category.assoc, ← Functor.map_comp]
    rfl
  rw [IsAffineOpen.algebraMap_Spec_obj]
  rw [← Iso.eq_comp_inv] at h
  exact congr($(h.symm).hom r)

/-- The `Γ(Spec Γ(X, V), W)`-module structure on the degree-`n` graded piece over the image of
`W`, obtained by restricting scalars along the comparison of structure sheaves. It is the
structure the restricted presheaf of modules carries. -/
@[instance_reducible]
def specPieceModule (W : (Spec Γ(X, V)).Opens) :
    Module Γ(Spec Γ(X, V), W)
      (gradedPiece (R := Γ(X, hV.fromSpec ''ᵁ W)) Γ(E, hV.fromSpec ''ᵁ W) n) :=
  Module.compHom _ (hV.fromSpec.appIso W).inv.hom

/-- The scalar tower `Γ(X, V) → Γ(Spec Γ(X, V), W) → Sym^n_{Γ(X, f(W))}(Γ(E, f(W)))`. -/
theorem pieceIsScalarTower (W : (Spec Γ(X, V)).Opens) :
    letI := gradedModuleOfLE E (fromSpec_image_le hV W) n
    letI := specPieceModule E hV n W
    IsScalarTower Γ(X, V) Γ(Spec Γ(X, V), W)
      (gradedPiece (R := Γ(X, hV.fromSpec ''ᵁ W)) Γ(E, hV.fromSpec ''ᵁ W) n) :=
  let := gradedModuleOfLE E (fromSpec_image_le hV W) n
  let := specPieceModule E hV n W
  IsScalarTower.of_algebraMap_smul fun r x =>
    congrArg (fun s : Γ(X, hV.fromSpec ''ᵁ W) => s • x) (appIso_inv_algebraMap hV W r)

/-- **The comparison on sections**: the base change of `Sym^n_{Γ(X, V)}(Γ(E, V))` to
`Γ(Spec Γ(X, V), W)` maps to `Sym^n_{Γ(X, f(W))}(Γ(E, f(W)))` by `a ⊗ x ↦ a · (x|_{f(W)})`. -/
def toPieceₗ (W : (Spec Γ(X, V)).Opens) :
    letI := specPieceModule E hV n W
    Γ(Spec Γ(X, V), W) ⊗[Γ(X, V)] gradedPiece (R := Γ(X, V)) Γ(E, V) n →ₗ[Γ(Spec Γ(X, V), W)]
      gradedPiece (R := Γ(X, hV.fromSpec ''ᵁ W)) Γ(E, hV.fromSpec ''ᵁ W) n :=
  letI := gradedModuleOfLE E (fromSpec_image_le hV W) n
  letI := specPieceModule E hV n W
  letI := pieceIsScalarTower E hV n W
  (gradedRestrictₗ E (fromSpec_image_le hV W) n).liftBaseChange Γ(Spec Γ(X, V), W)

/-- On a pure tensor, `toPieceₗ` sends `a ⊗ x` to `a · (x|_{f(W)})`. -/
@[simp]
theorem toPieceₗ_tmul (W : (Spec Γ(X, V)).Opens) (a : Γ(Spec Γ(X, V), W))
    (x : gradedPiece (R := Γ(X, V)) Γ(E, V) n) :
    letI := specPieceModule E hV n W
    toPieceₗ E hV n W (a ⊗ₜ[Γ(X, V)] x) =
      (hV.fromSpec.appIso W).inv a •
        (gradedRestrictₗ E (fromSpec_image_le hV W) n
          (letI := gradedModuleOfLE E (fromSpec_image_le hV W) n; x)) := rfl

/-! ### Naturality -/

/-- A restriction map of the restricted sectionwise symmetric power, as an additive map whose
source and target are written as graded pieces rather than as restrictions of scalars. -/
def pieceRestrictAdd {W W' : (Spec Γ(X, V)).Opens} (j : W' ⟶ W) :
    gradedPiece (R := Γ(X, hV.fromSpec ''ᵁ W)) Γ(E, hV.fromSpec ''ᵁ W) n →+
      gradedPiece (R := Γ(X, hV.fromSpec ''ᵁ W')) Γ(E, hV.fromSpec ''ᵁ W') n :=
  AddMonoidHom.mk'
    (fun y => (siteGradedPiece E.val n).map (hV.fromSpec.opensFunctor.map j).op y)
    fun y z => map_add ((siteGradedPiece E.val n).map
      (hV.fromSpec.opensFunctor.map j).op).hom y z

/-- The restriction maps of the restricted sectionwise symmetric power are semilinear over the
restriction maps of `𝒪_X`. -/
theorem pieceRestrictAdd_smul {W W' : (Spec Γ(X, V)).Opens} (j : W' ⟶ W)
    (r : Γ(X, hV.fromSpec ''ᵁ W))
    (z : gradedPiece (R := Γ(X, hV.fromSpec ''ᵁ W)) Γ(E, hV.fromSpec ''ᵁ W) n) :
    pieceRestrictAdd E hV n j (r • z) =
      X.presheaf.map (hV.fromSpec.opensFunctor.map j).op r • pieceRestrictAdd E hV n j z :=
  (siteGradedPiece E.val n).map_smul (hV.fromSpec.opensFunctor.map j).op r z

/-- Restricting from `V` to the image of `W` and then to the image of `W'` is restricting from
`V` to the image of `W'`. -/
theorem pieceRestrictAdd_gradedRestrictₗ {W W' : (Spec Γ(X, V)).Opens} (j : W' ⟶ W)
    (y : gradedPiece (R := Γ(X, V)) Γ(E, V) n) :
    pieceRestrictAdd E hV n j
        (letI := gradedModuleOfLE E (fromSpec_image_le hV W) n
         gradedRestrictₗ E (fromSpec_image_le hV W) n y) =
      (letI := gradedModuleOfLE E (fromSpec_image_le hV W') n
       gradedRestrictₗ E (fromSpec_image_le hV W') n y) :=
  ((siteGradedPiece E.val n).map_comp_apply (homOfLE (fromSpec_image_le hV W)).op
    (hV.fromSpec.opensFunctor.map j).op y).symm

/-- **The comparison of structure sheaves is natural**, in applied form. -/
theorem appIso_inv_restrict {W W' : (Spec Γ(X, V)).Opens} (j : W' ⟶ W)
    (a : Γ(Spec Γ(X, V), W)) :
    (hV.fromSpec.appIso W').inv (AffineBaseChange.specRestrictₗ (R := Γ(X, V)) j a) =
      X.presheaf.map (hV.fromSpec.opensFunctor.map j).op ((hV.fromSpec.appIso W).inv a) :=
  congr($(Scheme.Hom.appIso_inv_naturality hV.fromSpec j.op).hom a)

/-- **The comparison is natural on a pure tensor.** -/
theorem pieceRestrictAdd_toPieceₗ_tmul {W W' : (Spec Γ(X, V)).Opens} (j : W' ⟶ W)
    (a : Γ(Spec Γ(X, V), W)) (y : gradedPiece (R := Γ(X, V)) Γ(E, V) n) :
    pieceRestrictAdd E hV n j (toPieceₗ E hV n W (a ⊗ₜ[Γ(X, V)] y)) =
      toPieceₗ E hV n W'
        ((AffineBaseChange.specRestrictₗ (R := Γ(X, V)) j a) ⊗ₜ[Γ(X, V)] y) :=
  (pieceRestrictAdd_smul E hV n j ((hV.fromSpec.appIso W).inv a)
      (let := gradedModuleOfLE E (fromSpec_image_le hV W) n
       gradedRestrictₗ E (fromSpec_image_le hV W) n y)).trans
    ((congrArg
        (fun z : gradedPiece (R := Γ(X, hV.fromSpec ''ᵁ W')) Γ(E, hV.fromSpec ''ᵁ W') n =>
          X.presheaf.map (hV.fromSpec.opensFunctor.map j).op
            ((hV.fromSpec.appIso W).inv a) • z)
        (pieceRestrictAdd_gradedRestrictₗ E hV n j y)).trans
      (congrArg
        (fun r : Γ(X, hV.fromSpec ''ᵁ W') => r •
          (let := gradedModuleOfLE E (fromSpec_image_le hV W') n
           gradedRestrictₗ E (fromSpec_image_le hV W') n y))
        (appIso_inv_restrict hV j a).symm))

/-- **The comparison is natural.** -/
theorem toPieceₗ_naturality {W W' : (Spec Γ(X, V)).Opens} (j : W' ⟶ W)
    (x : Γ(Spec Γ(X, V), W) ⊗[Γ(X, V)] gradedPiece (R := Γ(X, V)) Γ(E, V) n) :
    pieceRestrictAdd E hV n j (toPieceₗ E hV n W x) =
      toPieceₗ E hV n W'
        (LinearMap.rTensor _ (AffineBaseChange.specRestrictₗ (R := Γ(X, V)) j) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a y => exact pieceRestrictAdd_toPieceₗ_tmul E hV n j a y
  | add y z hy hz => simp only [map_add, hy, hz]

/-- Naturality in the form a local-injectivity argument consumes, with the restriction map of the
base-change presheaf on the left. -/
theorem toPieceₗ_naturality' {W W' : (Spec Γ(X, V)).Opens} (j : W' ⟶ W)
    (x : (AffineBaseChange.presheaf (pieceAt E V n)).obj (op W)) :
    toPieceₗ E hV n W' ((AffineBaseChange.presheaf (pieceAt E V n)).map j.op x) =
      pieceRestrictAdd E hV n j (toPieceₗ E hV n W x) :=
  (toPieceₗ_naturality E hV n j x).symm

/-! ### Bijectivity on the basic opens -/

/-- The image under `fromSpec` of a basic open of `Spec Γ(X, V)` is an affine open of `X`: it is
`X.basicOpen g`. -/
theorem isAffineOpen_image_basicOpen (g : Γ(X, V)) :
    IsAffineOpen (hV.fromSpec ''ᵁ AffineBaseChange.specBasicOpen g) := by
  rw [show hV.fromSpec ''ᵁ AffineBaseChange.specBasicOpen g = X.basicOpen g from
    hV.fromSpec_image_basicOpen g]
  exact hV.basicOpen g

/-- **The comparison is bijective on a basic open.** Over `D(g)` both
`Γ(X, fromSpec ''ᵁ D(g))` and `Γ(Spec Γ(X, V), D(g))` are the localization of `Γ(X, V)` away
from `g`, so the base-change statement
`Stacks.SymGraded.isBaseChange_gradedRestrictₗ_int` for the first is the bijectivity of the
comparison for the second. -/
theorem bijective_toPieceₗ_basicOpen [E.IsQuasicoherent] (g : Γ(X, V)) :
    Function.Bijective (toPieceₗ E hV n (AffineBaseChange.specBasicOpen g)) := by
  let := algebraOfLE X (fromSpec_image_le hV (AffineBaseChange.specBasicOpen g))
  let := gradedModuleOfLE E (fromSpec_image_le hV (AffineBaseChange.specBasicOpen g)) n
  let := gradedIsScalarTowerOfLE E (fromSpec_image_le hV (AffineBaseChange.specBasicOpen g)) n
  let := specPieceModule E hV n (AffineBaseChange.specBasicOpen g)
  let := pieceIsScalarTower E hV n (AffineBaseChange.specBasicOpen g)
  have : IsLocalization.Away g Γ(X, hV.fromSpec ''ᵁ AffineBaseChange.specBasicOpen g) :=
    hV.isLocalization_of_eq_basicOpen (f := g)
      (homOfLE (fromSpec_image_le hV (AffineBaseChange.specBasicOpen g)))
      (hV.fromSpec_image_basicOpen g)
  have hbc : IsBaseChange Γ(X, hV.fromSpec ''ᵁ AffineBaseChange.specBasicOpen g)
      (gradedRestrictₗ E (fromSpec_image_le hV (AffineBaseChange.specBasicOpen g)) n) :=
    isBaseChange_gradedRestrictₗ_int E (isAffineOpen_image_basicOpen hV g) hV
      (fromSpec_image_le hV (AffineBaseChange.specBasicOpen g)) n
  have hlm : IsLocalizedModule (Submonoid.powers g)
      (gradedRestrictₗ E (fromSpec_image_le hV (AffineBaseChange.specBasicOpen g)) n) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers g)
      Γ(X, hV.fromSpec ''ᵁ AffineBaseChange.specBasicOpen g) _).2 hbc
  have hbc2 : IsBaseChange Γ(Spec Γ(X, V), AffineBaseChange.specBasicOpen g)
      (gradedRestrictₗ E (fromSpec_image_le hV (AffineBaseChange.specBasicOpen g)) n) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers g)
      Γ(Spec Γ(X, V), AffineBaseChange.specBasicOpen g) _).1 hlm
  have heq : (hbc2.equiv :
      Γ(Spec Γ(X, V), AffineBaseChange.specBasicOpen g) ⊗[Γ(X, V)]
        gradedPiece (R := Γ(X, V)) Γ(E, V) n →ₗ[_] _) =
      toPieceₗ E hV n (AffineBaseChange.specBasicOpen g) := by
    refine TensorProduct.AlgebraTensorModule.curry_injective ?_
    refine LinearMap.ext fun a => LinearMap.ext fun y => ?_
    exact hbc2.equiv_tmul a y
  rw [← heq]
  exact hbc2.equiv.bijective

/-! ### The comparison morphism and its local bijectivity -/

/-- The comparison as a morphism of presheaves of abelian groups. -/
def toPieceAb : (AffineBaseChange.presheaf (pieceAt E V n)).presheaf ⟶
    ((presheafRestrict hV.fromSpec).obj (siteGradedPiece E.val n)).presheaf where
  app W := AddCommGrpCat.ofHom (toPieceₗ E hV n W.unop).toAddMonoidHom
  naturality := fun {_ _} i => AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x =>
    (toPieceₗ_naturality E hV n i.unop x).symm)

/-- **The comparison morphism**: the base-change presheaf of `Sym^n_{Γ(X, V)}(Γ(E, V))` maps to
the restriction along `fromSpec` of the sectionwise degree-`n` symmetric power of `E`. -/
def toPiece : AffineBaseChange.presheaf (pieceAt E V n) ⟶
    (presheafRestrict hV.fromSpec).obj (siteGradedPiece E.val n) :=
  PresheafOfModules.homMk (toPieceAb E hV n) fun W r x =>
    letI := specPieceModule E hV n W.unop
    (toPieceₗ E hV n W.unop).map_smul r x

/-- The component of `toPiece` at `W` is `toPieceₗ` at `W`. -/
theorem toPiece_app (W : ((Spec Γ(X, V)).Opens)ᵒᵖ)
    (x : Γ(Spec Γ(X, V), W.unop) ⊗[Γ(X, V)] gradedPiece (R := Γ(X, V)) Γ(E, V) n) :
    PresheafOfModules.Hom.app (toPiece E hV n) W x = toPieceₗ E hV n W.unop x := rfl

/-- **The comparison is locally surjective**: the basic opens are a basis of `Spec Γ(X, V)`. -/
theorem isLocallySurjective_toPiece [E.IsQuasicoherent] :
    PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology ↥(Spec Γ(X, V)))
      (toPiece E hV n) := by
  constructor
  intro U s
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  obtain ⟨g, hxg, hgU⟩ := AffineBaseChange.exists_basicOpen_le (U := U) hx
  refine ⟨AffineBaseChange.specBasicOpen g, homOfLE hgU, ?_, hxg⟩
  obtain ⟨t, ht⟩ := (bijective_toPieceₗ_basicOpen E hV n g).2
    (((presheafRestrict hV.fromSpec).obj (siteGradedPiece E.val n)).map (homOfLE hgU).op s)
  exact ⟨t, ht⟩

/-- **The comparison is locally injective.** -/
theorem isLocallyInjective_toPiece [E.IsQuasicoherent] :
    PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology ↥(Spec Γ(X, V)))
      (toPiece E hV n) := by
  constructor
  intro U a b hab
  have hab' : toPieceₗ E hV n U.unop a = toPieceₗ E hV n U.unop b := hab
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  obtain ⟨g, hxg, hgU⟩ := AffineBaseChange.exists_basicOpen_le (U := U.unop) hx
  refine ⟨AffineBaseChange.specBasicOpen g, homOfLE hgU, ?_, hxg⟩
  have key : toPieceₗ E hV n (AffineBaseChange.specBasicOpen g)
        ((AffineBaseChange.presheaf (pieceAt E V n)).map (homOfLE hgU).op a) =
      toPieceₗ E hV n (AffineBaseChange.specBasicOpen g)
        ((AffineBaseChange.presheaf (pieceAt E V n)).map (homOfLE hgU).op b) :=
    (toPieceₗ_naturality' E hV n (homOfLE hgU) a).trans
      ((congrArg (pieceRestrictAdd E hV n (homOfLE hgU)) hab').trans
        (toPieceₗ_naturality' E hV n (homOfLE hgU) b).symm)
  exact (bijective_toPieceₗ_basicOpen E hV n g).1 key

/-! ### Quasi-coherence -/

/-- **The sheafification of the restriction to `Spec Γ(X, V)` of the sectionwise degree-`n`
symmetric power of `E` is the associated sheaf of `Sym^n_{Γ(X, V)}(Γ(E, V))`.** This is the third
assertion of Tag 01CG over an affine base. -/
def sheafificationIsoTilde [E.IsQuasicoherent] :
    (PresheafOfModules.sheafification (𝟙 (Spec Γ(X, V)).ringCatSheaf.obj)).obj
        ((presheafRestrict hV.fromSpec).obj (siteGradedPiece E.val n)) ≅
      tilde (pieceAt E V n) :=
  haveI := isLocallyInjective_toPiece E hV n
  haveI := isLocallySurjective_toPiece E hV n
  haveI := Stacks.PresheafOfModules.isIso_sheafification_map_of_isLocallyBijective
    (𝟙 (Spec Γ(X, V)).ringCatSheaf.obj) (toPiece E hV n)
  (asIso ((PresheafOfModules.sheafification
      (𝟙 (Spec Γ(X, V)).ringCatSheaf.obj)).map (toPiece E hV n))).symm ≪≫
    Stacks.PresheafOfModules.sheafificationIsoOfIsLocallyBijective
      (𝟙 (Spec Γ(X, V)).ringCatSheaf.obj) (tilde (pieceAt E V n))
      (AffineBaseChange.toTilde (pieceAt E V n))
      (AffineBaseChange.isLocallyInjective_toTilde (pieceAt E V n))
      (AffineBaseChange.isLocallySurjective_toTilde (pieceAt E V n))

/-- **The restriction to `Spec Γ(X, V)` of the degree-`n` piece of `Sym(E)` is
quasi-coherent**: it is an associated sheaf. -/
theorem isQuasicoherent_restrict_fromSpec_piece [E.IsQuasicoherent] :
    ((Scheme.Modules.restrictFunctor hV.fromSpec).obj
      ((Scheme.Modules.symmetricAlgebra X E).piece n)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec Γ(X, V)).ringCatSheaf).prop_of_iso
    ((sheafificationIsoTilde E hV n).symm ≪≫
      restrictSheafificationIso hV.fromSpec (siteGradedPiece E.val n)) inferInstance

end Stacks.SymGraded.AffinePieces

namespace Stacks.SymGraded

universe u

/-- **Every homogeneous piece of `Sym(E)` is quasi-coherent, for `E` a quasi-coherent module on
an arbitrary scheme.** This discharges the hypothesis
`Stacks.SymGraded.IsQuasicoherentPieces` of `Stacks.SymGraded.schemeSheafGradedAlgebra` and of
`Stacks.SymGraded.schemeProjectiveBundle` for a quasi-coherent module. -/
@[stacks 01CK "symmetric powers of a quasi-coherent module, at the encoding \
Stacks.SymGraded.schemeSymAlgebra"]
theorem isQuasicoherentPieces_of_isQuasicoherent {X : Scheme.{u}} (E : X.Modules)
    [E.IsQuasicoherent] : IsQuasicoherentPieces E :=
  isQuasicoherentPieces_of_restrict_affineOpens E fun n U =>
    Stacks.AlgebraicGeometry.ImmersionRestrict.isQuasicoherent_restrict_ι_of_fromSpec U.2 _
      (AffinePieces.isQuasicoherent_restrict_fromSpec_piece E U.2 n)

end Stacks.SymGraded

end
