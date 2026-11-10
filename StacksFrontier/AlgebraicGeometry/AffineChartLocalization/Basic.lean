module

public import StacksFrontier.AlgebraicGeometry.SymAlgebraQcohPieces.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationUnitSections

/-!
# A presheaf of modules that localizes on basic opens has sheaf sections over an affine chart

Let `X` be a scheme and `P` a presheaf of `𝒪_X`-modules. Over a general open the sheafification
unit `P(U) ⟶ Γ(U, P^#)` is neither injective nor surjective: a section of the sheafification is
only *locally* a section of `P`. **Over an affine open `V` it is bijective as soon as `P`
localizes on the basic opens of `V`**, i.e. as soon as for every `g : Γ(X, V)` the restriction
map `P(V) → P(X.basicOpen g)` exhibits its target as the localization of `P(V)` away from `g`.

That hypothesis is exactly what the quasi-coherence of a *sheaf* buys on an affine chart
(`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ`), and it is
available for many presheaves that are not sheaves: the sectionwise symmetric powers of a
quasi-coherent module, the presheaf of divided power differentials, and so on. Each such
consumer previously re-ran the whole chart argument; this file runs it once.

## The argument

The affine model of `V` is `Spec Γ(X, V)`, reached by `AlgebraicGeometry.IsAffineOpen.fromSpec`,
and over it the proof is a comparison of two presheaves of `𝒪_{Spec Γ(X, V)}`-modules:

* the base-change presheaf `W ↦ Γ(Spec Γ(X, V), W) ⊗_{Γ(X, V)} P(V)` of
  `Stacks.AffineBaseChange.presheaf`, whose sheafification is the associated sheaf `P(V)~`
  because `Stacks.AffineBaseChange.toTilde` is locally bijective;
* the restriction along `fromSpec` of `P` itself, whose sheafification unit over the whole of
  `Spec Γ(X, V)` is the unit of `P` over `V`, because `fromSpec` is an open immersion with image
  `V` and restriction along an open immersion preserves local bijectivity.

`toSections` is the comparison between them, `a ⊗ x ↦ a · (x|_{f(W)})`, and the localization
hypothesis says exactly that it is bijective over every basic open `D(g)`. Sheafification
inverts a locally bijective morphism, so the two units are bijective together, and the unit of
the base-change presheaf over `⊤ = D(1)` is bijective because `toTilde` is.

## Main definitions

* `sectionsModule`: the `Γ(X, U)`-module structure on `P(U)`, which instance search does not
  find for an arbitrary presheaf of modules — see the implementation notes.
* `presheafModuleOfLE` and `presheafRestrictₗ`: the `Γ(X, W)`-module structure on `P(U)` for
  `U ≤ W`, and the restriction map `P(W) → P(U)` as a `Γ(X, W)`-linear map. These are what the
  localization hypothesis is stated about.
* `sectionsAt`: the sections of `P` over `V`, as a `Γ(X, V)`-module.
* `toSectionsₗ`: **the comparison on sections**, `a ⊗ x ↦ a · (x|_{f(W)})`, as a linear map over
  `Γ(Spec Γ(X, V), W)`.
* `toSections`: **the comparison morphism** of presheaves of `𝒪_{Spec Γ(X, V)}`-modules.

## Main results

* `bijective_toSectionsₗ_basicOpen`: **the comparison is bijective on a basic open**, and
  `isLocallySurjective_toSections`, `isLocallyInjective_toSections`: it is therefore locally
  bijective.
* `bijective_sheafifyUnit_app_of_isAffineOpen`: **the sheafification unit of `P` is bijective on
  the sections over `V`.** This is the target.
* `bijective_toSheafify_app_of_isAffineOpen`: the same statement read on the underlying presheaf
  of abelian groups, where the unit is `CategoryTheory.toSheafify`. The two maps are the same.

## Implementation notes

**This is `Stacks.SymGraded.bijective_sheafifyUnit_app_of_isAffineOpen` with the symmetric powers
removed.** That theorem is the case `P = Stacks.SymGraded.siteGradedPiece E.val n` for `E`
quasi-coherent, where the localization hypothesis is
`Stacks.SymGraded.isBaseChange_gradedRestrictₗ_int`; the construction below is
`StacksFrontier/AlgebraicGeometry/SymAlgebraQcohPieces/Basic.lean` followed by
`StacksFrontier/AlgebraicGeometry/SheafSymmetricAlgebra/AffineChartSections.lean` with
`Sym^n_{Γ(X, V)}(Γ(E, V))` replaced by `P(V)`. It is shorter: with no graded pieces the module
structures are two deep rather than three, so the naturality chain that had to be written in
term mode there is an ordinary `rw` here.

**The one bridge the generic statement needs.** For a presheaf of modules built by hand the
sections over `U` are usually a `ModuleCat.of Γ(X, U) _`, and `Module Γ(X, U) ↥(P.obj (op U))`
is then found by instance search; for an arbitrary `P` the module structure is over
`X.ringCatSheaf.obj.obj (op U)`, the same ring as a `RingCat`, and the two spellings agree at
default transparency but not at instance transparency. `sectionsModule` is that bridge, and it
is a file-local instance rather than a global one so that it cannot form a diamond with the
instances a particular presheaf of modules carries. Nothing downstream needs it: the module
structures are already baked into the types of `presheafRestrictₗ` and `toSectionsₗ`.

**Why `fromSpec` and not the inclusion `V.ι`.** The hypothesis is about the basic opens of `X`
inside `V`, and the proof needs the basic opens of `Spec Γ(X, V)` as a basis on which to check
bijectivity. Restricting along `fromSpec` puts both in the same place: the sections of the
restricted presheaf over `W` are the sections of `P` over `fromSpec ''ᵁ W`, an open of `X`, and
`fromSpec ''ᵁ D(g) = X.basicOpen g`.

**The hypothesis needs no transport of opens.** It quantifies over an open `U` merely *equal* to
`X.basicOpen g`, in the shape of
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ`, so it applies to
`fromSpec ''ᵁ D(g)` directly and nothing has to be moved along an equality of opens. This is
also why bijectivity on `D(g)` is routed through `IsLocalizedModule` rather than through a ring
isomorphism: `Γ(X, fromSpec ''ᵁ D(g))` never appears, and `Γ(Spec Γ(X, V), D(g))` is a
localization of `Γ(X, V)` away from `g` by instance search, so
`isLocalizedModule_iff_isBaseChange` turns the hypothesis into the `IsBaseChange` the comparison
is.

**Two lemmas are reused rather than restated.**
`Stacks.SymGraded.AffinePieces.appIso_inv_algebraMap` and `appIso_inv_restrict` are already
stated with no reference to symmetric powers — they say that the comparison of structure sheaves
along `fromSpec` carries the structure map of `Γ(Spec Γ(X, V), W)` to a restriction map of
`𝒪_X`, and that it is natural — so they are imported from the symmetric-power file rather than
proved a second time here. When that file is rewritten against this one they should move here.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 00WY](https://stacks.math.columbia.edu/tag/00WY)

## Not done here

**No tag is claimed.** Tag 01I8 is the equivalence between modules over a ring and
quasi-coherent sheaves on its spectrum, and nothing here asserts it; what is used from that
circle of ideas is Mathlib's `AlgebraicGeometry.tilde` and the local bijectivity of
`Stacks.AffineBaseChange.toTilde`. Tag 01CG is a statement about the symmetric powers of a
module on a ringed space, and this file has no symmetric powers in it at all.

Nothing here is said about the functoriality of the identification in `P`: a morphism
`P ⟶ Q` of presheaves of modules, both localizing on the basic opens of `V`, induces a square
relating the two units, and that square is not proved.

Nothing here is said about two nested affine opens: the compatibility of the identification over
`V` with the one over an affine open `V' ≤ V` is not proved, and neither is the resulting
statement that the sheafification of `P` is determined on an affine cover by the localization
data.

Nothing here says the hypothesis is *necessary*, nor that it holds for any particular `P`; the
instances of it in this repository are
`Stacks.SymGraded.isBaseChange_gradedRestrictₗ_int` and
`Crystalline.isLocalizedModule_presheafRestrictₗ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open PresheafOfModules
open Stacks.AlgebraicGeometry.ImmersionRestrict
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange
open Stacks.SymGraded.AffinePieces (appIso_inv_algebraMap appIso_inv_restrict)
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.AffineChartLocalization

universe u

variable {X : Scheme.{u}} (P : PresheafOfModules.{u} X.ringCatSheaf.obj)

/-! ### Restriction of sections as a linear map -/

/-- The `Γ(X, U)`-module structure on the sections of `P` over `U`.

Instance search does not find it: `P.obj (op U)` is a module over `X.ringCatSheaf.obj.obj (op U)`,
which is the ring `Γ(X, U)` written as a `RingCat` rather than as a `CommRingCat`. The two agree
at default transparency but not at instance transparency, exactly as recorded for the monoidal
structure in `Stacks.InternalHom.schemeMonoidalCategory`; a presheaf of modules whose sections
are *built* with `ModuleCat.of Γ(X, U) _` does not need the bridge, which is why a construction
carried out for one such presheaf never meets this. -/
@[instance_reducible]
def sectionsModule (U : X.Opens) : Module Γ(X, U) ↥(P.obj (op U)) := (P.obj (op U)).isModule

attribute [local instance] sectionsModule

/-- The `Γ(X, W)`-module structure on the sections of `P` over a smaller open `U ≤ W`, obtained
by restricting scalars along the restriction map of `𝒪_X`. -/
@[instance_reducible]
def presheafModuleOfLE {U W : X.Opens} (h : U ≤ W) : Module Γ(X, W) ↥(P.obj (op U)) :=
  Module.compHom _ (X.presheaf.map (homOfLE h).op).hom

/-- A restriction map of `P`, as a linear map over the sections of `𝒪_X` on the larger open. -/
def presheafRestrictₗ {U W : X.Opens} (h : U ≤ W) :
    letI := presheafModuleOfLE P h
    ↥(P.obj (op W)) →ₗ[Γ(X, W)] ↥(P.obj (op U)) :=
  letI := presheafModuleOfLE P h
  { toFun := P.map (homOfLE h).op
    map_add' := map_add _
    map_smul' := fun r x ↦ P.map_smul (homOfLE h).op r x }

variable {V : X.Opens} (hV : IsAffineOpen V)

/-- The sections of `P` over `V`, as a `Γ(X, V)`-module. -/
abbrev sectionsAt (P : PresheafOfModules.{u} X.ringCatSheaf.obj) (V : X.Opens) :
    ModuleCat.{u} Γ(X, V) :=
  ModuleCat.of Γ(X, V) ↥(P.obj (op V))

/-! ### The comparison on sections -/

/-- The `Γ(Spec Γ(X, V), W)`-module structure on the sections of `P` over the image of `W`,
obtained by restricting scalars along the comparison of structure sheaves. It is the structure
the restricted presheaf of modules carries. -/
@[instance_reducible]
def specSectionsModule (W : (Spec Γ(X, V)).Opens) :
    Module Γ(Spec Γ(X, V), W) ↥(P.obj (op (hV.fromSpec ''ᵁ W))) :=
  Module.compHom _ (hV.fromSpec.appIso W).inv.hom

/-- The scalar tower `Γ(X, V) → Γ(Spec Γ(X, V), W) → P(f(W))`. -/
theorem sectionsIsScalarTower (P : PresheafOfModules.{u} X.ringCatSheaf.obj) (hV : IsAffineOpen V)
    (W : (Spec Γ(X, V)).Opens) :
    letI := presheafModuleOfLE P (fromSpec_image_le hV W)
    letI := specSectionsModule P hV W
    IsScalarTower Γ(X, V) Γ(Spec Γ(X, V), W) ↥(P.obj (op (hV.fromSpec ''ᵁ W))) :=
  let := presheafModuleOfLE P (fromSpec_image_le hV W)
  let := specSectionsModule P hV W
  IsScalarTower.of_algebraMap_smul fun r x =>
    congrArg (fun s : Γ(X, hV.fromSpec ''ᵁ W) => s • x) (appIso_inv_algebraMap hV W r)

/-- **The comparison on sections**: the base change of `P(V)` to `Γ(Spec Γ(X, V), W)` maps to
`P(f(W))` by `a ⊗ x ↦ a · (x|_{f(W)})`. -/
def toSectionsₗ (W : (Spec Γ(X, V)).Opens) :
    letI := specSectionsModule P hV W
    Γ(Spec Γ(X, V), W) ⊗[Γ(X, V)] ↥(P.obj (op V)) →ₗ[Γ(Spec Γ(X, V), W)]
      ↥(P.obj (op (hV.fromSpec ''ᵁ W))) :=
  letI := presheafModuleOfLE P (fromSpec_image_le hV W)
  letI := specSectionsModule P hV W
  letI := sectionsIsScalarTower P hV W
  (presheafRestrictₗ P (fromSpec_image_le hV W)).liftBaseChange Γ(Spec Γ(X, V), W)

/-- The comparison on sections sends `a ⊗ x` to `a · (x|_{f(W)})`. -/
@[simp]
theorem toSectionsₗ_tmul (W : (Spec Γ(X, V)).Opens) (a : Γ(Spec Γ(X, V), W))
    (x : ↥(P.obj (op V))) :
    letI := specSectionsModule P hV W
    toSectionsₗ P hV W (a ⊗ₜ[Γ(X, V)] x) =
      (hV.fromSpec.appIso W).inv a •
        (presheafRestrictₗ P (fromSpec_image_le hV W)
          (letI := presheafModuleOfLE P (fromSpec_image_le hV W); x)) := rfl

/-! ### Naturality -/

/-- A restriction map of the restricted presheaf, as an additive map whose source and target are
written as modules of sections rather than as restrictions of scalars. -/
def sectionsRestrictAdd {W W' : (Spec Γ(X, V)).Opens} (j : W' ⟶ W) :
    ↥(P.obj (op (hV.fromSpec ''ᵁ W))) →+ ↥(P.obj (op (hV.fromSpec ''ᵁ W'))) :=
  AddMonoidHom.mk' (fun y => P.map (hV.fromSpec.opensFunctor.map j).op y)
    fun y z => map_add (P.map (hV.fromSpec.opensFunctor.map j).op).hom y z

/-- The restriction maps of `P` are semilinear over the restriction maps of `𝒪_X`. -/
theorem sectionsRestrictAdd_smul {W W' : (Spec Γ(X, V)).Opens} (j : W' ⟶ W)
    (r : Γ(X, hV.fromSpec ''ᵁ W)) (z : ↥(P.obj (op (hV.fromSpec ''ᵁ W)))) :
    sectionsRestrictAdd P hV j (r • z) =
      X.presheaf.map (hV.fromSpec.opensFunctor.map j).op r • sectionsRestrictAdd P hV j z :=
  P.map_smul (hV.fromSpec.opensFunctor.map j).op r z

/-- Restricting from `V` to the image of `W` and then to the image of `W'` is restricting from
`V` to the image of `W'`. -/
theorem sectionsRestrictAdd_presheafRestrictₗ {W W' : (Spec Γ(X, V)).Opens} (j : W' ⟶ W)
    (y : ↥(P.obj (op V))) :
    sectionsRestrictAdd P hV j
        (letI := presheafModuleOfLE P (fromSpec_image_le hV W)
         presheafRestrictₗ P (fromSpec_image_le hV W) y) =
      (letI := presheafModuleOfLE P (fromSpec_image_le hV W')
       presheafRestrictₗ P (fromSpec_image_le hV W') y) :=
  (P.map_comp_apply (homOfLE (fromSpec_image_le hV W)).op
    (hV.fromSpec.opensFunctor.map j).op y).symm

/-- **The comparison is natural on a pure tensor.** -/
theorem sectionsRestrictAdd_toSectionsₗ_tmul {W W' : (Spec Γ(X, V)).Opens} (j : W' ⟶ W)
    (a : Γ(Spec Γ(X, V), W)) (y : ↥(P.obj (op V))) :
    sectionsRestrictAdd P hV j (toSectionsₗ P hV W (a ⊗ₜ[Γ(X, V)] y)) =
      toSectionsₗ P hV W'
        ((AffineBaseChange.specRestrictₗ (R := Γ(X, V)) j a) ⊗ₜ[Γ(X, V)] y) := by
  rw [toSectionsₗ_tmul, toSectionsₗ_tmul, sectionsRestrictAdd_smul,
    sectionsRestrictAdd_presheafRestrictₗ, ← appIso_inv_restrict hV j a]

/-- **The comparison is natural.** -/
theorem toSectionsₗ_naturality {W W' : (Spec Γ(X, V)).Opens} (j : W' ⟶ W)
    (x : Γ(Spec Γ(X, V), W) ⊗[Γ(X, V)] ↥(P.obj (op V))) :
    sectionsRestrictAdd P hV j (toSectionsₗ P hV W x) =
      toSectionsₗ P hV W'
        (LinearMap.rTensor _ (AffineBaseChange.specRestrictₗ (R := Γ(X, V)) j) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a y => exact sectionsRestrictAdd_toSectionsₗ_tmul P hV j a y
  | add y z hy hz => simp only [map_add, hy, hz]

/-- Naturality in the form a local-injectivity argument consumes, with the restriction map of the
base-change presheaf on the left. -/
theorem toSectionsₗ_naturality' {W W' : (Spec Γ(X, V)).Opens} (j : W' ⟶ W)
    (x : (AffineBaseChange.presheaf (sectionsAt P V)).obj (op W)) :
    toSectionsₗ P hV W' ((AffineBaseChange.presheaf (sectionsAt P V)).map j.op x) =
      sectionsRestrictAdd P hV j (toSectionsₗ P hV W x) :=
  (toSectionsₗ_naturality P hV j x).symm

/-! ### Bijectivity on the basic opens -/

variable (hloc : ∀ (g : Γ(X, V)) {U : X.Opens} (_ : U = X.basicOpen g) (hUV : U ≤ V),
  letI := presheafModuleOfLE P hUV
  IsLocalizedModule.Away g (presheafRestrictₗ P hUV))

include hV hloc in
/-- **The comparison is bijective on a basic open.** The image of `D(g)` under `fromSpec` is
`X.basicOpen g`, so the hypothesis says that the sections of `P` there are the localization of
`P(V)` away from `g`; and `Γ(Spec Γ(X, V), D(g))` is the localization of `Γ(X, V)` away from
`g`, so that localization statement *is* the bijectivity of the comparison. -/
theorem bijective_toSectionsₗ_basicOpen (g : Γ(X, V)) :
    Function.Bijective (toSectionsₗ P hV (AffineBaseChange.specBasicOpen g)) := by
  let := presheafModuleOfLE P (fromSpec_image_le hV (AffineBaseChange.specBasicOpen g))
  let := specSectionsModule P hV (AffineBaseChange.specBasicOpen g)
  let := sectionsIsScalarTower P hV (AffineBaseChange.specBasicOpen g)
  have hlm : IsLocalizedModule (Submonoid.powers g)
      (presheafRestrictₗ P (fromSpec_image_le hV (AffineBaseChange.specBasicOpen g))) :=
    hloc g (hV.fromSpec_image_basicOpen g)
      (fromSpec_image_le hV (AffineBaseChange.specBasicOpen g))
  have hbc : IsBaseChange Γ(Spec Γ(X, V), AffineBaseChange.specBasicOpen g)
      (presheafRestrictₗ P (fromSpec_image_le hV (AffineBaseChange.specBasicOpen g))) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers g)
      Γ(Spec Γ(X, V), AffineBaseChange.specBasicOpen g) _).1 hlm
  have heq : (hbc.equiv :
      Γ(Spec Γ(X, V), AffineBaseChange.specBasicOpen g) ⊗[Γ(X, V)] ↥(P.obj (op V)) →ₗ[_] _) =
      toSectionsₗ P hV (AffineBaseChange.specBasicOpen g) :=
    TensorProduct.AlgebraTensorModule.curry_injective <|
      LinearMap.ext fun a => LinearMap.ext fun y => hbc.equiv_tmul a y
  rw [← heq]
  exact hbc.equiv.bijective

/-! ### The comparison morphism and its local bijectivity -/

/-- A sieve on an open of `Spec R` that contains every basic open inside it is covering. -/
private theorem mem_grothendieckTopology_of_basicOpen {R : CommRingCat.{u}}
    {U : (Spec R).Opens} (S : Sieve U)
    (h : ∀ (g : R) (hgU : AffineBaseChange.specBasicOpen g ≤ U), S (homOfLE hgU)) :
    S ∈ Opens.grothendieckTopology ↥(Spec R) U := by
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  obtain ⟨g, hxg, hgU⟩ := AffineBaseChange.exists_basicOpen_le (U := U) hx
  exact ⟨AffineBaseChange.specBasicOpen g, homOfLE hgU, h g hgU, hxg⟩

/-- The comparison as a morphism of presheaves of abelian groups. -/
def toSectionsAb : (AffineBaseChange.presheaf (sectionsAt P V)).presheaf ⟶
    ((presheafRestrict hV.fromSpec).obj P).presheaf where
  app W := AddCommGrpCat.ofHom (toSectionsₗ P hV W.unop).toAddMonoidHom
  naturality := fun {_ _} i => AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x =>
    (toSectionsₗ_naturality P hV i.unop x).symm)

/-- **The comparison morphism**: the base-change presheaf of `P(V)` maps to the restriction of
`P` along `fromSpec`. -/
def toSections : AffineBaseChange.presheaf (sectionsAt P V) ⟶
    (presheafRestrict hV.fromSpec).obj P :=
  PresheafOfModules.homMk (toSectionsAb P hV) fun W r x =>
    letI := specSectionsModule P hV W.unop
    (toSectionsₗ P hV W.unop).map_smul r x

/-- On sections over `W`, the comparison morphism `toSections` is `toSectionsₗ`. -/
theorem toSections_app (W : ((Spec Γ(X, V)).Opens)ᵒᵖ)
    (x : Γ(Spec Γ(X, V), W.unop) ⊗[Γ(X, V)] ↥(P.obj (op V))) :
    PresheafOfModules.Hom.app (toSections P hV) W x = toSectionsₗ P hV W.unop x := rfl

include hloc in
/-- **The comparison is locally surjective**: the basic opens are a basis of `Spec Γ(X, V)`. -/
theorem isLocallySurjective_toSections :
    PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology ↥(Spec Γ(X, V)))
      (toSections P hV) := by
  constructor
  intro U s
  refine mem_grothendieckTopology_of_basicOpen _ fun g hgU => ?_
  exact (bijective_toSectionsₗ_basicOpen P hV hloc g).2
    (((presheafRestrict hV.fromSpec).obj P).map (homOfLE hgU).op s)

include hloc in
/-- **The comparison is locally injective.** -/
theorem isLocallyInjective_toSections :
    PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology ↥(Spec Γ(X, V)))
      (toSections P hV) := by
  constructor
  intro U a b hab
  have hab' : toSectionsₗ P hV U.unop a = toSectionsₗ P hV U.unop b := hab
  refine mem_grothendieckTopology_of_basicOpen _ fun g hgU => ?_
  exact (bijective_toSectionsₗ_basicOpen P hV hloc g).1 <|
    (toSectionsₗ_naturality' P hV (homOfLE hgU) a).trans
      ((congrArg (sectionsRestrictAdd P hV (homOfLE hgU)) hab').trans
        (toSectionsₗ_naturality' P hV (homOfLE hgU) b).symm)

/-! ### The sheafification unit over the affine chart -/

omit hV hloc in
/-- **The comparison with the associated sheaf is bijective on the global sections of
`Spec Γ(X, V)`**: `⊤` is the basic open of `1`. -/
theorem bijective_toTilde_app_top : Function.Bijective
    (Hom.app (AffineBaseChange.toTilde (sectionsAt P V))
      (op (⊤ : (Spec Γ(X, V)).Opens))) := by
  have h := AffineBaseChange.bijective_toTildeₗ_basicOpen (sectionsAt P V) (1 : Γ(X, V))
  rwa [show AffineBaseChange.specBasicOpen (1 : Γ(X, V)) =
    (⊤ : (Spec Γ(X, V)).Opens) from PrimeSpectrum.basicOpen_one] at h

include hV hloc in
/-- **The comparison of the base-change presheaf with `P` is bijective on the global sections of
`Spec Γ(X, V)`.** -/
theorem bijective_toSections_app_top : Function.Bijective
    (Hom.app (toSections P hV) (op (⊤ : (Spec Γ(X, V)).Opens))) := by
  have h := bijective_toSectionsₗ_basicOpen P hV hloc (1 : Γ(X, V))
  rwa [show AffineBaseChange.specBasicOpen (1 : Γ(X, V)) =
    (⊤ : (Spec Γ(X, V)).Opens) from PrimeSpectrum.basicOpen_one] at h

omit hV hloc in
/-- **The sheafification unit of the base-change presheaf is bijective on the global sections of
`Spec Γ(X, V)`.** -/
theorem bijective_sheafifyUnit_app_baseChange_top :
    Function.Bijective (Hom.app (sheafifyUnit (𝟙 (Spec Γ(X, V)).ringCatSheaf.obj)
      (AffineBaseChange.presheaf (sectionsAt P V)))
      (op (⊤ : (Spec Γ(X, V)).Opens))) :=
  (Stacks.PresheafOfModules.bijective_sheafifyUnit_app_iff
    (𝟙 (Spec Γ(X, V)).ringCatSheaf.obj) (tilde (sectionsAt P V))
    (AffineBaseChange.toTilde (sectionsAt P V))
    (AffineBaseChange.isLocallyInjective_toTilde (sectionsAt P V))
    (AffineBaseChange.isLocallySurjective_toTilde (sectionsAt P V))
    (op (⊤ : (Spec Γ(X, V)).Opens))).2 (bijective_toTilde_app_top P)

include hV hloc in
/-- **The sheafification unit of the restriction of `P` along `fromSpec` is bijective on the
global sections of `Spec Γ(X, V)`.** -/
theorem bijective_sheafifyUnit_app_restrict_top :
    Function.Bijective (Hom.app (sheafifyUnit (𝟙 (Spec Γ(X, V)).ringCatSheaf.obj)
      ((presheafRestrict hV.fromSpec).obj P))
      (op (⊤ : (Spec Γ(X, V)).Opens))) :=
  Stacks.PresheafOfModules.bijective_sheafifyUnit_app_of_isLocallyBijective
    (𝟙 (Spec Γ(X, V)).ringCatSheaf.obj) (toSections P hV)
    (isLocallyInjective_toSections P hV hloc) (isLocallySurjective_toSections P hV hloc)
    (op (⊤ : (Spec Γ(X, V)).Opens)) (bijective_sheafifyUnit_app_baseChange_top P)
    (bijective_toSections_app_top P hV hloc).2

include hV hloc in
/-- **The sheafification unit of a presheaf of modules that localizes on the basic opens of an
affine open `V` is bijective on the sections over `V`.**

So `Γ(V, P^#)` *is* `P(V)` there: a section of the sheafification over an affine chart is an
honest section of `P`, with no passage to a cover, and two sections of `P` over `V` with the
same image are equal. -/
theorem bijective_sheafifyUnit_app_of_isAffineOpen :
    Function.Bijective (PresheafOfModules.Hom.app
      (PresheafOfModules.sheafifyUnit (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj) P)
      (op V)) := by
  have h : Function.Bijective (Hom.app
      (sheafifyUnit (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj) P)
      (op (hV.fromSpec ''ᵁ (⊤ : (Spec Γ(X, V)).Opens)))) := by
    have _hi := Stacks.AlgebraicGeometry.SheafifyRestrict.isLocallyInjective_sheafifyUnit P
    have _hs := Stacks.AlgebraicGeometry.SheafifyRestrict.isLocallySurjective_sheafifyUnit P
    exact (Stacks.PresheafOfModules.bijective_sheafifyUnit_app_iff
      (𝟙 (Spec Γ(X, V)).ringCatSheaf.obj)
      ((Scheme.Modules.restrictFunctor hV.fromSpec).obj
        ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P))
      ((presheafRestrict hV.fromSpec).map
        (sheafifyUnit (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj) P))
      (isLocallyInjective_presheafRestrict_map hV.fromSpec
        (sheafifyUnit (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj) P))
      (isLocallySurjective_presheafRestrict_map hV.fromSpec
        (sheafifyUnit (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj) P))
      (op (⊤ : (Spec Γ(X, V)).Opens))).1 (bijective_sheafifyUnit_app_restrict_top P hV hloc)
  rwa [show hV.fromSpec ''ᵁ (⊤ : (Spec Γ(X, V)).Opens) = V from
    (Scheme.Hom.image_top_eq_opensRange hV.fromSpec).trans hV.opensRange_fromSpec] at h

include hV hloc in
/-- `bijective_sheafifyUnit_app_of_isAffineOpen` read on the underlying presheaf of abelian
groups, where the unit is `CategoryTheory.toSheafify`. The two maps are the same. -/
theorem bijective_toSheafify_app_of_isAffineOpen :
    Function.Bijective (ConcreteCategory.hom
      ((CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf).app (op V))) :=
  bijective_sheafifyUnit_app_of_isAffineOpen P hV hloc

end Stacks.AlgebraicGeometry.AffineChartLocalization

end
