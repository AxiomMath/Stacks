module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafDesc
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentAffineGermTensor
public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic
public import Mathlib.Algebra.Homology.Double
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The two complexes of Stacks 0D0I on an affine open, and the germ of the comparison

Let `f : X ⟶ Y` be a morphism of schemes, let `U` be an open of `Y` and `V` an open of `X` with
`V ⊆ f^{-1}U`, and write `R = Γ(Y, U)` and `A = Γ(X, V)`.  Stacks 0D0I asserts that the canonical
map

`(NL_{A/R})~ ⟶ NL_{X/Y}|_V`

of complexes of sheaves of `𝒪_V`-modules is an isomorphism in `D(𝒪_V)`.  This file builds the two
complexes that map is between, and supplies the arithmetic of germs that identifies the germ of
that map with the ring-level comparison whose quasi-isomorphy
`Stacks.NaiveCotangentAffineComparison.isQuasiIso_nlExtensionBaseChangeMap_canonicalStalkHom`
records.

## Main definitions

* `Stacks.NaiveCotangentAffineIso.alpha` is the ring map `Γ(X, V) ⟶ Γ(V, ⊤)` along which
  `Γ(V, ⊤)` is an algebra over the sections of `𝒪_X` on `V`: it is the restriction map of `𝒪_X`
  along the equality `V.ι ''ᵁ ⊤ = V`, which is `Scheme.Opens.topIso`'s inverse.
* `Stacks.NaiveCotangentAffineIso.nlSelf` is the naive cotangent complex `NL_{A/R}` as a two-term
  complex of `A`-modules, and `nlSelfModNegOne`, `nlSelfModZero`, `nlSelfModD` are its two terms
  and its differential read in `ModuleCat A`.
* `Stacks.NaiveCotangentAffineIso.associatedNaiveCotangentComplex` is `(NL_{A/R})~`: the complex
  of sheaves of `𝒪_V`-modules obtained by applying the sheaf-associated-to-a-module functor
  degreewise to `NL_{A/R}`.  It is built on the open `V` itself, through
  `Stacks.AssociatedSheaf.associatedSheafFunctor` for the ringed space underlying `V`; no
  identification of `V` with the spectrum of `A` is involved.
* `Stacks.NaiveCotangentAffineIso.restrictedNaiveCotangentComplex` is `NL_{X/Y}|_V`, the
  restriction of `NL_{X/Y}` to `V` along the open immersion `V.ι`, degreewise through Mathlib's
  `AlgebraicGeometry.Scheme.Modules.restrictFunctor`.

## Main results

* `Stacks.NaiveCotangentAffineIso.germ_baseSectionHom`: **the germ of the canonical section.**
  The germ at a point `x` of `V` of the canonical section of `f^{-1}𝒪_Y` attached to `r ∈ Γ(Y, U)`
  is the image of the germ of `r` at `f x` under the identification `𝒪_{Y, f x} ≅ (f^{-1}𝒪_Y)_x`.
  This is the one computation relating the two routes from `Γ(Y, U)` to `(f^{-1}𝒪_Y)_x`: through
  the sections over `V` on the one hand, through the germ at `f x` on the other.
* `Stacks.NaiveCotangentAffineIso.germPolynomialHom_comp_map`,
  `Stacks.NaiveCotangentAffineIso.cotangentMap_germSelfHom_eq_canonicalStalkHom` and
  `Stacks.NaiveCotangentAffineIso.cotangentSpaceMap_germSelfHom_eq_canonicalStalkHom`:
  **the germ square composes to the canonical morphism of extensions.**  The morphism of
  extensions `Stacks.SheafOfModules.germSelfHom` given by the germ maps, composed with the change
  of base `Stacks.NaiveCotangentAffineComparison.baseChangeSelfHom`, is
  `Stacks.NaiveCotangentAffineComparison.canonicalStalkHom`.  The first statement is the equality
  of the underlying maps of polynomial rings, which is what the two others — the equality of the
  induced maps on conormal modules and on cotangent spaces — are read off from.
* `Stacks.NaiveCotangentAffineIso.germ_smul_conormalSheaf` and
  `Stacks.NaiveCotangentAffineIso.germ_smul_tensorDifferentialsSheaf`: the germ map of the two
  terms of `NL_{B/A}` is semilinear over the germ map of `A`, the scalar being a section of `A`
  acting through `φ`.
* `Stacks.NaiveCotangentAffineIso.presentation_app_freeAlgebraSectionsMap_X`: every section of
  `B` over an open is the image under the canonical presentation `A[B] ⟶ B` of the section
  attached to its own variable.  This is what lets a scalar which is a section of `B` be read as
  a scalar which is a section of `A[B]`, and so lets the semilinearity statements of Stacks 0D09
  — which are over the stalk of the presentation — absorb the scalar that the germ of a map out
  of an associated sheaf produces.

## Implementation notes

**Two readings of the section ring, and why the germ lemmas are stated abstractly.**  `Γ(X, V)`
is `X.presheaf.obj (op V)`, while the site-level comparison and the germ formulas of
`StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentAffineGerm` are stated over
`X.sheaf.obj.obj (op V)`.  The two are the same term, but `SheafedSpace.sheaf` is a plain
definition, so they are not interchangeable at the transparency level at which a rewrite checks
that its motive is type-correct: `rw` and `simp` report the goal as ill-typed on any statement
mixing them.  Every proof here is therefore composed from `Eq.trans` and `congrArg` rather than
rewritten, and `Stacks.NaiveCotangentAffineIso.germPolynomialHom_comp_map` is stated entirely in
the second reading, the bridge to the first being made once, by ascription, in the two statements
about `Algebra.Extension.Cotangent.map` and `Algebra.Extension.CotangentSpace.map`.

**Why the two germ-semilinearity statements are over abstract sheaves of rings.**  The scalar
action on a section of a term of the naive cotangent complex of the *canonical* presentation
`A[B] ⟶ B` cannot be written down at all: finding it unfolds a sheafification, and the
elaborator's budget is spent before the statement is formed.  The two statements are therefore
made for an arbitrary morphism `φ : A ⟶ B` of sheaves of rings, where the terms are small, and
instantiated afterwards.  This is the same device as
`Stacks.SheafOfModules.moduleGerm`, which names the germ of a section of a presheaf of modules
for the same reason.

**What is not here.**  The canonical map `(NL_{A/R})~ ⟶ NL_{X/Y}|_V` itself, and its being an
isomorphism in `D(𝒪_V)`, are not proved, and no declaration in this file carries the tag 0D0I.
What is missing is the adjoint of
`Stacks.NaiveCotangentAffineComparison.sectionsBaseComparison` under
`Stacks.AssociatedSheaf.associatedSheafAdjunction`, degreewise: the datum it consumes is a map of
`Γ(X, V)`-modules into the global sections over `V` of a term of `NL_{X/Y}|_V`, and producing it
means exhibiting the composite of the comparison on sections with the restriction along
`V.ι ''ᵁ ⊤ = V` as a semilinear map.  Elaborating that semilinearity at the concrete terms
exhausts the elaborator's budget; it has to be packaged as one statement about an abstract sheaf
of modules on an open, as the germ formulas of
`StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentAffineGermTensor` are.  With that datum in
place, `Stacks.AssociatedSheaf.associatedSheafDesc` and
`HomologicalComplex.mkHomFromDouble` give the map, and the germ formulas of this file together
with `Stacks.AssociatedSheaf.stalkMap_associatedSheafDesc_germ_tmul`,
`AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso`, Stacks 0D09 and
`CochainComplex.quasiIso_of_isZero_X_of_addEquiv` give the tag.

One further ingredient has to be folded into that same packaged statement rather than named on
its own: the two identifications of Stacks 0D09 are semilinear over the stalk of the canonical
presentation, while the germ of a map out of an associated sheaf carries a scalar which is the
germ of a section of `𝒪_X`, and the statement converting one into the other cannot be written at
the canonical presentation for the reason given above — the section it would have to mention is
one of a sheafification.  `Stacks.NaiveCotangentAffineIso.germ_smul_conormalSheaf`,
`Stacks.NaiveCotangentAffineIso.germ_smul_tensorDifferentialsSheaf` and
`Stacks.NaiveCotangentAffineIso.presentation_app_freeAlgebraSectionsMap_X` are that conversion's
three ingredients, each cheap on its own.

## References

* [Stacks Project, Tag 0D0I](https://stacks.math.columbia.edu/tag/0D0I), of whose proof this is a
  step.
* [Stacks Project, Tag 0D09](https://stacks.math.columbia.edu/tag/0D09), the stalk of the naive
  cotangent complex of a morphism of sheaves of rings.
* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH), the sheaf associated to
  a module and its stalks.
* [Stacks Project, Tag 08TU](https://stacks.math.columbia.edu/tag/08TU), the canonical polynomial
  presentation.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

universe u

noncomputable section

namespace Stacks.NaiveCotangentAffineIso

open TopCat.Presheaf Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal Stacks.SheafOfModules

/-! ### Germ semilinearity of the two terms of the naive cotangent complex -/

section Germ

variable {T : TopCat.{u}} (A B : CategoryTheory.Sheaf (Opens.grothendieckTopology T)
    CommRingCat.{u}) (φ : A ⟶ B)
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology T) φ.hom] (z : T)

/-- **The germ map of the conormal sheaf is semilinear over the germ map of `A`.**  For a section
`σ` of `A` over an open neighbourhood of `z`, the germ of `φ(σ) • u` is the germ of `σ` acting on
the germ of `u`: the conormal sheaf is a sheaf of `A`-modules by restriction of scalars along
`A ⟶ A/I ⟶ B`, and this is the characterising equation of the module structure on its stalk. -/
theorem germ_smul_conormalSheaf (W : Opens T) (hz : z ∈ W) (σ : A.obj.obj (op W))
    (u : (conormalSheaf (Opens.grothendieckTopology T) A B φ).val.obj (op W)) :
    (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (conormalSheaf (Opens.grothendieckTopology T) A B φ).val.presheaf W z hz).hom
        ((φ.hom.app (op W)).hom σ • u) =
      (show ToType (TopCat.Presheaf.stalk A.obj z) from (TopCat.Presheaf.germ A.obj W z hz).hom σ) •
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (conormalSheaf (Opens.grothendieckTopology T) A B φ).val.presheaf W z hz).hom u :=
  PresheafOfModules.germ_smul (conormalSheafOverSource A B φ) z W hz σ u

/-- **The germ map of the tensor-differentials sheaf is semilinear over the germ map of `A`.**
The degree `0` counterpart of
`Stacks.NaiveCotangentAffineIso.germ_smul_conormalSheaf`. -/
theorem germ_smul_tensorDifferentialsSheaf
    (R : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}) (a : R ⟶ A)
    (W : Opens T) (hz : z ∈ W) (σ : A.obj.obj (op W))
    (u : (tensorDifferentialsSheaf (Opens.grothendieckTopology T) R A B a φ).val.obj (op W)) :
    (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (tensorDifferentialsSheaf (Opens.grothendieckTopology T) R A B a φ).val.presheaf
        W z hz).hom ((φ.hom.app (op W)).hom σ • u) =
      (show ToType (TopCat.Presheaf.stalk A.obj z) from (TopCat.Presheaf.germ A.obj W z hz).hom σ) •
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (tensorDifferentialsSheaf (Opens.grothendieckTopology T) R A B a φ).val.presheaf
          W z hz).hom u :=
  PresheafOfModules.germ_smul (tensorSheafOverSource R A B a φ) z W hz σ u

/-! ### The two identifications of Stacks 0D09 are linear over the stalk of `B` -/

/-- **Every section of `B` is the image of one variable of the canonical presentation.**  The
section of `A[B]` attached to the variable indexed by `s` is carried to `s` by the presentation
`A[B] ⟶ B`.  This is what lets a scalar which is a section of `B` be read as a scalar which is a
section of `A[B]`, and so lets the semilinearity statements of Stacks 0D09 absorb it. -/
theorem presentation_app_freeAlgebraSectionsMap_X (a : A ⟶ B) (W : Opens T)
    (s : ToType (B.obj.obj (op W))) :
    ((presentation (Opens.grothendieckTopology T) A B a
          (underlyingPresheaf (Opens.grothendieckTopology T) B) (𝟙 _)).hom.app (op W)).hom
        (freeAlgebraSectionsMap (Opens.grothendieckTopology T) A B (op W)
          (MvPolynomial.X s)) = s := by
  let := algebraSections (Opens.grothendieckTopology T) A B a (op W)
  exact (presentation_freeAlgebraSectionsMap A B a W (MvPolynomial.X s)).trans
    (algebraMap_sections_mvPolynomialX A B a W s)

end Germ

/-! ### The germ of the canonical section of the inverse image -/

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens} (hVU : V ≤ f ⁻¹ᵁ U)
  {x : X} (hx : x ∈ V) (hfx : f x ∈ U)

/-- **The inverse image of the structure sheaf of `Y`**, as a sheaf of commutative rings on `X`;
this is the spelling that `StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentAffineStalk` and
`StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentAffineComparison` use. -/
abbrev invSheaf : CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u} :=
  (TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf

/-- **The germ of the canonical section of `f^{-1}𝒪_Y`.**  For `x ∈ V` with `f x ∈ U`, the germ
at `x` of the section `Stacks.NaiveCotangentAffineComparison.baseSectionHom f hVU r` of
`f^{-1}𝒪_Y` over `V` is the image of the germ of `r` at `f x` under the identification
`(f^{-1}𝒪_Y)_x ≅ 𝒪_{Y, f x}` of
`Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso`.

Both sides are routes from `Γ(Y, U)` to `(f^{-1}𝒪_Y)_x`: one through the unit of `f^{-1} ⊣ f_*`
on sections and then the germ, the other through the germ at `f x` and then the comparison of
stalks.  The identification of the two is what makes the change of base of the comparison on
sections composable with the comparison on stalks. -/
theorem germ_baseSectionHom (r : Γ(Y, U)) :
    (TopCat.Presheaf.germ
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).presheaf V x hx).hom
        (Stacks.NaiveCotangentAffineComparison.baseSectionHom f hVU r) =
      (Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso f x).inv.hom
        ((Y.presheaf.germ U (f x) hfx).hom r) := by
  have hb : Stacks.NaiveCotangentAffineComparison.baseSectionHom f hVU r =
      (((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).presheaf.map
          (homOfLE hVU).op).hom
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).unit.app
          Y.sheaf).hom.app (op U)).hom r) := rfl
  have h1 : (Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso f x).inv.hom
        ((Y.presheaf.germ U (f x) hfx).hom r) =
      (TopCat.Presheaf.stalkPushforward CommRingCat.{u} f.base
          ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).presheaf x).hom
        (((TopCat.Presheaf.stalkFunctor CommRingCat.{u} (f x)).map
          ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).unit.app
            Y.sheaf).hom).hom ((Y.presheaf.germ U (f x) hfx).hom r)) :=
    congr($(Stacks.SheafifyStalk.stalkSheafPullbackIso_inv_eq CommRingCat.{u} f.base
      Y.sheaf x).hom ((Y.presheaf.germ U (f x) hfx).hom r))
  have h2 : ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} (f x)).map
          ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).unit.app
            Y.sheaf).hom).hom ((Y.presheaf.germ U (f x) hfx).hom r) =
      (TopCat.Presheaf.germ (C := CommRingCat.{u})
          ((TopCat.Presheaf.pushforward CommRingCat.{u} f.base).obj
            ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).presheaf) U (f x) hfx).hom
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).unit.app
          Y.sheaf).hom.app (op U)).hom r) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply U (f x) hfx _ r
  have h3 := congr($(TopCat.Presheaf.stalkPushforward_germ CommRingCat.{u} f.base
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).presheaf U x hfx).hom
    ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).unit.app
      Y.sheaf).hom.app (op U)).hom r))
  refine Eq.trans (congrArg (TopCat.Presheaf.germ
    ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).presheaf V x hx).hom hb) ?_
  refine Eq.trans (TopCat.Presheaf.germ_res_apply
    ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).presheaf (homOfLE hVU) x hx _) ?_
  refine Eq.trans ?_ h1.symm
  refine Eq.trans ?_ (congrArg (TopCat.Presheaf.stalkPushforward CommRingCat.{u} f.base
    ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).presheaf x).hom h2.symm)
  exact h3.symm

/-! ### The germ square composes to the canonical morphism of extensions -/

/-- **The germ square composes to the canonical square, on polynomial rings.**  The polynomial
map `Stacks.SheafOfModules.germPolynomialHom` given by the germ maps of `f^{-1}𝒪_Y` and of
`𝒪_X`, precomposed with the change of coefficients `Γ(Y, U) ⟶ (f^{-1}𝒪_Y)(V)` of
`Stacks.NaiveCotangentAffineComparison.baseChangeSelfHom`, is the polynomial map
`Stacks.NaiveCotangentAffineComparison.squareRingHom` of the square of rings underlying
`Stacks.NaiveCotangentAffineComparison.canonicalStalkHom`.

On a constant this is `Stacks.NaiveCotangentAffineIso.germ_baseSectionHom`, and on a variable it
is the definition of the two algebra structures of `𝒪_{X,x}` over `Γ(X, V)`. -/
theorem germPolynomialHom_comp_map :
    letI := Stacks.NaiveCotangentAffineComparison.algebraAppLE' f hVU
    letI := Stacks.NaiveCotangentAffineComparison.algebraBaseSection f hVU
    letI := Stacks.SheafOfModules.algebraGerm X.sheaf x V hx
    letI := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImage f hfx
    letI := Stacks.RelativeDifferentialStalk.algebraStalk
      (AlgebraicGeometry.inverseImageStructureMap f).hom x
    (Stacks.SheafOfModules.germPolynomialHom (invSheaf f) X.sheaf x V hx).comp
        (MvPolynomial.map (σ := ↑(X.sheaf.obj.obj (op V)))
          (algebraMap Γ(Y, U) ↑((invSheaf f).obj.obj (op V)))) =
      Stacks.NaiveCotangentAffineComparison.squareRingHom
        (R := Γ(Y, U)) (S := ↑(X.sheaf.obj.obj (op V)))
        (R' := ↑(TopCat.Presheaf.stalk (invSheaf f).obj x))
        (S' := ↑(TopCat.Presheaf.stalk X.sheaf.obj x)) := by
  let := Stacks.NaiveCotangentAffineComparison.algebraAppLE' f hVU
  let := Stacks.NaiveCotangentAffineComparison.algebraBaseSection f hVU
  let := Stacks.SheafOfModules.algebraGerm X.sheaf x V hx
  let := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImage f hfx
  let := Stacks.RelativeDifferentialStalk.algebraStalk
    (AlgebraicGeometry.inverseImageStructureMap f).hom x
  unfold Stacks.NaiveCotangentAffineComparison.squareRingHom
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun b => ?_)
  · refine Eq.trans (congrArg (Stacks.SheafOfModules.germPolynomialHom (invSheaf f) X.sheaf x V hx)
      (MvPolynomial.map_C _ r)) ?_
    refine Eq.trans (Stacks.SheafOfModules.germPolynomialHom_C (invSheaf f) X.sheaf x V hx _) ?_
    refine Eq.trans (congrArg MvPolynomial.C (germ_baseSectionHom f hVU hx hfx r)) ?_
    rw [MvPolynomial.eval₂Hom_C]
    rfl
  · refine Eq.trans (congrArg (Stacks.SheafOfModules.germPolynomialHom (invSheaf f) X.sheaf x V hx)
      (MvPolynomial.map_X _ b)) ?_
    refine Eq.trans (Stacks.SheafOfModules.germPolynomialHom_X (invSheaf f) X.sheaf x V hx b) ?_
    rw [MvPolynomial.eval₂Hom_X']
    rfl

/-- **The germ square composes to the canonical square, in degree `-1`.**  The conormal map of
the morphism of extensions given by the germ maps, applied after the conormal map of the change
of base of the canonical presentation, is the conormal map of
`Stacks.NaiveCotangentAffineComparison.canonicalStalkHom`.

This is `Stacks.NaiveCotangentAffineIso.germPolynomialHom_comp_map` read through
`Algebra.Extension.Cotangent.map_mk`: both sides send the class of a polynomial `g` over
`Γ(Y, U)` in the kernel to the class of its image, and the two images agree. -/
theorem cotangentMap_germSelfHom_eq_canonicalStalkHom :
    letI := Stacks.NaiveCotangentAffineComparison.algebraAppLE' f hVU
    letI := Stacks.NaiveCotangentAffineComparison.algebraBaseSection f hVU
    letI := Stacks.NaiveCotangentAffineSections.algebraSections f V
    haveI := Stacks.NaiveCotangentAffineComparison.isScalarTower_baseSection f hVU
    letI : Algebra Γ(X, V) ↑(X.sheaf.obj.obj (op V)) := Algebra.id Γ(X, V)
    letI := Stacks.SheafOfModules.algebraGerm (invSheaf f) x V hx
    letI := Stacks.SheafOfModules.algebraGerm X.sheaf x V hx
    letI := Stacks.RelativeDifferentialStalk.algebraStalk
      (AlgebraicGeometry.inverseImageStructureMap f).hom x
    letI := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImageStructureMap f (x := x)
    letI := Stacks.SheafOfModules.algebraGermComp (invSheaf f) X.sheaf
      (AlgebraicGeometry.inverseImageStructureMap f) x V hx
    haveI := Stacks.SheafOfModules.isScalarTower_germ (invSheaf f) X.sheaf
      (AlgebraicGeometry.inverseImageStructureMap f) x V hx
    letI := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
    letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : V)
    letI := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImage f hfx
    letI := Stacks.NaiveCotangentAffineStalk.algebraStalkOfAppLE f hVU hx
    haveI : IsScalarTower Γ(Y, U) Γ(X, V) ↑(X.presheaf.stalk x) :=
      Stacks.NaiveCotangentAffineStalk.isScalarTower_appLE f hVU hx
    haveI : IsScalarTower Γ(Y, U) ↑(TopCat.Presheaf.stalk (invSheaf f).obj x)
        ↑(X.presheaf.stalk x) :=
      Stacks.NaiveCotangentAffineStalk.isScalarTower_stalkInverseImage f hVU hx hfx
    ∀ m : (Algebra.Generators.self Γ(Y, U) Γ(X, V)).toExtension.Cotangent,
      Algebra.Extension.Cotangent.map
            (Stacks.SheafOfModules.germSelfHom (invSheaf f) X.sheaf
              (AlgebraicGeometry.inverseImageStructureMap f) x V hx)
            (Algebra.Extension.Cotangent.map
              (Stacks.NaiveCotangentAffineComparison.baseChangeSelfHom
                (R := Γ(Y, U)) (R' := ↑((invSheaf f).obj.obj (op V)))
                (A := ↑(X.sheaf.obj.obj (op V)))) m) =
        Algebra.Extension.Cotangent.map
          (Stacks.NaiveCotangentAffineComparison.canonicalStalkHom f hVU hx hfx) m := by
  let := Stacks.NaiveCotangentAffineComparison.algebraAppLE' f hVU
  let := Stacks.NaiveCotangentAffineComparison.algebraBaseSection f hVU
  let := Stacks.NaiveCotangentAffineSections.algebraSections f V
  have _ := Stacks.NaiveCotangentAffineComparison.isScalarTower_baseSection f hVU
  let _ : Algebra Γ(X, V) ↑(X.sheaf.obj.obj (op V)) := Algebra.id Γ(X, V)
  let := Stacks.SheafOfModules.algebraGerm (invSheaf f) x V hx
  let := Stacks.SheafOfModules.algebraGerm X.sheaf x V hx
  let := Stacks.RelativeDifferentialStalk.algebraStalk
    (AlgebraicGeometry.inverseImageStructureMap f).hom x
  let := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImageStructureMap f (x := x)
  let := Stacks.SheafOfModules.algebraGermComp (invSheaf f) X.sheaf
    (AlgebraicGeometry.inverseImageStructureMap f) x V hx
  have _ := Stacks.SheafOfModules.isScalarTower_germ (invSheaf f) X.sheaf
    (AlgebraicGeometry.inverseImageStructureMap f) x V hx
  let := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
  let := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : V)
  let := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImage f hfx
  let := Stacks.NaiveCotangentAffineStalk.algebraStalkOfAppLE f hVU hx
  have _ : IsScalarTower Γ(Y, U) Γ(X, V) ↑(X.presheaf.stalk x) :=
    Stacks.NaiveCotangentAffineStalk.isScalarTower_appLE f hVU hx
  have _ : IsScalarTower Γ(Y, U) ↑(TopCat.Presheaf.stalk (invSheaf f).obj x)
      ↑(X.presheaf.stalk x) :=
    Stacks.NaiveCotangentAffineStalk.isScalarTower_stalkInverseImage f hVU hx hfx
  intro m
  obtain ⟨g, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective m
  refine Eq.trans (congrArg (Algebra.Extension.Cotangent.map
    (Stacks.SheafOfModules.germSelfHom (invSheaf f) X.sheaf
      (AlgebraicGeometry.inverseImageStructureMap f) x V hx))
    (Algebra.Extension.Cotangent.map_mk _ g)) ?_
  refine Eq.trans (Algebra.Extension.Cotangent.map_mk _ _) ?_
  refine Eq.symm (Eq.trans (Algebra.Extension.Cotangent.map_mk _ g) ?_)
  exact congrArg Algebra.Extension.Cotangent.mk (Subtype.ext
    (DFunLike.congr_fun (germPolynomialHom_comp_map f hVU hx hfx) g.1).symm)

/-- **The germ square composes to the canonical square, in degree `0`.**  The degree `0`
counterpart of
`Stacks.NaiveCotangentAffineIso.cotangentMap_germSelfHom_eq_canonicalStalkHom`: the elements
`b ⊗ d p` generate the cotangent space as an abelian group
(`Stacks.NaiveCotangent.cotangentSpace_hom_ext`), and on them both sides are the tensor of the
germ of `b` with the universal differential of the image of `p`. -/
theorem cotangentSpaceMap_germSelfHom_eq_canonicalStalkHom :
    letI := Stacks.NaiveCotangentAffineComparison.algebraAppLE' f hVU
    letI := Stacks.NaiveCotangentAffineComparison.algebraBaseSection f hVU
    letI := Stacks.NaiveCotangentAffineSections.algebraSections f V
    haveI := Stacks.NaiveCotangentAffineComparison.isScalarTower_baseSection f hVU
    letI : Algebra Γ(X, V) ↑(X.sheaf.obj.obj (op V)) := Algebra.id Γ(X, V)
    letI := Stacks.SheafOfModules.algebraGerm (invSheaf f) x V hx
    letI := Stacks.SheafOfModules.algebraGerm X.sheaf x V hx
    letI := Stacks.RelativeDifferentialStalk.algebraStalk
      (AlgebraicGeometry.inverseImageStructureMap f).hom x
    letI := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImageStructureMap f (x := x)
    letI := Stacks.SheafOfModules.algebraGermComp (invSheaf f) X.sheaf
      (AlgebraicGeometry.inverseImageStructureMap f) x V hx
    haveI := Stacks.SheafOfModules.isScalarTower_germ (invSheaf f) X.sheaf
      (AlgebraicGeometry.inverseImageStructureMap f) x V hx
    letI := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
    letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : V)
    letI := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImage f hfx
    letI := Stacks.NaiveCotangentAffineStalk.algebraStalkOfAppLE f hVU hx
    haveI : IsScalarTower Γ(Y, U) Γ(X, V) ↑(X.presheaf.stalk x) :=
      Stacks.NaiveCotangentAffineStalk.isScalarTower_appLE f hVU hx
    haveI : IsScalarTower Γ(Y, U) ↑(TopCat.Presheaf.stalk (invSheaf f).obj x)
        ↑(X.presheaf.stalk x) :=
      Stacks.NaiveCotangentAffineStalk.isScalarTower_stalkInverseImage f hVU hx hfx
    ∀ m : (Algebra.Generators.self Γ(Y, U) Γ(X, V)).toExtension.CotangentSpace,
      Algebra.Extension.CotangentSpace.map
            (Stacks.SheafOfModules.germSelfHom (invSheaf f) X.sheaf
              (AlgebraicGeometry.inverseImageStructureMap f) x V hx)
            (Algebra.Extension.CotangentSpace.map
              (Stacks.NaiveCotangentAffineComparison.baseChangeSelfHom
                (R := Γ(Y, U)) (R' := ↑((invSheaf f).obj.obj (op V)))
                (A := ↑(X.sheaf.obj.obj (op V)))) m) =
        Algebra.Extension.CotangentSpace.map
          (Stacks.NaiveCotangentAffineComparison.canonicalStalkHom f hVU hx hfx) m := by
  let := Stacks.NaiveCotangentAffineComparison.algebraAppLE' f hVU
  let := Stacks.NaiveCotangentAffineComparison.algebraBaseSection f hVU
  let := Stacks.NaiveCotangentAffineSections.algebraSections f V
  have _ := Stacks.NaiveCotangentAffineComparison.isScalarTower_baseSection f hVU
  let _ : Algebra Γ(X, V) ↑(X.sheaf.obj.obj (op V)) := Algebra.id Γ(X, V)
  let := Stacks.SheafOfModules.algebraGerm (invSheaf f) x V hx
  let := Stacks.SheafOfModules.algebraGerm X.sheaf x V hx
  let := Stacks.RelativeDifferentialStalk.algebraStalk
    (AlgebraicGeometry.inverseImageStructureMap f).hom x
  let := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImageStructureMap f (x := x)
  let := Stacks.SheafOfModules.algebraGermComp (invSheaf f) X.sheaf
    (AlgebraicGeometry.inverseImageStructureMap f) x V hx
  have _ := Stacks.SheafOfModules.isScalarTower_germ (invSheaf f) X.sheaf
    (AlgebraicGeometry.inverseImageStructureMap f) x V hx
  let := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
  let := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : V)
  let := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImage f hfx
  let := Stacks.NaiveCotangentAffineStalk.algebraStalkOfAppLE f hVU hx
  have _ : IsScalarTower Γ(Y, U) Γ(X, V) ↑(X.presheaf.stalk x) :=
    Stacks.NaiveCotangentAffineStalk.isScalarTower_appLE f hVU hx
  have _ : IsScalarTower Γ(Y, U) ↑(TopCat.Presheaf.stalk (invSheaf f).obj x)
      ↑(X.presheaf.stalk x) :=
    Stacks.NaiveCotangentAffineStalk.isScalarTower_stalkInverseImage f hVU hx hfx
  refine fun m => DFunLike.congr_fun (Stacks.NaiveCotangent.cotangentSpace_hom_ext
    (Algebra.Generators.self Γ(Y, U) Γ(X, V)).toExtension
    ((Algebra.Extension.CotangentSpace.map
        (Stacks.SheafOfModules.germSelfHom (invSheaf f) X.sheaf
          (AlgebraicGeometry.inverseImageStructureMap f) x V hx)).toAddMonoidHom.comp
      (Algebra.Extension.CotangentSpace.map
        (Stacks.NaiveCotangentAffineComparison.baseChangeSelfHom
          (R := Γ(Y, U)) (R' := ↑((invSheaf f).obj.obj (op V)))
          (A := ↑(X.sheaf.obj.obj (op V))))).toAddMonoidHom)
    (Algebra.Extension.CotangentSpace.map
      (Stacks.NaiveCotangentAffineComparison.canonicalStalkHom f hVU hx hfx)).toAddMonoidHom
    (fun b q => ?_)) m
  refine Eq.trans (congrArg (Algebra.Extension.CotangentSpace.map
    (Stacks.SheafOfModules.germSelfHom (invSheaf f) X.sheaf
      (AlgebraicGeometry.inverseImageStructureMap f) x V hx))
    (Algebra.Extension.CotangentSpace.map_tmul _ b q)) ?_
  refine Eq.trans (Algebra.Extension.CotangentSpace.map_tmul _ _ _) ?_
  refine Eq.symm (Eq.trans (Algebra.Extension.CotangentSpace.map_tmul _ b q) ?_)
  refine congrArg₂ (fun (bb : ↑(TopCat.Presheaf.stalk X.sheaf.obj x))
      (qq : (Algebra.Generators.self ↑(TopCat.Presheaf.stalk (invSheaf f).obj x)
        ↑(TopCat.Presheaf.stalk X.sheaf.obj x)).toExtension.Ring) =>
      bb ⊗ₜ[(Algebra.Generators.self ↑(TopCat.Presheaf.stalk (invSheaf f).obj x)
          ↑(TopCat.Presheaf.stalk X.sheaf.obj x)).toExtension.Ring]
        KaehlerDifferential.D ↑(TopCat.Presheaf.stalk (invSheaf f).obj x)
          ((Algebra.Generators.self ↑(TopCat.Presheaf.stalk (invSheaf f).obj x)
            ↑(TopCat.Presheaf.stalk X.sheaf.obj x)).toExtension.Ring) qq) ?_ ?_
  · exact congrArg (algebraMap ↑(X.sheaf.obj.obj (op V)) ↑(TopCat.Presheaf.stalk X.sheaf.obj x))
      (Algebra.algebraMap_self_apply b)
  · exact (DFunLike.congr_fun (germPolynomialHom_comp_map f hVU hx hfx) q).symm

/-! ### The two complexes -/

/-- **The structural map `Γ(X, V) ⟶ Γ(V, ⊤)`**: the restriction map of `𝒪_X` along the equality
`V.ι ''ᵁ ⊤ = V`, which is the inverse of `AlgebraicGeometry.Scheme.Opens.topIso`.  This is the
ring map along which the sheaf associated to a `Γ(X, V)`-module on the open `V` is formed: the
construction of Stacks 01BH is stated for a ring map into the global sections of a ringed space,
and the global sections of `V` are the sections of `𝒪_X` over `V.ι ''ᵁ ⊤`, not over `V`. -/
abbrev alpha : Γ(X, V) →+* (V.toScheme.toRingedSpace).presheaf.obj (op ⊤) := V.topIso.inv.hom

/-- **`NL_{A/R}` for `A = Γ(X, V)` and `R = Γ(Y, U)`**, as a two-term complex of `A`-modules:
the naive cotangent complex of the canonical presentation of `Γ(X, V)` over `Γ(Y, U)`, the
algebra structure being the restriction `f.appLE U V` of `f`. -/
abbrev nlSelf :
    letI := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
    NaiveCotangent.TwoTerm Γ(X, V) :=
  letI := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
  NaiveCotangent.NL (Algebra.Generators.self Γ(Y, U) Γ(X, V))

/-- The degree `-1` term of `NL_{A/R}`, read in `ModuleCat Γ(X, V)`. -/
abbrev nlSelfModNegOne : ModuleCat.{u} Γ(X, V) :=
  letI := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
  ModuleCat.of Γ(X, V) (nlSelf f hVU).X₁

/-- The degree `0` term of `NL_{A/R}`, read in `ModuleCat Γ(X, V)`. -/
abbrev nlSelfModZero : ModuleCat.{u} Γ(X, V) :=
  letI := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
  ModuleCat.of Γ(X, V) (nlSelf f hVU).X₀

/-- The differential of `NL_{A/R}`, read in `ModuleCat Γ(X, V)`. -/
abbrev nlSelfModD : nlSelfModNegOne f hVU ⟶ nlSelfModZero f hVU :=
  letI := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
  ModuleCat.ofHom (nlSelf f hVU).d

/-- **`(NL_{A/R})~`**, the complex of sheaves of `𝒪_V`-modules associated to `NL_{A/R}`: the
sheaf of Stacks 01BH, construction (3), of each of the two terms, with the associated map of the
differential, placed in degrees `-1` and `0`.

The construction is carried out on the open `V` itself rather than transported along
`V ≅ Spec Γ(X, V)`: `Stacks.AssociatedSheaf.associatedSheafFunctor` is stated for an arbitrary
ringed space and a ring map into its global sections, so it applies to `V` directly, and the
affineness of `V` enters only in the quasi-isomorphy statement. -/
abbrev associatedNaiveCotangentComplex : CochainComplex V.toScheme.Modules ℤ :=
  HomologicalComplex.double
    ((Stacks.AssociatedSheaf.associatedSheafFunctor.{u, u} (V.toScheme.toRingedSpace)
      (alpha (V := V))).map (nlSelfModD f hVU))
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)

/-- **`NL_{X/Y}|_V`**, the restriction of `NL_{X/Y}` to the open `V`: Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` for the open immersion `V.ι`, applied
degreewise.

Restriction along an open immersion is used rather than the inverse image: its sections over an
open `W` of `V` are *equal*, not merely isomorphic, to the sections of the original sheaf over
`V.ι ''ᵁ W` (`AlgebraicGeometry.Scheme.Modules.restrict_obj`), and the comparison of its stalks
with those of the original sheaf
(`AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso`) is an additive bijection of the very
groups that the stalkwise criterion for quasi-isomorphy consumes.  In particular no stalk of a
composite inverse image `(V.ι ≫ f)^{-1}𝒪_Y` occurs. -/
abbrev restrictedNaiveCotangentComplex : CochainComplex V.toScheme.Modules ℤ :=
  ((Scheme.Modules.restrictFunctor V.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (Scheme.naiveCotangentComplex f)

end Stacks.NaiveCotangentAffineIso

end

end
