module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.ExtAlongAnExactFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.AbelianLowerShriek
public import StacksCore.Tactic.StacksAttribute

/-!
# Global cohomology does not change on a bigger site

Let `u : C ⥤ D` be a continuous functor of sites whose restriction functor
`g⁻¹ = u.sheafPushforwardContinuous` on abelian sheaves admits a left adjoint `g_!` which is
exact, so that `g⁻¹` is right exact and carries injective abelian sheaves to injective abelian
sheaves.  Assume moreover that `C` and `D` have terminal objects `e_C`, `e_D` with `u(e_C) = e_D`.
Then restriction along `u` does not change global sheaf cohomology:

`g⁻¹ ⋙ H^p(C, -) ≅ H^p(D, -)`,

naturally in the abelian sheaf on the bigger site, where `H^p` is Mathlib's
`CategoryTheory.Sheaf.functorH`, the `Ext`-groups out of the constant sheaf on `ℤ`.

This is **Stacks 03YU**, statement (1), at *independent universes*: the two sites have objects and
morphisms in arbitrary universes and the coefficients in a third.  Geometric sites — the fppf site
of an algebraic stack, and its slices — are of that shape: their objects live one universe above
their morphisms, and they are not small.

## Main results

* `Stacks.Cohomology.BiggerSiteGlobal.gammaCompRestrictionIso`: `g⁻¹ ⋙ Γ(C, -) ≅ Γ(D, -)`.
* `Stacks.Cohomology.BiggerSiteGlobal.lowerShriekConstantSheafIso`: `g_! ℤ_C ≅ ℤ_D`, the
  statement that lower shriek takes the constant sheaf to the constant sheaf.
* `Stacks.Cohomology.BiggerSiteGlobal.sheafCohomologyIso`: the comparison of global cohomology.
* `Stacks.Cohomology.BiggerSiteGlobal.sheafCohomologyIsoOfAcyclic` and
  `Stacks.Cohomology.BiggerSiteGlobal.cohomologyOverObjectIsoOfAcyclic`: the same two
  comparisons with preservation of injective objects by `g⁻¹` weakened to *acyclicity* of the
  restriction of an injective sheaf. That is the hypothesis the proof of Stacks 07AK supplies
  by comparing Čech complexes along `u` (Stacks 0D6X), and the only one available when `g_!`
  is not exact — as it is not for the inclusion of a subsite with no fibre products.
* `Stacks.Cohomology.BiggerSiteGlobal.sheafCohomologyIsoOfConstantSheafIsoOfAcyclic`: the global
  comparison with the terminal objects themselves weakened to the single isomorphism
  `g_! ℤ_C ≅ ℤ_D` they are a route to. This is the form a subsite of the site of an algebraic
  stack can use: such a subsite has no terminal object once the stack has a nontrivial
  automorphism, by
  `CategoryTheory.Functor.IsFiberedInGroupoids.not_isTerminal_of_faithful_of_ne_id`.

## Implementation notes

The whole proof is the `Ext`-transport of
`Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfIso` — Stacks 015Z read through `Ext` —
applied to the adjunction `g_! ⊣ g⁻¹` of `CategoryTheory.Functor.sheafAdjunctionContinuous` and
to the identification `g_! ℤ_C ≅ ℤ_D`.  That identification is itself obtained from the
comparison of global sections by uniqueness of left adjoints: `Γ` is *defined* as the right
adjoint of the constant sheaf functor, and over a terminal object `Γ` is evaluation
(`CategoryTheory.Sheaf.ΓNatIsoSheafSections`), while restriction composed with evaluation at
`e_C` is evaluation at `u(e_C) = e_D` on the nose.

The existing formalisation of this lemma,
`Stacks.Cohomology.CompositeRightDerived.cohomologySiteIso`, works with the right derived
functors of the limit-over-the-site model of `Γ` and carries `[SmallCategory C]`,
`[SmallCategory D]`; and `Stacks.Cohomology.BiggerSite.extFunctorObjIso` is its `Ext`-based
*objectwise* counterpart, again only for small sites.  Neither applies to a geometric site, so
the comparison is proved here directly from the `Ext` transport rather than transported from
either of them.

The exactness of `g_!` and the right exactness of `g⁻¹` enter only through the two typeclass
hypotheses `[PreservesFiniteColimits …]` and `[… .PreservesInjectiveObjects]` on the restriction
functor.  Stated that way rather than through the "bigger site" package of Stacks 03A4 — fully
faithfulness of `u`, fibre products in `C` preserved by `u`, and
`[(u.sheafPullback _ J K).PreservesMonomorphisms]` — the statement is the one a consumer can
actually use: those hypotheses are only ever a route to these.

## References

* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 03A4](https://stacks.math.columbia.edu/tag/03A4)
* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Cohomology.BiggerSiteGlobal

universe w v u

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D)

section Sections

variable (A : Type*) [Category* A] [HasWeakSheafify J A] [HasWeakSheafify K A]
  [u.IsContinuous J K]

omit [HasWeakSheafify J A] [HasWeakSheafify K A] in
/-- **Restriction along a continuous functor is evaluation at the image object.** The underlying
presheaf of `g⁻¹ F` is `F ∘ uᵒᵖ`, so the sections of `g⁻¹ F` over `X` are the sections of `F`
over `u(X)` on the nose. -/
theorem sheafSections_comp_sheafPushforwardContinuous (X : C) :
    u.sheafPushforwardContinuous A J K ⋙ (sheafSections J A).obj (op X) =
      (sheafSections K A).obj (op (u.obj X)) :=
  rfl

variable [HasGlobalSectionsFunctor J A] [HasGlobalSectionsFunctor K A]

/-- **Restriction along a continuous functor does not change global sections.** For terminal
objects `e_C` of `C` and `e_D` of `D` with `u(e_C) = e_D`, we have `Γ(C, g⁻¹ F) ≅ Γ(D, F)`,
naturally in `F`.

Global sections over a site with a terminal object are the sections over that object
(`CategoryTheory.Sheaf.ΓNatIsoSheafSections`), and restriction turns sections over `e_C` into
sections over `u(e_C) = e_D`. -/
def gammaCompRestrictionIso {eC : C} {eD : D} (heC : IsTerminal eC) (heD : IsTerminal eD)
    (hu : u.obj eC = eD) :
    u.sheafPushforwardContinuous A J K ⋙ Sheaf.Γ J A ≅ Sheaf.Γ K A :=
  have : HasTerminal C := heC.hasTerminal
  have : HasTerminal D := heD.hasTerminal
  Functor.isoWhiskerLeft _ (Sheaf.ΓNatIsoSheafSections J A heC) ≪≫
    eqToIso ((sheafSections_comp_sheafPushforwardContinuous J K u A eC).trans (by rw [hu])) ≪≫
    (Sheaf.ΓNatIsoSheafSections K A heD).symm

end Sections

section Cohomology

variable [u.IsContinuous J K]
  [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasGlobalSectionsFunctor J AddCommGrpCat.{w}]
  [HasGlobalSectionsFunctor K AddCommGrpCat.{w}]
  [(u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]

/-- The adjunction `g_! ⊣ g⁻¹` on abelian sheaves. -/
abbrev lowerShriekAdjunction :
    lowerShriekAbelian J K u ⊣ u.sheafPushforwardContinuous AddCommGrpCat.{w} J K :=
  u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K

/-- Restriction `g⁻¹` is additive: as a right adjoint it preserves binary products. -/
instance : (u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).Additive :=
  have : PreservesLimitsOfSize.{0, 0}
      (u.sheafPushforwardContinuous AddCommGrpCat.{w} J K) :=
    (lowerShriekAdjunction J K u).rightAdjoint_preservesLimits
  Functor.additive_of_preserves_binary_products _

/-- Lower shriek `g_!` is additive, being a left adjoint between additive categories. -/
instance : (lowerShriekAbelian J K u).Additive :=
  (lowerShriekAdjunction J K u).left_adjoint_additive

/-- **Lower shriek takes the constant sheaf to the constant sheaf.** For terminal objects
`e_C`, `e_D` with `u(e_C) = e_D` and any coefficient group `M`, `g_! M_C ≅ M_D`.

Both `g_! ∘ (constant sheaf on C)` and `constant sheaf on D` are left adjoint to `Γ(D, -)`: the
first because its right adjoint is `g⁻¹ ⋙ Γ(C, -)`, which `gammaCompRestrictionIso` identifies
with `Γ(D, -)`, and the second by the definition of `Γ`. -/
def lowerShriekConstantSheafIso {eC : C} {eD : D} (heC : IsTerminal eC) (heD : IsTerminal eD)
    (hu : u.obj eC = eD) :
    constantSheaf J AddCommGrpCat.{w} ⋙ lowerShriekAbelian J K u ≅
      constantSheaf K AddCommGrpCat.{w} :=
  Adjunction.leftAdjointUniq
    (Adjunction.ofNatIsoRight
      ((constantSheafΓAdj J AddCommGrpCat.{w}).comp (lowerShriekAdjunction J K u))
      (gammaCompRestrictionIso J K u AddCommGrpCat.{w} heC heD hu))
    (constantSheafΓAdj K AddCommGrpCat.{w})

variable [HasExt.{max u w} (Sheaf J AddCommGrpCat.{w})]
  [HasExt.{max u w} (Sheaf K AddCommGrpCat.{w})]
  [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{w})]
  [HasInjectiveResolutions (Sheaf K AddCommGrpCat.{w})]
  [PreservesFiniteColimits (u.sheafPushforwardContinuous AddCommGrpCat.{w} J K)]
  [(u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).PreservesInjectiveObjects]

/-- **Stacks 03YU (1): restriction from a bigger site does not change global cohomology.** For
terminal objects `e_C` of `C` and `e_D` of `D` with `u(e_C) = e_D`, and every degree `p`,

`H^p(C, g⁻¹ F) ≅ H^p(D, F)`

naturally in the abelian sheaf `F` on the bigger site `(D, K)`, where `H^p` is `Ext^p` out of the
constant sheaf on `ℤ`.

The two hypotheses on `g⁻¹` beyond continuity — right exactness and preservation of injective
objects — are the content of Stacks 03A4 that this lemma consumes: they hold whenever `g⁻¹` has
an exact left adjoint `g_!`, which for a fully faithful continuous and cocontinuous `u` between
sites with fibre products is Stacks 03A4 itself. -/
@[stacks 03YU "global cohomology, at independent site and coefficient universes"]
def sheafCohomologyIso {eC : C} {eD : D} (heC : IsTerminal eC) (heD : IsTerminal eD)
    (hu : u.obj eC = eD) (p : ℕ) :
    u.sheafPushforwardContinuous AddCommGrpCat.{w} J K ⋙
        Sheaf.functorH.{max u w, w, v, u} J p ≅
      Sheaf.functorH.{max u w, w, v, u} K p :=
  (Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfIso
    (lowerShriekAdjunction J K u)
    ((lowerShriekConstantSheafIso J K u heC heD hu).app
      (AddCommGrpCat.of (ULift.{w} ℤ))) p).symm

end Cohomology

section CohomologyFromAcyclicity

variable [u.IsContinuous J K]
  [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasGlobalSectionsFunctor J AddCommGrpCat.{w}]
  [HasGlobalSectionsFunctor K AddCommGrpCat.{w}]
  [(u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]
  [HasExt.{max u w} (Sheaf J AddCommGrpCat.{w})]
  [HasExt.{max u w} (Sheaf K AddCommGrpCat.{w})]
  [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{w})]
  [HasInjectiveResolutions (Sheaf K AddCommGrpCat.{w})]
  [EnoughInjectives (Sheaf K AddCommGrpCat.{w})]
  [PreservesFiniteColimits (u.sheafPushforwardContinuous AddCommGrpCat.{w} J K)]

/-- **Restriction from a bigger site does not change global cohomology, from the comparison of
constant sheaves and acyclicity.** Suppose `g_!` carries the constant sheaf on `ℤ` of `(C, J)` to
the constant sheaf on `ℤ` of `(D, K)`, and that the restriction of an injective abelian sheaf has
vanishing higher global cohomology on `(C, J)`. Then for every degree `p`

`H^p(C, g⁻¹ F) ≅ H^p(D, F)`

naturally in the abelian sheaf `F` on the bigger site `(D, K)`.

This is `Stacks.Cohomology.BiggerSiteGlobal.sheafCohomologyIsoOfAcyclic` with the two terminal
objects replaced by the one isomorphism they are a route to: terminality enters that statement
only through `lowerShriekConstantSheafIso`, which produces exactly the datum `e` below. The
replacement is what makes the comparison applicable to the inclusion of the lisse-étale or
flat-fppf subsite of an algebraic stack, which has no terminal object as soon as the stack has a
nontrivial automorphism — see
`CategoryTheory.Functor.IsFiberedInGroupoids.not_isTerminal_of_faithful_of_ne_id` — while the
comparison of constant sheaves still holds, being the degree-zero case of the comparison itself.

The universality argument that propagates the comparison from degree zero to every degree is
`Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfIsoOfAcyclic`, so no spectral sequence is
needed beyond the degree-zero datum `e` and the acyclicity hypothesis. -/
def sheafCohomologyIsoOfConstantSheafIsoOfAcyclic
    (e : (lowerShriekAbelian J K u).obj ((constantSheaf J AddCommGrpCat.{w}).obj
          (AddCommGrpCat.of (ULift.{w} ℤ))) ≅
        (constantSheaf K AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w} ℤ)))
    (hacyclic : ∀ (I : Sheaf K AddCommGrpCat.{w}), Injective I → ∀ (n : ℕ)
      (a : Sheaf.H ((u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj I) (n + 1)), a = 0)
    (p : ℕ) :
    u.sheafPushforwardContinuous AddCommGrpCat.{w} J K ⋙
        Sheaf.functorH.{max u w, w, v, u} J p ≅
      Sheaf.functorH.{max u w, w, v, u} K p :=
  (Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfIsoOfAcyclic
    (lowerShriekAdjunction J K u) e (fun I _ n a ↦ hacyclic I inferInstance n a) p).symm

/-- **Restriction from a bigger site does not change global cohomology, from acyclicity.** For
terminal objects `e_C` of `C` and `e_D` of `D` with `u(e_C) = e_D`, and every degree `p`,

`H^p(C, g⁻¹ F) ≅ H^p(D, F)`

naturally in the abelian sheaf `F` on the bigger site `(D, K)`, provided only that the
restriction of an injective abelian sheaf has vanishing higher global cohomology on `(C, J)`.

This is `Stacks.Cohomology.BiggerSiteGlobal.sheafCohomologyIso` with the hypothesis
`[(u.sheafPushforwardContinuous …).PreservesInjectiveObjects]` replaced by the acyclicity
statement it is only ever a route to. The replacement is what makes the lemma applicable to the
inclusion of a subsite that is not closed under fibre products: there `g_!` is not exact, so
restriction does not preserve injective objects, while the restriction of an injective sheaf is
still acyclic — the content of Stacks 0D6X, by comparison of Čech complexes along `u`.

The hypothesis is stated as the vanishing of `CategoryTheory.Sheaf.H` rather than as
preservation of injectives precisely so that 0D6X can discharge it.

The terminal objects are used only to produce the comparison of constant sheaves which
`sheafCohomologyIsoOfConstantSheafIsoOfAcyclic` takes as a datum. -/
@[stacks 03YU "global cohomology, from acyclicity of the restriction of an injective sheaf",
  sga "4½ Arcata 2.3.5" "H^p(Y, special case"]
def sheafCohomologyIsoOfAcyclic {eC : C} {eD : D} (heC : IsTerminal eC) (heD : IsTerminal eD)
    (hu : u.obj eC = eD)
    (hacyclic : ∀ (I : Sheaf K AddCommGrpCat.{w}), Injective I → ∀ (n : ℕ)
      (a : Sheaf.H ((u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj I) (n + 1)), a = 0)
    (p : ℕ) :
    u.sheafPushforwardContinuous AddCommGrpCat.{w} J K ⋙
        Sheaf.functorH.{max u w, w, v, u} J p ≅
      Sheaf.functorH.{max u w, w, v, u} K p :=
  sheafCohomologyIsoOfConstantSheafIsoOfAcyclic J K u
    ((lowerShriekConstantSheafIso J K u heC heD hu).app
      (AddCommGrpCat.of (ULift.{w} ℤ))) hacyclic p

end CohomologyFromAcyclicity

section LocalCohomology

variable (X : C) [u.IsContinuous J K]
  [(Over.post (X := X) u).IsContinuous (J.over X) (K.over (u.obj X))]

/-- **Restriction commutes with localization.** Restricting an abelian sheaf on the bigger site
to `(C, J)` and then to the slice over `X` is restricting it to the slice over `u(X)` and then
along `Over.post u`: both are restriction along the one functor `Over X ⥤ D`,
`(Y → X) ↦ u(Y)`. -/
theorem overPullback_comp_sheafPushforwardContinuous :
    u.sheafPushforwardContinuous AddCommGrpCat.{w} J K ⋙
        J.overPullback AddCommGrpCat.{w} X =
      K.overPullback AddCommGrpCat.{w} (u.obj X) ⋙
        (Over.post (X := X) u).sheafPushforwardContinuous AddCommGrpCat.{w}
          (J.over X) (K.over (u.obj X)) :=
  rfl

variable [HasSheafify (J.over X) AddCommGrpCat.{w}]
  [HasSheafify (K.over (u.obj X)) AddCommGrpCat.{w}]
  [HasGlobalSectionsFunctor (J.over X) AddCommGrpCat.{w}]
  [HasGlobalSectionsFunctor (K.over (u.obj X)) AddCommGrpCat.{w}]
  [((Over.post (X := X) u).sheafPushforwardContinuous AddCommGrpCat.{w}
    (J.over X) (K.over (u.obj X))).IsRightAdjoint]
  [HasExt.{max u v w} (Sheaf (J.over X) AddCommGrpCat.{w})]
  [HasExt.{max u v w} (Sheaf (K.over (u.obj X)) AddCommGrpCat.{w})]
  [HasInjectiveResolutions (Sheaf (J.over X) AddCommGrpCat.{w})]
  [HasInjectiveResolutions (Sheaf (K.over (u.obj X)) AddCommGrpCat.{w})]
  [PreservesFiniteColimits ((Over.post (X := X) u).sheafPushforwardContinuous
    AddCommGrpCat.{w} (J.over X) (K.over (u.obj X)))]
  [((Over.post (X := X) u).sheafPushforwardContinuous AddCommGrpCat.{w}
    (J.over X) (K.over (u.obj X))).PreservesInjectiveObjects]

/-- **Stacks 03YU (2): restriction from a bigger site does not change cohomology over an
object.** For every `X : C` and every degree `p`,

`H^p(C/X, g⁻¹ F) ≅ H^p(D/u(X), F)`

naturally in the abelian sheaf `F` on the bigger site `(D, K)`, where cohomology over an object
is the global cohomology of the sheaf restricted to the slice site.

This is the global comparison `sheafCohomologyIso` applied to `Over.post u`, whose two slice
sites have the terminal objects `𝟙 X` and `𝟙 u(X)`; the identification of the two ways of
restricting to the slice is `overPullback_comp_sheafPushforwardContinuous`. -/
@[stacks 03YU "cohomology over an object, at independent site and coefficient universes"]
def cohomologyOverObjectIso (p : ℕ) :
    u.sheafPushforwardContinuous AddCommGrpCat.{w} J K ⋙
        J.overPullback AddCommGrpCat.{w} X ⋙
          Sheaf.functorH.{max u v w, w, v, max u v} (J.over X) p ≅
      K.overPullback AddCommGrpCat.{w} (u.obj X) ⋙
        Sheaf.functorH.{max u v w, w, v, max u v} (K.over (u.obj X)) p :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (eqToIso (overPullback_comp_sheafPushforwardContinuous J K u X)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (sheafCohomologyIso (J.over X) (K.over (u.obj X)) (Over.post (X := X) u)
        Over.mkIdTerminal Over.mkIdTerminal (by simp) p)

end LocalCohomology

section LocalCohomologyFromAcyclicity

variable (X : C) [u.IsContinuous J K]
  [(Over.post (X := X) u).IsContinuous (J.over X) (K.over (u.obj X))]
  [HasSheafify (J.over X) AddCommGrpCat.{w}]
  [HasSheafify (K.over (u.obj X)) AddCommGrpCat.{w}]
  [HasGlobalSectionsFunctor (J.over X) AddCommGrpCat.{w}]
  [HasGlobalSectionsFunctor (K.over (u.obj X)) AddCommGrpCat.{w}]
  [((Over.post (X := X) u).sheafPushforwardContinuous AddCommGrpCat.{w}
    (J.over X) (K.over (u.obj X))).IsRightAdjoint]
  [HasExt.{max u v w} (Sheaf (J.over X) AddCommGrpCat.{w})]
  [HasExt.{max u v w} (Sheaf (K.over (u.obj X)) AddCommGrpCat.{w})]
  [HasInjectiveResolutions (Sheaf (J.over X) AddCommGrpCat.{w})]
  [HasInjectiveResolutions (Sheaf (K.over (u.obj X)) AddCommGrpCat.{w})]
  [EnoughInjectives (Sheaf (K.over (u.obj X)) AddCommGrpCat.{w})]
  [PreservesFiniteColimits ((Over.post (X := X) u).sheafPushforwardContinuous
    AddCommGrpCat.{w} (J.over X) (K.over (u.obj X)))]

/-- **Restriction from a bigger site does not change cohomology over an object, from
acyclicity.** For every `X : C` and every degree `p`,

`H^p(C/X, g⁻¹ F) ≅ H^p(D/u(X), F)`

naturally in the abelian sheaf `F` on the bigger site `(D, K)`, provided only that the
restriction to `C/X` of an injective abelian sheaf on `D/u(X)` has vanishing higher cohomology
there.

This is `Stacks.Cohomology.BiggerSiteGlobal.cohomologyOverObjectIso` with preservation of
injective objects by restriction on the slice replaced by acyclicity, exactly as
`sheafCohomologyIsoOfAcyclic` replaces it in the global statement; it is that statement applied
to `Over.post u`, whose two slice sites have the terminal objects `𝟙 X` and `𝟙 u(X)`. -/
@[stacks 03YU
  "cohomology over an object, from acyclicity of the restriction of an injective sheaf"]
def cohomologyOverObjectIsoOfAcyclic
    (hacyclic : ∀ (I : Sheaf (K.over (u.obj X)) AddCommGrpCat.{w}), Injective I → ∀ (n : ℕ)
      (a : Sheaf.H (((Over.post (X := X) u).sheafPushforwardContinuous AddCommGrpCat.{w}
        (J.over X) (K.over (u.obj X))).obj I) (n + 1)), a = 0)
    (p : ℕ) :
    u.sheafPushforwardContinuous AddCommGrpCat.{w} J K ⋙
        J.overPullback AddCommGrpCat.{w} X ⋙
          Sheaf.functorH.{max u v w, w, v, max u v} (J.over X) p ≅
      K.overPullback AddCommGrpCat.{w} (u.obj X) ⋙
        Sheaf.functorH.{max u v w, w, v, max u v} (K.over (u.obj X)) p :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (eqToIso (overPullback_comp_sheafPushforwardContinuous J K u X)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (sheafCohomologyIsoOfAcyclic (J.over X) (K.over (u.obj X)) (Over.post (X := X) u)
        Over.mkIdTerminal Over.mkIdTerminal (by simp) hacyclic p)

end LocalCohomologyFromAcyclicity

end Stacks.Cohomology.BiggerSiteGlobal

end
