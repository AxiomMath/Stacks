module

public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleQuasicoherent
import StacksFrontier.AlgebraicGeometry.Spaces.ZeroSchemeEffectiveCartier

/-!
# Trivializations of a module on an étale chart of an algebraic space

Let `X` be an algebraic space over a scheme `S`.  An invertible `𝒪_X`-module is, by Stacks 0B8Q
on the small étale site, isomorphic to the structure sheaf over the members of a covering sieve of
every étale chart; arguments that read a global statement off such a trivialization are frequent
(Stacks 0846 (3) and (4), Stacks 083C, Stacks 0847), and they all need the same three things: the
covering sieve with its trivializations, the generator which the trivialization exhibits, and the
fact that every section below the chart is a multiple of that generator.  This file provides those
three at one spelling.

## Main definitions

* `AlgebraicGeometry.Space.unitIsoGenerator` is the section of `M` over a chart which a
  trivialization of `M` there exhibits: the image of the unit section.

## Main results

* `AlgebraicGeometry.Space.exists_covering_unitIso_of_isInvertible`: **an invertible
  `𝒪_X`-module is trivial over every member of a covering sieve of every étale chart.**
* `AlgebraicGeometry.Space.unitIso_app_one`: on a chart below the trivializing chart the
  trivialization takes the unit section to the restriction of the generator.
* `AlgebraicGeometry.Space.exists_smul_unitIsoGenerator`: **every section of a trivialized module
  over a chart below the trivializing chart is a multiple of the restricted generator.**
* `AlgebraicGeometry.Space.restrictₛₗ_id_apply`: restriction of a section along the identity of a
  chart is the section.

## Implementation notes

The charts here are objects of the small étale site, `AlgebraicGeometry.Space.SmallEtale`, and the
structure sheaf is `AlgebraicGeometry.Space.structureRingSheaf`, which is indexed by the small
étale topology.  That choice is forced, and is the reason this file exists.  The small étale
ringed site has `AlgebraicGeometry.Space.SmallEtale` as its underlying category, so an étale chart
is also an object of `(smallEtaleRingedSite B S hS X.1 X.2).C` and the two types are
definitionally equal — but `CategoryTheory.Over` finds its category instance only at the first
spelling, so a *statement* about the slice site written with a chart of the second type is not
type-correct at `implicit` transparency, and `rw` into it fails even though the statement
elaborates.  Spelling the slice as `(structureRingSheaf B S hS X).over U` with
`U : SmallEtale B S hS X.1` avoids that, and it remains interoperable with the ringed-site
spelling of `AlgebraicGeometry.Space.unitIsoRestrict` and
`AlgebraicGeometry.Space.exists_isRegular_span_definingIdealAt_of_unitIso`, which accept these
trivializations as they stand.

The covering sieve comes from `Stacks.SheafOfModules.locallyOnCovering_nonempty_over_iso_unit`
rather than from `AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank`: the former already
delivers a sieve with a trivialization over *every* arrow in it, so no covering family has to be
decomposed and no colimit cofan has to be converted into an isomorphism.  Only the local-unit half
of local ringedness of the small étale site is used, through
`AlgebraicGeometry.Space.smallEtaleRingedSite_isLocallyRinged`.

`restrictₛₗ_id_apply` repeats `Stacks.PresheafOfModules.InternalHom.restrictₛₗ_id`, which cannot
be used here: that statement is for a presheaf of modules whose sections live in `max u v`, the
universe of the objects of the site, whereas the sections of an `𝒪_X`-module live one universe
below the objects of the small étale site.

## References

* [Stacks Project, Tag 0B8Q](https://stacks.math.columbia.edu/tag/0B8Q)
* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-! ### Restriction along an identity -/

/-- Restriction of a section of an `𝒪_X`-module along the identity of an étale chart is the
section. -/
theorem restrictₛₗ_id_apply (M : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (U : SmallEtale B S hS X.1) (x : M.val.obj (op U)) :
    M.val.restrictₛₗ (𝟙 U).op x = x := by
  simp only [PresheafOfModules.restrictₛₗ_apply]
  exact congrFun (congrArg (fun φ => (ModuleCat.Hom.hom φ).toFun) (M.val.map_id (op U))) x

/-! ### The trivializing covering sieve of an invertible module -/

/-- **Stacks 0B8Q on the small étale site: an invertible `𝒪_X`-module is trivial over every
member of a covering sieve of every étale chart.**  Only the local-unit half of local ringedness
of the small étale site is used. -/
theorem exists_covering_unitIso_of_isInvertible
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (hM : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property M)
    (U : SmallEtale B S hS X.1) :
    ∃ T : Sieve U, T ∈ SmallEtale.topology B S hS X.1 U ∧
      ∀ ⦃V : SmallEtale B S hS X.1⦄ (g : V ⟶ U), T.arrows g →
        Nonempty (SheafOfModules.unit ((structureRingSheaf B S hS X).over V) ≅ M.over V) := by
  have hweak : HasWeakSheafify (smallEtaleRingedSite B S hS X.1 X.2).J AddCommGrpCat.{u} :=
    inferInstanceAs (HasWeakSheafify (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u})
  have hloc : (smallEtaleRingedSite B S hS X.1 X.2).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstanceAs ((SmallEtale.topology B S hS X.1).WEqualsLocallyBijective AddCommGrpCat.{u})
  have hinv : Stacks.SheafOfModules.IsInvertible
      (smallEtaleRingedSite B S hS X.1 X.2).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property M :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hM
  obtain ⟨T, hT, hiso⟩ := Stacks.SheafOfModules.locallyOnCovering_nonempty_over_iso_unit
    (smallEtaleRingedSite B S hS X.1 X.2).O (structureRingSheaf B S hS X).property M
    (smallEtaleRingedSite_isLocallyRinged B S hS X.1 X.2).2 U
  refine ⟨T, hT, ?_⟩
  intro V g hg
  exact ⟨(hiso g hg).some.symm⟩

/-! ### The generator exhibited by a trivialization -/

variable (M : SheafOfModules.{u} (structureRingSheaf B S hS X)) (U : SmallEtale B S hS X.1)
    (e : SheafOfModules.unit ((structureRingSheaf B S hS X).over U) ≅ M.over U)

/-- The section of `M` over a chart which a trivialization of `M` there exhibits: the image of the
unit section. -/
def unitIsoGenerator : M.val.obj (op U) :=
  (e.hom.val.app (op (Over.mk (𝟙 U)))).hom
    (1 : ToType ((structureRingSheaf B S hS X).obj.obj (op U)))

/-- **On a chart below the trivializing chart the trivialization takes the unit section to the
restriction of the generator**, because it is a morphism of sheaves of modules and the unit
section restricts to the unit section. -/
theorem unitIso_app_one (W : SmallEtale B S hS X.1) (f : W ⟶ U) :
    (e.hom.val.app (op (Over.mk f))).hom
        (1 : ToType ((structureRingSheaf B S hS X).obj.obj (op W))) =
      M.val.restrictₛₗ f.op (unitIsoGenerator B S hS X M U e) := by
  set hk : (op (Over.mk (𝟙 U)) : (Over U)ᵒᵖ) ⟶ op (Over.mk f) :=
    (Over.homMk f (Category.comp_id f) : (Over.mk f : Over U) ⟶ Over.mk (𝟙 U)).op with hkdef
  have hone : (SheafOfModules.unit ((structureRingSheaf B S hS X).over U)).val.map hk
        (1 : ToType ((structureRingSheaf B S hS X).obj.obj (op U))) =
      (1 : ToType ((structureRingSheaf B S hS X).obj.obj (op W))) :=
    PresheafOfModules.unit_map_one _ hk
  have hnat := PresheafOfModules.naturality_apply e.hom.val hk
    (1 : ToType ((structureRingSheaf B S hS X).obj.obj (op U)))
  rw [hone] at hnat
  exact hnat

/-- **Every section of a trivialized module over a chart below the trivializing chart is a
multiple of the restricted generator**: it is the image of a regular function under the
trivialization, and the trivialization is linear. -/
theorem exists_smul_unitIsoGenerator (W : SmallEtale B S hS X.1) (f : W ⟶ U)
    (t : M.val.obj (op W)) :
    ∃ r : ToType ((structureRingSheaf B S hS X).obj.obj (op W)),
      t = r • M.val.restrictₛₗ f.op (unitIsoGenerator B S hS X M U e) := by
  set r : ToType ((structureRingSheaf B S hS X).obj.obj (op W)) :=
    (e.inv.val.app (op (Over.mk f))).hom t with hr
  refine ⟨r, ?_⟩
  have hinv : (e.hom.val.app (op (Over.mk f))).hom r = t :=
    congrArg (fun φ => (φ.val.app (op (Over.mk f))).hom t) e.inv_hom_id
  have hsymm : (M.over U).unitHomEquiv.symm ((M.over U).unitHomEquiv e.hom) = e.hom :=
    (M.over U).unitHomEquiv.symm_apply_apply e.hom
  have hval := unitHomEquiv_symm_app_apply ((structureRingSheaf B S hS X).over U) (M.over U)
    ((M.over U).unitHomEquiv e.hom) (Over.mk f) r
  rw [hsymm, hinv] at hval
  refine hval.trans (congrArg (fun z => r • z) ?_)
  have h1 : ((M.over U).unitHomEquiv e.hom).eval (op (Over.mk f)) =
      (e.hom.val.app (op (Over.mk f))).hom
        (1 : ToType ((structureRingSheaf B S hS X).obj.obj (op W))) :=
    SheafOfModules.unitHomEquiv_apply_coe (M.over U) e.hom (op (Over.mk f))
  exact h1.trans (unitIso_app_one B S hS X M U e W f)

end AlgebraicGeometry.Space

end
