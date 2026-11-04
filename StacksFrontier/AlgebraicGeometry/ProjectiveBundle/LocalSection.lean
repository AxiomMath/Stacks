module

public import StacksFrontier.AlgebraicGeometry.ProjF1DegreeOneChart.Relative
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocalQuotientDatum
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumExists
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TrivializedQuotient
public import StacksFrontier.AlgebraicGeometry.RelativeProj.MappingInSheafGraded
public import StacksFrontier.AlgebraicGeometry.SymmetricDehomogenize.Basic

/-!
# A local section of a projective bundle from an invertible quotient

Let `X` be a scheme, `F` a quasi-coherent `𝒪_X`-module, `q : F ⟶ L` a surjection onto an
invertible module and `π : 𝐏(F) ⟶ X` the projection of the projective bundle. **This file builds,
over every affine open of `X` on which `L` is trivial and `q` is surjective on sections, a
morphism `V ⟶ 𝐏(F)` lying over the inclusion of `V`** — that is, a section of `π` over `V`.

This is the inverse direction of Tag 0B3V's bijection, carried out locally. It is the first point
at which the whole chain of the route composes, so the chain is recorded here in one place:

1. `Stacks.RelativeProj.trivializedQuotientHom` turns `(q, trivialization)` into
   `κ : F ⟶ (V.ι)_*𝒪_V`;
2. `Stacks.SymmetricDehomogenize.dehomogenize` turns `κ` into a ring homomorphism
   `ψ : Γ(V, Sym F) ⟶ Γ(V, 𝒪)` out of the graded ring of homogeneous sections of `Sym F`;
3. `Stacks.RelativeProj.exists_app_trivializedQuotientHom_eq_one` and
   `Stacks.SymmetricDehomogenize.dehomogenize_of_one` make one degree-one homogeneous section
   invertible under `ψ`, which by
   `Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.map_irrelevant_eq_top_of_isUnit` is the only
   hypothesis `AlgebraicGeometry.Proj.fromOfGlobalSections` asks for;
4. `Stacks.SymmetricDehomogenize.dehomogenize_strHom_app` is the degree-zero clause, and
   `Stacks.AlgebraicGeometry.RelativeProj.fromOfIsUnit_comp_projInclusionToOpen` turns it into
   the statement that the classified morphism lies over `V` **on the nose**, not merely over the
   base;
5. the chart of the relative `Proj` and `Stacks.RelativeProj.bundlePresentationIso` carry the
   result into `𝐏(F)`.

## Main definitions

* `Stacks.RelativeProj.preimageSelfTopRingHom`: the identification
  `Γ(V, (V.ι) ⁻¹ V) ≅ Γ(V, ⊤)`, as a ring homomorphism. It is the `φ` the dehomogenization needs,
  and it is an identification and not a choice: the two opens are equal.

## Main results

* `Stacks.RelativeProj.appLE_self_top_eq_topIso_inv`: the structure map of `V.ι` over `V`,
  restricted to all of `V`, is `AlgebraicGeometry.Scheme.Opens.topIso`. This is what matches the
  degree-zero clause of the dehomogenization to the degree-zero hypothesis of the chart.
* `Stacks.RelativeProj.exists_hom_projectiveBundle_of_trivializing`: **the local section**, over
  an affine open trivializing `L` on which `q` is surjective on sections.
* `Stacks.RelativeProj.exists_affineOpen_hom_projectiveBundle`: the same with the open produced,
  so every point of `X` has a neighbourhood carrying a section of `π`.

## Implementation notes

**What this is not.** A section of `π` over `X` is not obtained here. Two things are still owed:
the local sections of
`Stacks.RelativeProj.exists_affineOpen_hom_projectiveBundle` must be *glued*, which needs them to
agree on overlaps — the uniqueness half of Tag 01NA read through the chart — and the glued section
must be shown to *classify* `q`, that is, its pullback of the tautological twist must be
identified with `L` carrying the pulled-back tautological map to `q`. Neither is done here, and
together they are what
`Stacks.RelativeProj.TautologicalDatum.IsUniversal.exists_classifies` asks for.

**The existential, rather than a named morphism.** The morphism is completely explicit — it is
the term in the proof — but it depends on a choice of trivialization and of a lift of the unit
section, neither of which is canonical. A named definition would have to carry both choices as
arguments, and the consumer (a gluing argument) will re-choose them per cover member anyway; so
the statement is an existential, as `Stacks.RelativeProj.exists_affineOpen_trivializing_surjective`
already is.

**Why `bundlePresentationIso` appears.** The route reaches the relative `Proj` of the
`SheafGradedAlgebra` presentation of `Sym F`, and Tag 0B3V's bijection is stated for
`Stacks.RelativeProj.projectiveBundle`. The comparison between the two presentations is the
existing `Stacks.RelativeProj.bundlePresentationIso`, which the tautological datum of
`Stacks.RelativeProj.tautologicalDatum` is itself built from — so using it here introduces no
comparison that the datum does not already contain, and the later identification of the pullback
of the twist will be stated against the same choice.

No `@[stacks]` attribute is attached. Tag 0B3V is the bijection between the sections of `π` and
the invertible quotients of `F`; a section over one open of the base, with no statement about
which quotient it classifies, is not a covering part of it.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01NA](https://stacks.math.columbia.edu/tag/01NA)
* [Stacks Project, Tag 01NS](https://stacks.math.columbia.edu/tag/01NS)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
open Stacks.AlgebraicGeometry.ProjF1Dehomogenization
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.SymGraded

universe u

namespace Stacks.RelativeProj

variable {X : Scheme.{u}} {F L : X.Modules} [F.IsQuasicoherent] (V : X.Opens)

/-- **The identification `Γ(V, (V.ι) ⁻¹ V) ≅ Γ(V, ⊤)`, as a ring homomorphism.** The inverse
image of `V` under its own inclusion is all of `V`, so this is the restriction map between two
equal opens. It is the `φ` out of which `Stacks.SymmetricDehomogenize.dehomogenize` builds a ring
map to the global sections of `V`. -/
public def preimageSelfTopRingHom :
    V.toScheme.ringCatSheaf.obj.obj (op (V.ι ⁻¹ᵁ V)) →+* Γ(V.toScheme, ⊤) :=
  (V.toScheme.presheaf.map
    (homOfLE (by simp : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V)).op).hom

/-- **The structure map of the inclusion of `V`, from `V` to all of `V`, is
`AlgebraicGeometry.Scheme.Opens.topIso`.** Both are the restriction map of `X` between the two
equal opens `V` and `V.ι ''ᵁ ⊤`, so this is `Subsingleton.elim` in the poset of opens.

This identity is what matches the degree-zero clause of the dehomogenization, which is stated in
terms of the structure map of the morphism, to the degree-zero hypothesis of
`Stacks.AlgebraicGeometry.RelativeProj.fromOfGlobalSections_comp_projInclusionToOpen`, which is
stated in terms of `topIso`. -/
public theorem appLE_self_top_eq_topIso_inv :
    V.ι.appLE V ⊤ (by simp) = V.topIso.inv := by
  rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
  exact congrArg X.presheaf.map (Subsingleton.elim _ _)

/-- **A section of `π : 𝐏(F) ⟶ X` over an affine open trivializing the quotient.** Let
`q : F ⟶ L` be a map of `𝒪_X`-modules, `V` an affine open of `X` on which `L` is trivial and over
which `q` is surjective on sections. Then there is a morphism `V ⟶ 𝐏(F)` whose composite with the
projection is the inclusion of `V`.

Neither invertibility of `L` nor surjectivity of `q` as a map of sheaves is used: what the
construction consumes is the trivialization and the surjectivity on sections over `V`, which is
what `Stacks.RelativeProj.exists_affineOpen_trivializing_surjective` produces from them.

This is the inverse direction of Tag 0B3V's bijection over one member of a cover; see the
implementation notes for what gluing it still needs. -/
public theorem exists_hom_projectiveBundle_of_trivializing (hV : IsAffineOpen V) (q : F ⟶ L)
    (e : L.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V))
    (hq : Function.Surjective (q.val.app (op V))) :
    ∃ τ : V.toScheme ⟶ projectiveBundle X F, τ ≫ projectiveBundleToBase X F = V.ι := by
  set hqc := isQuasicoherentPieces_of_isQuasicoherent F
  set A := schemeSheafGradedAlgebra F hqc
  set κ := trivializedQuotientHom V q e
  set ψ := Stacks.SymmetricDehomogenize.dehomogenize V.ι F κ V (preimageSelfTopRingHom V) hqc
  -- A section of `F` over `V` that `κ` carries to the unit section, …
  obtain ⟨m, hm⟩ := exists_app_trivializedQuotientHom_eq_one V q e hq
  -- … read as a degree-one homogeneous section of `Sym F`, …
  set r := DirectSum.of (A.sectionPieces V) 1
    ((symmetricAlgebraGen X F).val.app (op V) m)
  have hr : r ∈ A.grading V 1 := SheafGradedAlgebra.of_mem_grading A V _
  -- … whose dehomogenization is the unit, so the irrelevant ideal's image is everything.
  have hval : ψ r = 1 :=
    (Stacks.SymmetricDehomogenize.dehomogenize_of_one V.ι F κ V
        (preimageSelfTopRingHom V) hqc m).trans
      ((congrArg (fun z => preimageSelfTopRingHom V z) hm).trans
        (map_one (preimageSelfTopRingHom V)))
  have hu : IsUnit (ψ r) := hval ▸ isUnit_one
  -- The degree-zero clause places the classified morphism over `V` on the nose.
  have hψ0 : ∀ x : Γ(X, V), ψ (A.strHom V x) =
      (V.topIso.inv ≫ (𝟙 V.toScheme : V.toScheme ⟶ V.toScheme).appTop).hom x := by
    intro x
    refine (Stacks.SymmetricDehomogenize.dehomogenize_strHom_app V.ι F κ V
      (preimageSelfTopRingHom V) hqc x).trans ?_
    rw [AlgebraicGeometry.Scheme.Hom.id_appTop, Category.comp_id,
      ← appLE_self_top_eq_topIso_inv V]
    rfl
  have hchart := Stacks.AlgebraicGeometry.RelativeProj.fromOfIsUnit_comp_projInclusionToOpen
    A hV (𝟙 V.toScheme : V.toScheme ⟶ V.toScheme) ψ Nat.one_pos hr hu hψ0
  refine ⟨Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.fromOfIsUnit (A.grading V) ψ
      Nat.one_pos hr hu ≫ (symGradedBundle F).chart V hV ≫
      (bundlePresentationIso F).hom, ?_⟩
  rw [Category.assoc, Category.assoc, bundlePresentationIso_hom_comp_toBase,
    ((symGradedBundle F).chart_isPullback V hV).w, ← Category.assoc, hchart, Category.id_comp]

/-- **Every point of `X` has an affine open neighbourhood carrying a section of
`π : 𝐏(F) ⟶ X`.** The cover of
`Stacks.RelativeProj.exists_affineOpen_trivializing_surjective` supplies, at each point, an
affine open on which `L` is trivial and `q` is surjective on sections, which is exactly what
`Stacks.RelativeProj.exists_hom_projectiveBundle_of_trivializing` consumes. -/
public theorem exists_affineOpen_hom_projectiveBundle
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (q : F ⟶ L) [Epi q] (p : X) :
    ∃ W : X.affineOpens, p ∈ W.1 ∧
      ∃ τ : W.1.toScheme ⟶ projectiveBundle X F,
        τ ≫ projectiveBundleToBase X F = W.1.ι := by
  obtain ⟨W, hpW, ⟨e⟩, hsurj⟩ := exists_affineOpen_trivializing_surjective q p
  exact ⟨W, hpW, exists_hom_projectiveBundle_of_trivializing W.1 W.2 q e hsurj⟩

end Stacks.RelativeProj

end
