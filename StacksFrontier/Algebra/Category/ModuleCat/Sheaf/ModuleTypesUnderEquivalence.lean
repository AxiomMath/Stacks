module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposEquivalencePullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackModulesComp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackFiniteType
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackLocalGeneration
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackPresentationAssembly
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Sheafification.SheafificationFromSlices
import StacksCore.Tactic.StacksAttribute

/-!
# Local conditions on sheaves of modules are intrinsic

Stacks 03DM asserts that each of the local conditions of Stacks 03DL on a sheaf of modules on a
ringed site depends only on the associated ringed topos: an equivalence of ringed topoi both
preserves and reflects it.  This file proves that for local generation by `r` sections
(03DL (4)), for being of finite type (03DL (5)) and for finite presentation (03DL (7)).

The three clauses here are the ones whose 03DO — the forward implication both directions are
built from — needs no replacement of the sites, so the two ringed topoi may live in independent
universes.  Local freeness (03DL (1)), finite local freeness (03DL (2)), local generation by
sections (03DL (3)) and quasi-coherence (03DL (6)) are proved in the same form, but only for
ringed topoi on Stacks sites, in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalTypesUnderEquivalence`: their 03DO goes
through the factorization of Stacks 03CR, which fixes the universes.  Coherence (03DL (8)) has
no 03DO at all and is proved by the route of Section 03DG, along a special cocontinuous functor
of sites, in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalTypesUnderSpecialCocontinuous`.

Each statement is an `iff`.  The forward implication is Stacks 03DO, which holds for an
arbitrary morphism of ringed topoi.  The reverse implication applies 03DO to the inverse
morphism `AlgebraicGeometry.RingedToposHom.inverse` and then transports the condition back
along `AlgebraicGeometry.RingedToposHom.pullbackModulesInverseObjIso`, the identification of
the round trip with the identity: it is the comparison of Stacks 03D8 for the composite,
followed by `AlgebraicGeometry.RingedToposHom.pullbackModulesCompInverseIso`.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.pullbackModulesInverseObjIso`: pulling a sheaf of modules
  back along an equivalence of ringed topoi and then back along its inverse returns it.

## Main results

* `Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso`,
  `Stacks.SheafOfModules.Intrinsic.isFiniteType_of_iso` and
  `Stacks.SheafOfModules.Intrinsic.isLocallyGeneratedByOnSite_of_iso`: the three conditions are
  invariant under isomorphism of sheaves of modules.
* `AlgebraicGeometry.RingedToposHom.isFinitePresentation_iff_pullbackModules`: **Stacks 03DM
  for the clause 03DL (7).**
* `AlgebraicGeometry.RingedToposHom.isFiniteType_iff_pullbackModules`: **Stacks 03DM for the
  clause 03DL (5).**
* `AlgebraicGeometry.RingedToposHom.isLocallyGeneratedByOnSite_iff_pullbackModules`:
  **Stacks 03DM for the clause 03DL (4).**

## Implementation notes

The three isomorphism-invariance statements are in the namespace
`Stacks.SheafOfModules.Intrinsic` because `Stacks.SheafOfModules.isFiniteType_of_iso` is already
taken, by a statement that assumes `HasBinaryProducts` on the site and the object, morphism and
module universes to agree; the statements here assume none of that, as the ringed-topoi
statements below cannot.

The sheafification hypotheses are asked of the *slice* sites only, for both ringed topoi, and
of the whole site only for the source.  The missing two for the target —
`HasWeakSheafify Y.J AddCommGrpCat` and `Y.J.WEqualsLocallyBijective AddCommGrpCat`, which the
reverse implication needs in order to pull back along the inverse morphism — are derived inside
the proofs from the slice ones by
`CategoryTheory.GrothendieckTopology.hasWeakSheafify_addCommGrpCat_of_over` and its companion,
so they are not assumed.  They cannot be derived for the source as well, because the pullback
functor appearing in the statement already needs them.

## References

* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules

namespace Stacks.SheafOfModules.Intrinsic

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Finite presentation is invariant under isomorphism of sheaves of modules.**  A
quasicoherent datum witnessing finite presentation is carried across by restricting the
isomorphism to each member of its covering and applying
`SheafOfModules.Presentation.ofIsIso`, which leaves the index types of the generators and of
the relations unchanged. -/
theorem isFinitePresentation_of_iso {M N : _root_.SheafOfModules.{w} R} (e : M ≅ N)
    (hM : M.IsFinitePresentation) : N.IsFinitePresentation := by
  let _ : ∀ V : C, HasSheafify (J.over V) AddCommGrpCat.{w} :=
    fun _ ↦ AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  obtain ⟨q, hq⟩ := hM.exists_quasicoherentData
  have hfin : ∀ i, ((q.presentation i).ofIsIso
      ((_root_.SheafOfModules.overFunctor R (q.X i)).mapIso e).hom).IsFinite := fun i ↦ by
    have := hq.isFinite_presentation i
    infer_instance
  exact ⟨⟨{
    I := q.I
    X := q.X
    coversTop := q.coversTop
    presentation := fun i ↦ (q.presentation i).ofIsIso
      ((_root_.SheafOfModules.overFunctor R (q.X i)).mapIso e).hom }, ⟨hfin⟩⟩⟩

/-- **Being of finite type is invariant under isomorphism of sheaves of modules.**  The local
generators data is carried across by restricting the isomorphism to each member of its
covering; `SheafOfModules.GeneratingSections.ofEpi` leaves the index type unchanged, so the
finiteness is preserved. -/
theorem isFiniteType_of_iso {M N : _root_.SheafOfModules.{w} R} (e : M ≅ N)
    (hM : M.IsFiniteType) : N.IsFiniteType := by
  obtain ⟨σ, hσ⟩ := hM.exists_localGeneratorsData
  have hfin : ∀ i : σ.I, ((σ.generators i).ofEpi
      ((_root_.SheafOfModules.overFunctor R (σ.X i)).map e.hom)).IsFiniteType := fun i ↦ by
    have := hσ.isFiniteType i
    infer_instance
  exact ⟨⟨{
    I := σ.I
    X := σ.X
    coversTop := σ.coversTop
    generators := fun i ↦
      (σ.generators i).ofEpi ((_root_.SheafOfModules.overFunctor R (σ.X i)).map e.hom) },
    ⟨hfin⟩⟩⟩

/-- **Local generation by `r` sections is invariant under isomorphism of sheaves of modules.**
The same covering works, and the generating sections are carried across by the restriction of
the isomorphism, which is an epimorphism and does not change the index type. -/
theorem isLocallyGeneratedByOnSite_of_iso {M N : _root_.SheafOfModules.{w} R} (e : M ≅ N)
    (r : ℕ) (hM : M.IsLocallyGeneratedByOnSite r) : N.IsLocallyGeneratedByOnSite r := by
  intro U
  obtain ⟨S, hS⟩ := hM U
  refine ⟨S, fun V g hg ↦ ?_⟩
  obtain ⟨σ, ⟨d⟩⟩ := hS V g hg
  exact ⟨σ.ofEpi ((_root_.SheafOfModules.overFunctor R V).map e.hom), ⟨d⟩⟩

end Stacks.SheafOfModules.Intrinsic

namespace AlgebraicGeometry.RingedToposHom

universe v u v' u' w

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : Y.C, HasWeakSheafify (Y.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : Y.C, (Y.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Pulling a sheaf of modules back along an equivalence of ringed topoi and then back along
its inverse returns it.**  The two steps are the comparison of Stacks 03D8 for the composite
`Y ⟶ X ⟶ Y` and the identification of that composite's pullback with the identity functor. -/
noncomputable def pullbackModulesInverseObjIso [HasWeakSheafify Y.J AddCommGrpCat.{w}]
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] (f : RingedToposHom X Y)
    [f.toToposHom.pushforward.IsEquivalence] [IsIso f.fSharp]
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    ((inverse f).toModulesHom.pullbackModules).obj ((f.toModulesHom.pullbackModules).obj F) ≅ F :=
  ((pullbackModulesCompIso (inverse f) f).app F).symm ≪≫
    (pullbackModulesCompInverseIso f).app F

/-- **Stacks 03DM for the clause 03DL (7): finite presentation is intrinsic.**  A sheaf of
modules on the target of an equivalence of ringed topoi is of finite presentation if and only
if its pullback is.

The forward implication is Stacks 03DO.  The reverse one applies Stacks 03DO to the inverse
equivalence and carries the conclusion back along
`AlgebraicGeometry.RingedToposHom.pullbackModulesInverseObjIso`.

For Descent, Lemma 05VG this is an **engine lemma awaiting instantiation** and carries no
`@[stacks 05VG]` attribute: 05VG asserts the clause at a comparison functor of Descent,
Proposition 03DX, and no such functor is known to satisfy
`[f.toToposHom.pushforward.IsEquivalence] [IsIso f.fSharp]`.  Instantiating it for 05VG would
need a named morphism of ringed topoi presenting the small Zariski comparison together with
proofs that its pushforward is an equivalence and its structure map an isomorphism.  See the
section at the end of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LocalTypesUnderComparison.lean`, where an
`add_to_stacks 05VG` against this declaration was retracted. -/
@[stacks 03DM "finite_presentation"]
theorem isFinitePresentation_iff_pullbackModules (f : RingedToposHom X Y)
    [f.toToposHom.pushforward.IsEquivalence] [IsIso f.fSharp]
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    F.IsFinitePresentation ↔ ((f.toModulesHom.pullbackModules).obj F).IsFinitePresentation := by
  have : HasWeakSheafify Y.J AddCommGrpCat.{w} :=
    GrothendieckTopology.hasWeakSheafify_addCommGrpCat_of_over Y.J
  have : Y.J.WEqualsLocallyBijective AddCommGrpCat.{w} :=
    GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat_of_over Y.J
  exact ⟨fun _ ↦ Stacks.Sheaves.FinitePresentation.isFinitePresentation_pullbackModules
      f.toModulesHom F,
    fun _ ↦ Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso
      (pullbackModulesInverseObjIso f F)
      (Stacks.Sheaves.FinitePresentation.isFinitePresentation_pullbackModules
        (inverse f).toModulesHom ((f.toModulesHom.pullbackModules).obj F))⟩

/-- **Stacks 03DM for the clause 03DL (5): being of finite type is intrinsic.**  A sheaf of
modules on the target of an equivalence of ringed topoi is of finite type if and only if its
pullback is.

For Descent, Lemma 05VG this is an **engine lemma awaiting instantiation** and carries no
`@[stacks 05VG]` attribute, for the reason given on
`AlgebraicGeometry.RingedToposHom.isFinitePresentation_iff_pullbackModules` above: 05VG asserts
the clause at a comparison functor of Descent, Proposition 03DX, and no such functor is known
to satisfy this declaration's two instance hypotheses.  Instantiating it would need a named
morphism of ringed topoi presenting the small Zariski comparison together with proofs of
those two facts about it. -/
@[stacks 03DM "finite_type"]
theorem isFiniteType_iff_pullbackModules (f : RingedToposHom X Y)
    [f.toToposHom.pushforward.IsEquivalence] [IsIso f.fSharp]
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    F.IsFiniteType ↔ ((f.toModulesHom.pullbackModules).obj F).IsFiniteType := by
  have : HasWeakSheafify Y.J AddCommGrpCat.{w} :=
    GrothendieckTopology.hasWeakSheafify_addCommGrpCat_of_over Y.J
  have : Y.J.WEqualsLocallyBijective AddCommGrpCat.{w} :=
    GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat_of_over Y.J
  refine ⟨fun hF ↦ ?_, fun hP ↦ ?_⟩
  · exact Stacks.Sheaves.FiniteType.pullbackModules_isFiniteType f.toModulesHom F hF
  · exact Stacks.SheafOfModules.Intrinsic.isFiniteType_of_iso
      (pullbackModulesInverseObjIso f F)
      (Stacks.Sheaves.FiniteType.pullbackModules_isFiniteType (inverse f).toModulesHom
        ((f.toModulesHom.pullbackModules).obj F) hP)

/-- **Stacks 03DM for the clause 03DL (4): local generation by `r` sections is intrinsic.**  A
sheaf of modules on the target of an equivalence of ringed topoi is locally generated by `r`
sections if and only if its pullback is.

For Descent, Lemma 05VG this is an **engine lemma awaiting instantiation** and carries no
`@[stacks 05VG]` attribute, for the reason given on
`AlgebraicGeometry.RingedToposHom.isFinitePresentation_iff_pullbackModules` above: 05VG asserts
the clause at a comparison functor of Descent, Proposition 03DX, and no such functor is known
to satisfy this declaration's two instance hypotheses.  Instantiating it would need a named
morphism of ringed topoi presenting the small Zariski comparison together with proofs of
those two facts about it. -/
@[stacks 03DM "locally_generated_r"]
theorem isLocallyGeneratedByOnSite_iff_pullbackModules (f : RingedToposHom X Y)
    [f.toToposHom.pushforward.IsEquivalence] [IsIso f.fSharp]
    (F : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)) (r : ℕ) :
    F.IsLocallyGeneratedByOnSite r ↔
      ((f.toModulesHom.pullbackModules).obj F).IsLocallyGeneratedByOnSite r := by
  have : HasWeakSheafify Y.J AddCommGrpCat.{w} :=
    GrothendieckTopology.hasWeakSheafify_addCommGrpCat_of_over Y.J
  have : Y.J.WEqualsLocallyBijective AddCommGrpCat.{w} :=
    GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat_of_over Y.J
  refine ⟨fun hF ↦ ?_, fun hP ↦ ?_⟩
  · exact Stacks.Sheaves.LocalGeneration.pullbackModules_isLocallyGeneratedByOnSite
      f.toModulesHom F r hF
  · exact Stacks.SheafOfModules.Intrinsic.isLocallyGeneratedByOnSite_of_iso
      (pullbackModulesInverseObjIso f F) r
      (Stacks.Sheaves.LocalGeneration.pullbackModules_isLocallyGeneratedByOnSite
        (inverse f).toModulesHom ((f.toModulesHom.pullbackModules).obj F) r hP)

end AlgebraicGeometry.RingedToposHom

end
