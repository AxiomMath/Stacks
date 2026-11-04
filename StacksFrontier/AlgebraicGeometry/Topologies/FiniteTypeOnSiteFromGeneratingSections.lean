module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackFiniteType
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeFromGlobalGenerators
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentFromCoherence
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite type on a site from generating sections, and its stability under pullback

Stacks 03DL(5), local generation by finitely many global sections, is recorded in this tree
twice: categorically, as `SheafOfModules.IsFiniteTypeOnSite`, whose witness on each member of a
covering is a finite coproduct of copies of the structure sheaf mapping onto the module; and
sectionwise, as Mathlib's `SheafOfModules.IsFiniteType`, whose witness is a family of generating
global sections indexed by a finite type.
`Stacks.SheafOfModules.isFiniteType_of_isFiniteTypeOnSite` descends the first to the second.
This file supplies the ascent, and uses it to put Stacks 03DO
for the clause 03DL(5) — stability of finite type under pullback along a morphism of ringed
topoi — into the categorical form, which is the one the support statements of Stacks 07TZ
consume.

The ascent is the composite of two facts of the library.  A family of generating sections spans the
module locally, by `Stacks.Sheaves.LocalGeneration.generatingSections_locally_span`; and a
family of sections which spans locally presents the module as a quotient of a finite coproduct
of copies of the structure sheaf, by `SheafOfModules.epi_powDesc`.  That coproduct is
`SheafOfModules.liftPow`, formed in the universe `max u v w` in which the universe-lifted
structure sheaf lives, which is exactly where `SheafOfModules.HasFiniteGlobalGenerators` asks
for it.

## Main results

* `Stacks.SheafOfModules.hasFiniteGlobalGenerators_of_sections`: finitely many sections which
  span locally exhibit finitely many global generators in the sense of Stacks 03DE(5).
* `Stacks.SheafOfModules.hasFiniteGlobalGenerators_of_generatingSections`: the same from
  Mathlib's `SheafOfModules.GeneratingSections` with a finite index type.  This is the converse
  of `Stacks.SheafOfModules.exists_sections_of_hasFiniteGlobalGenerators`.
* `Stacks.SheafOfModules.isFiniteTypeOnSite_of_locally_finite_generators`: the local criterion
  for `SheafOfModules.IsFiniteTypeOnSite`, the counterpart of
  `Stacks.SheafOfModules.isFiniteType_of_locally_finite_generators`.
* `Stacks.Sheaves.FiniteType.pullbackModules_isFiniteTypeOnSite`: **Stacks 03DO for the clause
  03DL(5)**, in the categorical form.

## Implementation notes

The covering demanded by `SheafOfModules.IsFiniteTypeOnSite` is a `CategoryTheory.Sieve.ofArrows`
of a family indexed by a type in `Type (max u v)`, whereas the local criterion is given a
`CategoryTheory.GrothendieckTopology.Cover`.  The family used is the family of *all* arrows of
that cover, indexed by their sources; the sieve it generates contains the cover, so it covers.
No arrow of the cover is discarded, so no choice is made.

`Stacks.Sheaves.FiniteType.pullbackModules_isFiniteTypeOnSite` runs the proof of
`Stacks.Sheaves.FiniteType.pullbackModules_isFiniteType` again rather than deducing one from the
other: the two halves of that proof — the inverse image and the extension of scalars — both
produce and consume the per-object sectionwise data, and only the final assembly differs, so
reusing it costs one line and deducing the categorical form from the sectionwise one would need
to re-extract a covering of each object from a covering of the terminal object.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace Stacks.SheafOfModules

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- **Finitely many locally spanning sections give finitely many global generators.**  The
presenting morphism is `SheafOfModules.powDesc`, out of the finite coproduct
`SheafOfModules.liftPow` of copies of the universe-lifted structure sheaf, and it is an
epimorphism by `SheafOfModules.epi_powDesc`.

This is the shape of Stacks 03DE(5) that `SheafOfModules.HasFiniteGlobalGenerators` records. -/
theorem hasFiniteGlobalGenerators_of_sections (N : SheafOfModules.{w} R) {n : ℕ}
    (σ : Fin n → N.sections)
    (hgen : ∀ (V : C) (x : N.val.obj (op V)), ∃ T : Sieve V, T ∈ J V ∧
      ∀ ⦃B : C⦄ (g : B ⟶ V), T.arrows g → ∃ c : Fin n → R.obj.obj (op B),
        ∑ i, c i • (σ i).eval (op B) = N.val.map g.op x) :
    N.HasFiniteGlobalGenerators := by
  have hsh : HasSheafify J AddCommGrpCat.{max u v w} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v w, v, u} J
  have hlb : J.WEqualsLocallyBijective AddCommGrpCat.{max u v w} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v w, u, v} J
  exact ⟨n, liftPow R n, biproduct.ι (fun _ : Fin n => liftUnit R),
    ⟨biproduct.isColimit _⟩, powDesc N σ, epi_powDesc N σ hgen⟩

/-- **Mathlib's generating sections, with a finite index type, give finitely many global
generators.**  The index type is transported to `Fin n` and the sections are shown to span
locally by `Stacks.Sheaves.LocalGeneration.generatingSections_locally_span`.

This is the converse of `Stacks.SheafOfModules.exists_sections_of_hasFiniteGlobalGenerators`. -/
theorem hasFiniteGlobalGenerators_of_generatingSections [HasWeakSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] (N : SheafOfModules.{w} R)
    (σ : N.GeneratingSections) (hσ : σ.IsFiniteType) :
    N.HasFiniteGlobalGenerators := by
  have hfin : Finite σ.I := hσ.finite
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ.I
  refine hasFiniteGlobalGenerators_of_sections N (fun i => σ.s (e.symm i)) ?_
  intro V x
  refine ⟨Stacks.Sheaves.LocalGeneration.spanSieve N
      (fun i => (σ.s (e.symm i)).val (op V)) x,
    Stacks.Sheaves.LocalGeneration.generatingSections_locally_span N σ n e V x, ?_⟩
  intro B g hg
  obtain ⟨c, hc⟩ := hg
  refine ⟨c, ?_⟩
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hc
  exact congrArg (fun y => c i • y)
    ((σ.s (e.symm i)).property g.op).symm

/-- **The local criterion for finite type on a site.**  A sheaf of modules generated by finitely
many global sections on each member of some covering of each object of the site satisfies
`SheafOfModules.IsFiniteTypeOnSite`.

This is the categorical counterpart of
`Stacks.SheafOfModules.isFiniteType_of_locally_finite_generators`; the covering family is the
family of all arrows of the given cover, indexed by their sources. -/
theorem isFiniteTypeOnSite_of_locally_finite_generators
    [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{w}]
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (M : SheafOfModules.{w} R)
    (hM : ∀ U : C, ∃ T : J.Cover U, ∀ (V : C) (g : V ⟶ U), T g →
      ∃ σ : (M.over V).GeneratingSections, σ.IsFiniteType) :
    M.IsFiniteTypeOnSite := by
  refine ⟨fun U => ?_⟩
  obtain ⟨T, hT⟩ := hM U
  refine ⟨Σ V : C, {g : V ⟶ U // T.1 g}, fun i => i.1, fun i => i.2.1, ?_, fun i => ?_⟩
  · refine J.superset_covering (fun Z g hg => ?_) T.2
    exact (Sieve.mem_ofArrows_iff _ _ _).2 ⟨⟨Z, g, hg⟩, 𝟙 Z, (Category.id_comp g).symm⟩
  · obtain ⟨σ, hσ⟩ := hT i.1 i.2.1 i.2.2
    exact hasFiniteGlobalGenerators_of_generatingSections (M.over i.1) σ hσ

end Stacks.SheafOfModules

namespace Stacks.Sheaves.FiniteType

open Stacks.Sheaves.LocalGeneration Stacks.Topos

universe v u v' u' w w'

/-- **Stacks 03DO for the clause 03DL(5), in the categorical form: pullback preserves finite
type on the site.**  The pullback `f^*F = O_C ⊗_{f⁻¹O_D} f⁻¹F` of Stacks 03D6(2) of a sheaf of
`O_D`-modules satisfying `SheafOfModules.IsFiniteTypeOnSite` along a morphism of ringed topoi
again satisfies it.

The two factors are the same as for
`Stacks.Sheaves.FiniteType.pullbackModules_isFiniteType`: the inverse image produces a covering
of each object of the source site carrying finitely many generating sections of `f⁻¹F`, and
extension of scalars carries those sections across `f⁻¹O_D ⟶ O_C`.  Only the assembly differs,
and it is `Stacks.SheafOfModules.isFiniteTypeOnSite_of_locally_finite_generators`. -/
theorem pullbackModules_isFiniteTypeOnSite
    {X : AlgebraicGeometry.RingedTopos.{v, u, w}}
    {Y : AlgebraicGeometry.RingedTopos.{v', u', w}}
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
    (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (hF : F.IsFiniteTypeOnSite) :
    ((f.pullbackModules).obj F).IsFiniteTypeOnSite := by
  have : F.IsFiniteType := Stacks.SheafOfModules.isFiniteType_of_isFiniteTypeOnSite F hF
  have hP := exists_cover_finite_generators_inverseImage f.toToposHom
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
    (ToposPullback.pullbackModule X.J Y.J f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) F
  exact Stacks.SheafOfModules.isFiniteTypeOnSite_of_locally_finite_generators _
    (extendScalars_exists_finite_generators (RingedToposModules.fSharpCommRing f)
      (ToposPushforward.inverseImageRingSheaf f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property _ hP)

end Stacks.Sheaves.FiniteType

end
