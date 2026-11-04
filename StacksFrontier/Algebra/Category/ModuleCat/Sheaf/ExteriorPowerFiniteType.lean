module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentAlgebras
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ConstantRank
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialForms

/-!
# Finiteness of the exterior powers of a sheaf of modules

Let `(X, 𝒪_X)` be a ringed space and `F` a sheaf of `𝒪_X`-modules of finite presentation. Then
every exterior power `⋀ⁿ F` is again of finite presentation, hence of finite type and
quasi-coherent; and on a locally Noetherian scheme every exterior power of a coherent sheaf of
modules is coherent.

The mathematics is Tag 01CJ, which is already available here: an exact presentation of `F` by
free modules over an open presents `⋀ⁿ F` over that *same* open, by free modules whose index
types are built from the index types of the given presentation
(`Stacks.SheafOfModules.exists_free_exteriorPower_presentation`). When the given presentation is
finite — finitely many generators and finitely many relations — the index types produced for
`⋀ⁿ F` are a finite product and a set of `n`-element subsets of a finite set, so they are finite
as well. The content of this file is therefore the bookkeeping of finiteness along the
constructions by which
`Stacks.SheafOfModules.nonempty_presentation_exteriorPower_over` builds a presentation of
`(⋀ⁿ F)|_U` out of one of `F|_U`: the presentation of a cokernel of free modules
(`SheafOfModules.presentationOfIsCokernelFree`), transport along an isomorphism
(`Stacks.SheafOfModules.presentationOfIso`), transport along a colimit-preserving change of site
(`SheafOfModules.Presentation.map`), the composite of the last two which crosses to an open
subspace (`Stacks.SheafOfModules.presentationOfOpenSubspaceIso`), and the presentations of a free
module and of the structure sheaf (`Stacks.SheafOfModules.presentationFree`, `presentationUnit`).

## Main results

* `Stacks.SheafOfModules.exists_isFinite_presentation_exteriorPower`: a finite presentation of a
  sheaf of modules on a ringed space gives a finite presentation of each of its exterior powers.
* `Stacks.SheafOfModules.exists_isFinite_presentation_exteriorPower_over`: the same over an open,
  for the restriction of an exterior power computed on the whole space.
* `Stacks.SheafOfModules.isFinitePresentation_exteriorPower`: **clause (3) of Tag 01CK for the
  exterior powers** — each exterior power of a sheaf of modules of finite presentation on a
  ringed space is of finite presentation; and
  `Stacks.SheafOfModules.isFiniteType_exteriorPower` for the finite-type consequence.
* `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_exteriorPower`,
  `isFiniteType_exteriorPower`, `isFiniteType_exteriorPower_of_isCoherent`,
  `isQuasicoherent_exteriorPower` and `isQuasicoherent_exteriorPower_of_isCoherent`: the
  scheme-level forms, for `AlgebraicGeometry.Scheme.Modules.exteriorPower`, all recorded as
  instances.
* `AlgebraicGeometry.Scheme.Modules.isCoherent_exteriorPower`: **on a locally Noetherian scheme
  every exterior power of a coherent sheaf of modules is coherent.**

## Implementation notes

**Why finiteness has to be tracked by hand.** `SheafOfModules.Presentation.IsFinite` is a class
whose two fields are the finiteness of the generator and of the relation index type, and every
construction above leaves both index types unchanged. Nevertheless none of the transfers is
found by instance search: `SheafOfModules.Presentation.ofIsIso` has a Mathlib instance but
`Stacks.SheafOfModules.presentationOfIso` is a plain definition wrapping it, so the instance has
to be re-exposed at the wrapper; `SheafOfModules.presentationOfIsCokernelFree` has no instance at
all; and the existing instance `Presentation.IsFinite.map` for
`SheafOfModules.Presentation.map` is not found either, so
`Stacks.SheafOfModules.presentation_isFinite_map` restates it with only the hypotheses
`SheafOfModules.Presentation.map` itself needs.

**The transfers are applied, not synthesized, at the open subspace.** The comparison
`Stacks.SheafOfModules.exteriorPowerPushforwardIso` lands in sheaves of modules over
`CategoryTheory.Sheaf.toRingCat` of a pushforward structure sheaf, whereas the presentation that
has to be transported along it is produced over `structureSheafRing` of the
open subspace. Those two sheaves of rings are definitionally equal but not syntactically so, and
instance search matches up to reducible unfolding only. The finiteness hypothesis of each
transfer is therefore a named instance binder (`hP`, `hp`, `hq`) and is passed by name at the
application, where the definitional equality is checked once.

**The base case needs no separate argument.**
`Stacks.SheafOfModules.exists_free_exteriorPower_presentation` names the index types of the
exterior-power presentation concretely rather than hiding them behind an existential, and states
their finiteness as an implication from the finiteness of the given index types — that is also
what makes `Stacks.SheafOfModules.exteriorPower_finiteFreePresentation` possible. So the
positive-degree case is the general theorem with the two implications applied, and nothing about
free modules has to be redone. In degree zero the exterior power is the structure sheaf, whose
presentation `Stacks.SheafOfModules.presentationUnit` has one generator and no relations.

**The abelian structure is put in the local context.** Exactness and cokernels of short complexes
of sheaves of modules are needed in the positive-degree case, and they are derived from
`SheafOfModules.instAbelian`, whose two hypotheses `CategoryTheory.HasSheafify` and
`GrothendieckTopology.WEqualsLocallyBijective` have large synthesis proofs at the site of open
subsets of a space. Searching for them inside the search for `CategoryTheory.Abelian` overflows
the default instance-size bound, so they are introduced by `let` at the head of the proof, where
they are found in one step and the abelian structure follows.

**The two spellings of the structure sheaf of rings.** A scheme's sheaf of modules lives over
`AlgebraicGeometry.Scheme.ringCatSheaf`, which is `sheafCompose` applied to `X.sheaf`, while the
ringed-space development works over `structureSheafRing`. The two are
definitionally equal but `sheafCompose` is not reducible, so a class instance standing in context
at one spelling is not found at the other; each scheme-level statement therefore restates its
hypothesis at the other spelling with a `have` before appealing to the ringed-space theorem.

**One `@[stacks]` attribute, on one result.** `isFinitePresentation_exteriorPower` is clause (3)
of Tag 01CK for the exterior powers and carries the tag; the symmetric half is
`Stacks.SheafOfModules.isFinitePresentation_symmetricPower` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerFiniteType`.

Nothing else here is a clause of that tag, and three near misses are worth naming. Clause (2)
assumes only that `F` is of **finite type**, whereas `isFiniteType_exteriorPower` below assumes
finite presentation, which is strictly stronger; it is therefore not that clause and is not
tagged. The clause itself is `Stacks.SheafOfModules.isFiniteType_exteriorPower'` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerLocalGenerators`, proved from the
surjectivity half of Tag 01CJ alone. Clause (4) asserts coherence of the powers of a coherent
sheaf of modules on a **ringed space**, whereas
`AlgebraicGeometry.Scheme.Modules.isCoherent_exteriorPower` below assumes a locally Noetherian
scheme; it too is a narrowing and is not tagged, and the exterior third of that clause is still
open. Clause (6) is about local freeness and makes no finiteness assertion at all; it is
`Stacks.SheafOfModules.isLocallyFree_exteriorPower` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreePowers`.

What the untagged results are for is Tag 0B3T, whose invertibility assertion is about the
reflexive hull of the top exterior power of a coherent sheaf of modules on an integral regular
surface: the hull can only be formed once the exterior power is known to be coherent.

## References

* [Stacks Project, Tag 01BV](https://stacks.math.columbia.edu/tag/01BV)
* [Stacks Project, Tag 01BW](https://stacks.math.columbia.edu/tag/01BW)
* [Stacks Project, Tag 01CJ](https://stacks.math.columbia.edu/tag/01CJ)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe v₁ v₂ u₁ u₂ u

namespace Stacks.SheafOfModules

-- Reducing `structureSheafRing Y` exposes the explicit sheaf `⟨Y.presheaf, Y.IsSheaf⟩`, while the
-- algebra bundles of a ringed space are indexed by `Sheaf.toRingCat J Y.sheaf`; the two are equal
-- by `rfl`, and the goals of this namespace are type-correct at `implicit` transparency only once
-- these three Mathlib definitions unfold there. The attribute is confined to this namespace on
-- purpose: `AlgebraicGeometry.Scheme.Modules` below needs `X.sheaf` to stay folded, since the
-- index `Sheaf.toRingCat ?J ?Osharp` is solved for `?Osharp` by first-order unification against a
-- `Sheaf.obj` projection and `?Osharp.obj ≟ X.presheaf` is not invertible.
attribute [local implicit_reducible] TopCat.Sheaf TopCat.Presheaf.IsSheaf
  AlgebraicGeometry.SheafedSpace.sheaf

/-! ### Finiteness of the four presentation constructions -/

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A presentation of a sheaf of modules as the cokernel of a map between free modules on finite
index types is a finite presentation: its generator and relation index types are those two index
types. -/
instance presentationOfIsCokernelFree_isFinite {ι σ : Type u} [Finite ι] [Finite σ]
    {M : _root_.SheafOfModules.{u} R}
    (f : _root_.SheafOfModules.free (R := R) ι ⟶ _root_.SheafOfModules.free σ)
    (g : _root_.SheafOfModules.free (R := R) σ ⟶ M) (H : f ≫ g = 0)
    (H' : IsColimit (CokernelCofork.ofπ g H)) :
    (_root_.SheafOfModules.presentationOfIsCokernelFree f g H H').IsFinite where
  isFiniteType_generators := ⟨inferInstanceAs (Finite σ)⟩
  isFiniteType_relations := ⟨inferInstanceAs (Finite ι)⟩

/-- Transporting a presentation along an isomorphism of sheaves of modules preserves finiteness:
`Stacks.SheafOfModules.presentationOfIso` changes neither index type. -/
instance presentationOfIso_isFinite {M N : _root_.SheafOfModules.{u} R} (e : M ≅ N)
    (P : M.Presentation) [hP : P.IsFinite] : (presentationOfIso e P).IsFinite :=
  inferInstanceAs (_root_.SheafOfModules.Presentation.IsFinite
    (_root_.SheafOfModules.Presentation.ofIsIso e.hom P))

/-- Transporting a presentation along a colimit-preserving functor which carries the structure
sheaf to the structure sheaf preserves finiteness: `SheafOfModules.Presentation.map` changes
neither index type.

This restates the existing instance `Presentation.IsFinite.map`, which instance search does not
find in the situations of this file, with two changes: the two
`GrothendieckTopology.HasSheafCompose (forget₂ RingCat AddCommGrpCat)` hypotheses are dropped,
since `SheafOfModules.Presentation.map` does not need them, and the finiteness of the given
presentation is a *named* instance binder, so that it can be supplied at the application rather
than left to synthesis. -/
theorem presentation_isFinite_map {C' : Type u₂} [Category.{v₂} C']
    {J' : GrothendieckTopology C'} {S : Sheaf J' RingCat.{u}} [HasSheafify J' AddCommGrpCat.{u}]
    [J'.WEqualsLocallyBijective AddCommGrpCat.{u}] {M : _root_.SheafOfModules.{u} R}
    (P : M.Presentation) [hP : P.IsFinite]
    (F : _root_.SheafOfModules.{u} R ⥤ _root_.SheafOfModules.{u} S)
    [PreservesColimitsOfSize.{u, u} F]
    (η : _root_.SheafOfModules.unit S ≅ F.obj (_root_.SheafOfModules.unit R)) :
    (P.map F η).IsFinite where
  isFiniteType_generators :=
    ⟨by rw [_root_.SheafOfModules.Presentation.map_generators_I]; infer_instance⟩
  isFiniteType_relations :=
    ⟨by rw [_root_.SheafOfModules.Presentation.map_relations_I]; infer_instance⟩

/-- The presentation of a free sheaf of modules on a finite index type is finite: its generators
are that index type and it has no relations. -/
instance presentationFree_isFinite (σ : Type u) [Finite σ] :
    (presentationFree (R := R) σ).IsFinite :=
  inferInstanceAs (_root_.SheafOfModules.Presentation.IsFinite
    (_root_.SheafOfModules.presentationOfIsCokernelFree (ι := PEmpty.{u + 1}) 0 (𝟙 _) (by simp)
      isColimitCokernelCoforkId))

/-- The presentation of the structure sheaf is finite: one generator and no relations. -/
instance presentationUnit_isFinite : (presentationUnit (R := R)).IsFinite where
  isFiniteType_generators := ⟨inferInstanceAs (Finite PUnit.{u + 1})⟩
  isFiniteType_relations := ⟨inferInstanceAs (Finite PEmpty.{u + 1})⟩

section OpenSubspace

variable {X : RingedSpace.{u, u}} (U : Opens X.carrier)

/-- Transporting a presentation from the open subspace `U` back to the slice site over `U`
preserves finiteness: `Stacks.SheafOfModules.presentationOfOpenSubspaceIso` is a transport along
the equivalence of the two sites followed by a transport along an isomorphism, and neither
changes an index type. -/
instance presentationOfOpenSubspaceIso_isFinite
    {M : _root_.SheafOfModules.{u} ((structureSheafRing X).over U)}
    {N : _root_.SheafOfModules.{u}
      (structureSheafRing (openSubspace U))}
    (e : (openSubspaceEquiv U).functor.obj M ≅ N) (P : N.Presentation) [hP : P.IsFinite] :
    (presentationOfOpenSubspaceIso U e P).IsFinite :=
  presentationOfIso_isFinite _ _
    (hP := presentation_isFinite_map P (openSubspaceEquiv U).inverse
      (U.sheafOfModulesEquivOverInverseUnit (structureSheafRing X)).symm)

end OpenSubspace

/-! ### Finite presentations of the exterior powers -/

/-- **A finite presentation of a sheaf of modules on a ringed space presents every exterior
power of it finitely.** This is the finite refinement of
`Stacks.SheafOfModules.nonempty_presentation_exteriorPower`: in positive degree the two index
types produced by Tag 01CJ are finite as soon as the given ones are, which is the content of the
two implications in `Stacks.SheafOfModules.exists_free_exteriorPower_presentation`, and in degree
zero the exterior power is the structure sheaf. -/
theorem exists_isFinite_presentation_exteriorPower {Y : RingedSpace.{u, u}}
    {M : _root_.SheafOfModules.{u} (structureSheafRing Y)}
    (q : M.Presentation) [hq : q.IsFinite]
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology Y.carrier) M) (n : ℕ) :
    ∃ p : (A.exteriorPower n).Presentation, p.IsFinite := by
  let _ : HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u} := inferInstance
  let _ : (Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstance
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨presentationOfIso A.exteriorPieceZeroIsoUnit.symm presentationUnit, inferInstance⟩
  · obtain ⟨T, ιJ, ιK, hJ, hK, -, -, hT₃, hex, hepi, ⟨e₁⟩, ⟨e₂⟩⟩ :=
      exists_free_exteriorPower_presentation
        (S := ShortComplex.mk q.relationsHom q.generators.π q.relationsHom_comp_π)
        (ShortComplex.exact_of_g_is_cokernel _ q.isColimitRelationsHom) q.generators.epi
        (_root_.SheafOfModules.ringedSpaceAlgebras Y _) A
        q.relations.I q.generators.I (Iso.refl _) (Iso.refl _) n hn
    have := hepi
    have : Finite ιJ := hJ inferInstance inferInstance
    have : Finite ιK := hK inferInstance
    rw [← hT₃]
    exact ⟨_root_.SheafOfModules.presentationOfIsCokernelFree
      (e₁.inv ≫ T.f ≫ e₂.hom) (e₂.inv ≫ T.g) (by simp [T.zero])
      (IsCokernel.ofIso _ hex.gIsCokernel _ e₁ e₂ (Iso.refl _) (by simp) (by simp)),
      inferInstance⟩

section Over

variable {X : RingedSpace.{u, u}} (U : Opens X.carrier)
  (F : _root_.SheafOfModules.{u} (structureSheafRing X))
  (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) F)

/-- **A finite presentation of `F` over an open presents every exterior power of `F` finitely
over that same open.** This is the finite refinement of
`Stacks.SheafOfModules.nonempty_presentation_exteriorPower_over`, and as there the uniformity in
`n` matters: one open presents every degree, with no further shrinking. -/
theorem exists_isFinite_presentation_exteriorPower_over
    (p : (F.over U).Presentation) [hp : p.IsFinite] (n : ℕ) :
    ∃ r : ((A.exteriorPower n).over U).Presentation, r.IsFinite := by
  have hB := _root_.SheafOfModules.isExteriorAlgebra_sectionwiseExteriorAlgebra_val
    (J := (Opens.grothendieckTopology X.carrier).over U) (Osharp := X.sheaf.over U) (F.over U)
  let η := (U.sheafOfModulesEquivOverUnit (structureSheafRing X)).symm
  obtain ⟨q, hq⟩ := exists_isFinite_presentation_exteriorPower
    (p.map (openSubspaceEquiv U).functor η) (openSubspaceAlgebras U F) n
    (hq := presentation_isFinite_map p (openSubspaceEquiv U).functor η)
  exact ⟨presentationOfIso
    (exteriorPowerOverIso F U n A.exterior A.exteriorGenerator
      A.exterior_isExteriorAlgebra _ _ hB).symm
    (presentationOfOpenSubspaceIso U (exteriorPowerPushforwardIso
      (Opens.grothendieckTopology ↥U) (openSubspaceSiteFunctor U)
      (Jt := (Opens.grothendieckTopology X.carrier).over U) (Osharp := X.sheaf.over U)
      (F.over U) n _ _ hB (openSubspaceAlgebras U F).exterior
      (openSubspaceAlgebras U F).exteriorGenerator
      (openSubspaceAlgebras U F).exterior_isExteriorAlgebra) q),
    presentationOfIso_isFinite _ _
      (hP := presentationOfOpenSubspaceIso_isFinite U _ q (hP := hq))⟩

end Over

/-! ### The conclusions on a ringed space -/

section Conclusions

variable {X : RingedSpace.{u, u}}
  (F : _root_.SheafOfModules.{u} (structureSheafRing X))
  (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) F)

/-- **Each exterior power of a sheaf of modules of finite presentation on a ringed space is of
finite presentation.** The covering family is the one that presents `F` finitely; no degree needs
a smaller open, because
`Stacks.SheafOfModules.exists_isFinite_presentation_exteriorPower_over` presents every degree
finitely over that same open. This is clause (3) of [Stacks, Tag 01CK] for the exterior
powers. -/
@[stacks 01CK "exterior powers of a module of finite presentation"]
theorem isFinitePresentation_exteriorPower [F.IsFinitePresentation] (n : ℕ) :
    (A.exteriorPower n).IsFinitePresentation := by
  obtain ⟨c, hc⟩ :=
    _root_.SheafOfModules.IsFinitePresentation.exists_quasicoherentData.{u, u, u} F
  choose r hr using fun i =>
    exists_isFinite_presentation_exteriorPower_over (c.X i) F A (c.presentation i) n
      (hp := hc.isFinite_presentation i)
  exact ⟨{ I := c.I, X := c.X, coversTop := c.coversTop, presentation := r }, ⟨hr⟩⟩

/-- **Each exterior power of a sheaf of modules of finite presentation on a ringed space is of
finite type.** This is the half of
`Stacks.SheafOfModules.isFinitePresentation_exteriorPower` that Tag 0B3T consumes, the other half
being the quasi-coherence recorded in
`Stacks.SheafOfModules.isQuasicoherent_exteriorPower`. -/
theorem isFiniteType_exteriorPower [F.IsFinitePresentation] (n : ℕ) :
    (A.exteriorPower n).IsFiniteType :=
  have := isFinitePresentation_exteriorPower F A n
  inferInstance

/-- **Each exterior power of a coherent sheaf of modules on a ringed space is of finite type.**
A coherent sheaf of modules is of finite presentation by Tag 01BW, and
`Stacks.SheafOfModules.isFiniteType_exteriorPower` applies. -/
theorem isFiniteType_exteriorPower_of_isCoherent [F.IsCoherent] (n : ℕ) :
    (A.exteriorPower n).IsFiniteType :=
  have := isFinitePresentation_of_isCoherent F
  isFiniteType_exteriorPower F A n

end Conclusions

end Stacks.SheafOfModules

/-! ### The scheme-level statements -/

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (F : X.Modules)

/-- **Each exterior power of a sheaf of modules of finite presentation on a scheme is of finite
presentation.** -/
instance isFinitePresentation_exteriorPower [hF : F.IsFinitePresentation] (n : ℕ) :
    (Scheme.Modules.exteriorPower F (n : ℤ)).IsFinitePresentation :=
  have : _root_.SheafOfModules.IsFinitePresentation.{u, u, u}
    (R := structureSheafRing X.toRingedSpace) F := hF
  Stacks.SheafOfModules.isFinitePresentation_exteriorPower (X := X.toRingedSpace) F
    (_root_.SheafOfModules.algebras _ F) n

/-- **Each exterior power of a sheaf of modules of finite presentation on a scheme is of finite
type.** -/
instance isFiniteType_exteriorPower [hF : F.IsFinitePresentation] (n : ℕ) :
    _root_.SheafOfModules.IsFiniteType.{u, u, u} (Scheme.Modules.exteriorPower F (n : ℤ)) :=
  have : _root_.SheafOfModules.IsFinitePresentation.{u, u, u}
    (R := structureSheafRing X.toRingedSpace) F := hF
  Stacks.SheafOfModules.isFiniteType_exteriorPower (X := X.toRingedSpace) F
    (_root_.SheafOfModules.algebras _ F) n

/-- **Each exterior power of a coherent sheaf of modules on a scheme is of finite type.** This is
the finiteness input of Tag 0B3T; its quasi-coherent companion is
`Stacks.SheafOfModules.isQuasicoherent_exteriorPower`. -/
instance isFiniteType_exteriorPower_of_isCoherent [hF : F.IsCoherent] (n : ℕ) :
    _root_.SheafOfModules.IsFiniteType.{u, u, u} (Scheme.Modules.exteriorPower F (n : ℤ)) :=
  have : _root_.SheafOfModules.IsCoherent
    (R := structureSheafRing X.toRingedSpace) F := hF
  Stacks.SheafOfModules.isFiniteType_exteriorPower_of_isCoherent (X := X.toRingedSpace) F
    (_root_.SheafOfModules.algebras _ F) n

/-- **Each exterior power of a quasi-coherent sheaf of modules on a scheme is quasi-coherent.**
This is `Stacks.SheafOfModules.isQuasicoherent_exteriorPower` recorded as an instance for
`AlgebraicGeometry.Scheme.Modules.exteriorPower`. -/
instance isQuasicoherent_exteriorPower [hF : F.IsQuasicoherent] (n : ℕ) :
    _root_.SheafOfModules.IsQuasicoherent.{u, u, u} (Scheme.Modules.exteriorPower F (n : ℤ)) :=
  have : _root_.SheafOfModules.IsQuasicoherent.{u, u, u}
    (R := structureSheafRing X.toRingedSpace) F := hF
  Stacks.SheafOfModules.isQuasicoherent_exteriorPower (X := X.toRingedSpace) F
    (_root_.SheafOfModules.algebras _ F) n

/-- **Each exterior power of a coherent sheaf of modules on a scheme is quasi-coherent.** A
coherent sheaf of modules is quasi-coherent by Tag 01BW; the implication is a theorem and not an
instance in this library, so the coherent case is recorded separately from
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_exteriorPower`. -/
instance isQuasicoherent_exteriorPower_of_isCoherent [hF : F.IsCoherent] (n : ℕ) :
    _root_.SheafOfModules.IsQuasicoherent.{u, u, u} (Scheme.Modules.exteriorPower F (n : ℤ)) :=
  have _hFr : _root_.SheafOfModules.IsCoherent
    (R := structureSheafRing X.toRingedSpace) F := hF
  have : _root_.SheafOfModules.IsQuasicoherent.{u, u, u}
    (R := structureSheafRing X.toRingedSpace) F :=
    isQuasicoherent_of_isCoherent F
  Stacks.SheafOfModules.isQuasicoherent_exteriorPower (X := X.toRingedSpace) F
    (_root_.SheafOfModules.algebras _ F) n

/-- **On a locally Noetherian scheme every exterior power of a coherent sheaf of modules is
coherent.** The exterior power is quasi-coherent by
`Stacks.SheafOfModules.isQuasicoherent_exteriorPower` and of finite type by
`AlgebraicGeometry.Scheme.Modules.isFiniteType_exteriorPower_of_isCoherent`, and on a locally
Noetherian scheme those two conditions imply coherence — implication (2) ⇒ (1) of Tag 01XZ,
`Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType`.

This is the finiteness statement Tag 0B3T needs: the reflexive hull of the top exterior power of
a coherent sheaf of modules can only be formed once that exterior power is known to be
coherent. -/
instance isCoherent_exteriorPower [IsLocallyNoetherian X] [hF : F.IsCoherent] (n : ℕ) :
    _root_.SheafOfModules.IsCoherent (Scheme.Modules.exteriorPower F (n : ℤ)) :=
  have _hFr : _root_.SheafOfModules.IsCoherent
    (R := structureSheafRing X.toRingedSpace) F := hF
  have : _root_.SheafOfModules.IsQuasicoherent.{u, u, u}
    (R := structureSheafRing X.toRingedSpace) F :=
    isQuasicoherent_of_isCoherent F
  have : _root_.SheafOfModules.IsQuasicoherent.{u, u, u}
      (Scheme.Modules.exteriorPower F (n : ℤ)) :=
    Stacks.SheafOfModules.isQuasicoherent_exteriorPower (X := X.toRingedSpace) F
      (_root_.SheafOfModules.algebras _ F) n
  have : _root_.SheafOfModules.IsFiniteType.{u, u, u}
      (Scheme.Modules.exteriorPower F (n : ℤ)) :=
    Stacks.SheafOfModules.isFiniteType_exteriorPower_of_isCoherent (X := X.toRingedSpace) F
      (_root_.SheafOfModules.algebras _ F) n
  Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType
    (Scheme.Modules.exteriorPower F (n : ℤ))

end AlgebraicGeometry.Scheme.Modules

end
