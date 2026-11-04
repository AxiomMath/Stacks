module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.GlobalPresentationComparison

/-!
# Pullback along a morphism of ringed topoi and the quasi-coherent clause

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi and let `F` be a
quasi-coherent sheaf of `O_D`-modules.  Stacks 03DO, for the clause 03DL (6), asserts that the
pullback `f^*F = O_C ⊗_{f⁻¹O_D} f⁻¹F` of Stacks 03D6 (2) is again quasi-coherent.  This file
proves the extension-of-scalars half of that statement and reduces the whole of it to the
inverse-image factor, exactly as
`Stacks.Sheaves.FinitePresentation.isFinitePresentation_pullbackModules_of_inverseImage_local`
does for the clause 03DL (7).

The reduction is available now because
`Stacks.SheafOfModules.hasGlobalPresentation_of_presentation` of
`StacksFrontier.AlgebraicGeometry.Topologies.GlobalPresentationComparison` converts a
`SheafOfModules.Presentation` into a `SheafOfModules.HasGlobalPresentation`.  Extension of
scalars transports a presentation with no finiteness hypothesis
(`Stacks.Sheaves.FinitePresentation.presentationExtendScalarsOver`), so the whole
extension-of-scalars half of the quasi-coherent clause follows from the finitely presented one
by dropping the finiteness, once the two encodings of a global presentation are known to agree.

## Main results

* `Stacks.SheafOfModules.isQuasicoherentOnSite_of_locally_presented`: **the local criterion for
  quasi-coherence.**  A sheaf of modules admitting a `SheafOfModules.Presentation` on each
  member of some covering of each object of the site is quasi-coherent.  This is the
  quasi-coherent counterpart of
  `Stacks.SheafOfModules.isFinitePresentation_of_locally_presented`.
* `Stacks.Sheaves.Quasicoherence.isQuasicoherentOnSite_pullbackModules_of_inverseImage_local`:
  **Stacks 03DO, the quasi-coherent clause of 03DL (6), reduced to the inverse-image factor.**
  If the inverse image `f⁻¹F` of Stacks 03D2 has a presentation on the members of some covering
  of each object of the source site, then `f^*F` is quasi-coherent.

## Implementation notes

**What this reduction still owes, and why the finitely presented route does not supply it.**
The clause 03DL (6) itself is proved, by a different route: it is
`AlgebraicGeometry.RingedToposHom.isQuasicoherentOnSite_pullbackModules` in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LocalTypesToposPullback.lean`, which factors the
morphism with Stacks 03CR and carries the clause around the resulting square.  What remains
undischarged is the hypothesis of the reduction *below*, the inverse-image half: that a
quasi-coherent `F` makes `f⁻¹F` locally presented on the source site.  For the clause 03DL (7)
that half is
`Stacks.Sheaves.PresentationTransport.exists_cover_isFinite_presentation_inverseImage`, and its
mechanism is that a *finite* presentation over an object is a point of a sheaf of sets,
`Stacks.Sheaves.LocalGeneration.presDataSheaf F n m`, indexed by `ℕ × ℕ`; joint local
inhabitedness of that family then transports along `f⁻¹` by
`Stacks.Topos.exists_cover_inverseImage_sections`, whose index type is arbitrary.  A general
presentation names two index *types* in the module universe, so the presentations of `F` over an
object do not form a type in that universe and there is no sheaf of sets to carry along.  The
remaining half therefore needs the localization of a morphism of ringed topoi — the content of
the source's Section 03DG, which assumes the sites have finite limits — and not a larger index
type for the family.

**No `@[stacks]` attribute is placed here.** The quasi-coherent clause is not proved outright
below, only reduced, so nothing here states it; it carries its attribute at
`AlgebraicGeometry.RingedToposHom.isQuasicoherentOnSite_pullbackModules`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LocalTypesToposPullback.lean`), alongside the
clauses 03DL (1), (2) and (3).  The clauses proved by the sheaf-of-sets route described above
carry theirs at `Stacks.Sheaves.LocalGeneration.pullbackModules_isLocallyGeneratedByOnSite`
(`ToposPullbackLocalGeneration.lean`), `Stacks.Sheaves.FiniteType.pullbackModules_isFiniteType`
(`ToposPullbackFiniteType.lean`) and
`Stacks.Sheaves.FinitePresentation.isFinitePresentation_pullbackModules`
(`ToposPullbackPresentationAssembly.lean`).

**The hypotheses are the ones the inputs carry.** The local criterion needs sheafification of
abelian presheaves on the slice sites and nothing else — in particular no smallness of the site,
because the conversion from a `SheafOfModules.Presentation` to a
`SheafOfModules.HasGlobalPresentation` is unconditional.  The reduction adds the variable block
of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ToposPullbackFinitePresentation.lean`, which is
what `Stacks.Sheaves.RingedToposModules.pullbackModules` and
`Stacks.Sheaves.FinitePresentation.presentationExtendScalarsOver` ask for.

## References

* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.SheafOfModules

/-! ### The local criterion for quasi-coherence -/

section Local

universe u v u₁

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{u}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The local criterion for quasi-coherence.** A sheaf of modules that has a
`SheafOfModules.Presentation` on each member of some covering of each object of the site is
quasi-coherent.

The covering sieve is turned into the covering family of arrows that
`SheafOfModules.IsQuasicoherentOnSite` asks for by indexing it by the objects of the sieve, and
each presentation becomes a global presentation by
`Stacks.SheafOfModules.hasGlobalPresentation_of_presentation`. -/
theorem isQuasicoherentOnSite_of_locally_presented (M : _root_.SheafOfModules.{u} R)
    (hM : ∀ U : C, ∃ T : J.Cover U, ∀ (V : C) (g : V ⟶ U), T g →
      Nonempty (M.over V).Presentation) :
    M.IsQuasicoherentOnSite := by
  refine ⟨fun U => ?_⟩
  obtain ⟨T, hT⟩ := hM U
  refine ⟨{h : Over U // (T : Sieve U) h.hom}, fun a => a.1.left, fun a => a.1.hom, ?_, ?_⟩
  · have hEq : Sieve.ofArrows (fun a : {h : Over U // (T : Sieve U) h.hom} => a.1.left)
        (fun a => a.1.hom) = (T : Sieve U) := by
      refine le_antisymm (fun Z k hk => ?_) (fun Z k hk => ?_)
      · rw [Sieve.mem_ofArrows_iff] at hk
        obtain ⟨a, b, rfl⟩ := hk
        exact (T : Sieve U).downward_closed a.2 b
      · rw [Sieve.mem_ofArrows_iff]
        exact ⟨⟨Over.mk k, hk⟩, 𝟙 Z, by simp⟩
    rw [hEq]
    exact T.2
  · exact fun a => (hT a.1.left a.1.hom a.2).elim hasGlobalPresentation_of_presentation

end Local

end Stacks.SheafOfModules

namespace Stacks.Sheaves.Quasicoherence

open AlgebraicGeometry Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.FinitePresentation

universe v u v' u' w

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposHom X Y)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- **Stacks 03DO for the clause 03DL (6), reduced to the inverse-image factor.** If the inverse
image `f⁻¹F` of Stacks 03D2 has a `SheafOfModules.Presentation` on the members of some covering
of each object of the source site, then the pullback `f^*F = O_C ⊗_{f⁻¹O_D} f⁻¹F` of
Stacks 03D6 (2) is quasi-coherent.

The two steps are
`Stacks.Sheaves.FinitePresentation.presentationExtendScalarsOver`, which transports each local
presentation across extension of scalars along `f⁻¹O_D ⟶ O_C` and carries no finiteness
hypothesis, and `Stacks.SheafOfModules.isQuasicoherentOnSite_of_locally_presented`, which
assembles the local presentations into quasi-coherence. -/
theorem isQuasicoherentOnSite_pullbackModules_of_inverseImage_local
    (F : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (hF : ∀ U : X.C, ∃ T : X.J.Cover U, ∀ (V : X.C) (g : V ⟶ U), T g →
      Nonempty ((((inverseImageModules f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F).over V).Presentation)) :
    ((f.pullbackModules).obj F).IsQuasicoherentOnSite := by
  refine Stacks.SheafOfModules.isQuasicoherentOnSite_of_locally_presented _ fun U => ?_
  obtain ⟨T, hT⟩ := hF U
  refine ⟨T, fun V g hg => ?_⟩
  obtain ⟨P⟩ := hT V g hg
  exact ⟨presentationExtendScalarsOver (fSharpCommRing f)
    (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
    ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F) V P⟩

end Stacks.Sheaves.Quasicoherence

end
