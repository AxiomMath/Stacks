module

public import StacksFrontier.AlgebraicGeometry.CohomologyFinitenessNoetherian.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.AffineModuleFinite
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.NoetherianBase

/-!
# The finite-type clause of Tag 0EX4 over a locally Noetherian base, from Tag 02O6 at a ring base

`StacksFrontier/AlgebraicGeometry/TopDegreeFiniteType/NoetherianBase.lean` proves that over a
locally Noetherian base the finite-type clause of [Stacks, Tag 0EX4] is *equivalent* to
[Stacks, Tag 02O6], and states [Stacks, Tag 02O6] over an **abstract affine scheme** `S₀`, with
`Γ(S₀, ⊤)` as the ring and `g.appTop` as the structure map on sections.

Every proof of [Stacks, Tag 02O6] in this development instead concludes at a **ring** base: the
morphism goes to `Spec (CommRingCat.of A)` for `A` a Noetherian commutative ring, and the module
is finite over `A` along `(Scheme.ΓSpecIso (.of A)).inv ≫ g.appTop`. That is the shape of
`AlgebraicGeometry.forall_moduleFinite_cohomology_ringBase_of_exists_epi`,
of `AlgebraicGeometry.forall_moduleFinite_cohomology_ringBase_of_epi_biprodPow`, and of
`Stacks.AlgebraicGeometry.ProperCohomologyFinite.moduleFinite_cohomology_ringBase_of_isCoherent`.

So the tag is produced at one shape and consumed at another, and nothing identified the two. This
file identifies them, in both directions, and reads the consequence off for
[Stacks, Tag 0EX4]: the ring-base shape of [Stacks, Tag 02O6] suffices for the tag's finite-type
clause over a locally Noetherian base.

## Main results

* `…ΓSpecIso_inv_comp_isoSpec_appTop`: the one computation the identification needs —
  composing with `AlgebraicGeometry.Scheme.isoSpec` and then correcting by
  `AlgebraicGeometry.Scheme.ΓSpecIso` returns the original map on global sections.
* `…moduleFinite_cohomology_ringBase_iff_moduleFinite_cohomology`: **the two shapes of
  [Stacks, Tag 02O6] are equivalent**, each quantified over all of its own data.
* `…isFiniteType_rightDerived_of_forall_moduleFinite_cohomology_ringBase`: the finite-type clause
  of [Stacks, Tag 0EX4] over a locally Noetherian base from the ring-base shape.
* `…isFiniteType_rightDerived_of_forall_topologicalKrullDim_fiber_le_of_ringBase`: the same with
  the tag's fibre-dimension bound carried as a binder, so the statement is the tag's clause with
  two hypotheses added and nothing else changed.
* `…forall_isFiniteType_rightDerived_iff_forall_moduleFinite_cohomology_ringBase`: the family
  equivalence, which is what shows nothing was weakened to obtain the implication.
* `…isFiniteType_rightDerived_of_forall_exists_epi_ringBase`: the same conclusion from the
  *dévissage input* of [Stacks, Tag 02O6] — every coherent module is a quotient of a coherent
  module with finite cohomology — rather than from its conclusion.

## Implementation notes

**Why the identification is not a formality.** `Γ(S₀, ⊤)` is a `CommRingCat` and `A` is a bare
type with a `CommRing` instance, the two structure maps differ by
`AlgebraicGeometry.Scheme.ΓSpecIso`, and the morphism itself has a different target on the two
sides. The forward direction composes the given `g : X₀ ⟶ S₀` with `S₀.isoSpec.hom` to land in
`Spec (.of Γ(S₀, ⊤))`, and the correction term is then exactly
`(Scheme.ΓSpecIso Γ(S₀, ⊤)).inv ≫ (Scheme.ΓSpecIso Γ(S₀, ⊤)).hom`, which cancels. The backward
direction needs no morphism surgery, only that `A`-finiteness restricts along the surjection
`(Scheme.ΓSpecIso (.of A)).inv`, which is
`…ProperCohomologyFinite.moduleFinite_compHom_of_surjective`.

`CommRingCat.of (Γ(S₀, ⊤) : Type u)` and `Γ(S₀, ⊤)` are the same bundled ring by `rfl`, but not
syntactically, so the cancellation is reached by `change` at the spelling
`Scheme.ΓSpecIso Γ(S₀, ⊤)` before `Iso.inv_hom_id_assoc` is applied. Writing the statement with
the un-coerced `Γ(S₀, ⊤)` instead would make the lemma unusable at the ring-base shape, which
always spells its ring as `CommRingCat.of A`.

**Which coherence predicate.** `_root_.SheafOfModules.IsCoherent` is written out in full
throughout. This namespace begins with `Stacks`, so the relative name `SheafOfModules.IsCoherent`
resolves to `Stacks.SheafOfModules.IsCoherent`, a *different* constant with the same two fields;
the predicate used here is the root-level one, which is the one
`…TopDegreeFiniteType.isFiniteType_rightDerived_of_moduleFinite_cohomology` and
`AlgebraicGeometry.forall_moduleFinite_cohomology_ringBase_of_exists_epi` both take.

**No Stacks attribute is attached to anything here.** Every statement carries
`IsLocallyNoetherian Y` together with [Stacks, Tag 02O6] as an explicit hypothesis, and
[Stacks, Tag 0EX4] carries neither; the two equivalences are between families of which none is
proved. 
**What the hypothesis is, and what it is not.** The ring-base family quantified over every
Noetherian ring and every proper morphism is [Stacks, Tag 02O6] itself, which this development
does not prove. It is not an empty slot: its restriction from `IsProper` to `IsFinite` is proved
unconditionally, as
`…ProperCohomologyFinite.moduleFinite_cohomology_ringBase_of_isFinite`. But the family
equivalence below shows the hypothesis is exactly as strong as the conclusion, so nothing here
exhibits an unconditional witness for it, and none is claimed.

## References

* [Stacks Project, Tag 0EX4](https://stacks.math.columbia.edu/tag/0EX4)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Stacks.Cohomology.AffineBase
open Stacks.AlgebraicGeometry.ProperCohomologyFinite

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeFiniteType

attribute [local instance] HasDerivedCategory.standard

/-! ### The comparison of the two structure maps on global sections -/

/-- **Composing with `AlgebraicGeometry.Scheme.isoSpec` and correcting by
`AlgebraicGeometry.Scheme.ΓSpecIso` is the identity on global sections.** For `g : X ⟶ S` with
`S` affine, the structure map that the ring-base spelling of [Stacks, Tag 02O6] attaches to
`g ≫ S.isoSpec.hom : X ⟶ Spec (.of Γ(S, ⊤))` is `g.appTop` itself.

This is the whole content of the identification of the two shapes: `Scheme.isoSpec` is
`Scheme.toSpecΓ` and `Scheme.toSpecΓ_appTop` says that is `(Scheme.ΓSpecIso Γ(S, ⊤)).hom`. -/
theorem ΓSpecIso_inv_comp_isoSpec_appTop {X S : Scheme.{u}} (g : X ⟶ S) [IsAffine S] :
    (Scheme.ΓSpecIso (.of (Γ(S, ⊤) : Type u))).inv ≫ (g ≫ S.isoSpec.hom).appTop = g.appTop := by
  rw [Scheme.Hom.comp_appTop, Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop]
  change (Scheme.ΓSpecIso Γ(S, ⊤)).inv ≫ (Scheme.ΓSpecIso Γ(S, ⊤)).hom ≫ g.appTop = g.appTop
  exact Iso.inv_hom_id_assoc _ _

/-! ### The two shapes of Tag 02O6 -/

/-- **[Stacks, Tag 02O6] over an abstract affine base, from [Stacks, Tag 02O6] over a ring
base.** Given the finiteness theorem for every Noetherian ring `A` and every proper morphism to
`Spec (.of A)`, it holds for every proper morphism to an affine locally Noetherian scheme `S₀`,
with `Γ(S₀, ⊤)` as the ring.

`Γ(S₀, ⊤)` is a Noetherian ring because `⊤` is an affine open of `S₀`; the given morphism is
composed with `S₀.isoSpec.hom`, which is an isomorphism and so leaves properness alone; and
`ΓSpecIso_inv_comp_isoSpec_appTop` identifies the two structure maps, so the two conclusions are
the same proposition. -/
theorem moduleFinite_cohomology_of_moduleFinite_cohomology_ringBase
    (h : ∀ (A : Type u) [CommRing A], IsNoetherianRing A → ∀ (X₀ : Scheme.{u})
      (g : X₀ ⟶ Spec (.of A)), IsProper g →
      ∀ G : X₀.Modules, _root_.SheafOfModules.IsCoherent G → ∀ n : ℕ, Module.Finite A
        ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ g.appTop).hom).obj
          (((moduleGlobalSections X₀).rightDerived n).obj G)))
    (X₀ S₀ : Scheme.{u}) (g : X₀ ⟶ S₀) (hg : IsProper g) (hS : IsAffine S₀)
    (hSN : IsLocallyNoetherian S₀) (G : X₀.Modules)
    (hG : _root_.SheafOfModules.IsCoherent G) (n : ℕ) :
    Module.Finite Γ(S₀, ⊤) ((ModuleCat.restrictScalars g.appTop.hom).obj
      (((moduleGlobalSections X₀).rightDerived n).obj G)) := by
  have := hg
  have := hS
  have := hSN
  have hN : IsNoetherianRing (Γ(S₀, ⊤) : Type u) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S₀⟩
  have key := h (Γ(S₀, ⊤) : Type u) hN X₀ (g ≫ S₀.isoSpec.hom) inferInstance G hG n
  rw [ΓSpecIso_inv_comp_isoSpec_appTop g] at key
  exact key

/-- **[Stacks, Tag 02O6] over a ring base, from [Stacks, Tag 02O6] over an abstract affine
base.** The converse of `moduleFinite_cohomology_of_moduleFinite_cohomology_ringBase`.

`Spec (.of A)` is affine and is locally Noetherian exactly when `A` is
(`AlgebraicGeometry.isLocallyNoetherian_Spec`), so the hypothesis applies on the nose with
`Γ(Spec (.of A), ⊤)` as the ring; `moduleFinite_compHom_of_surjective` then restricts the module
structure along the surjection `(Scheme.ΓSpecIso (.of A)).inv`. -/
theorem moduleFinite_cohomology_ringBase_of_moduleFinite_cohomology
    (h : ∀ (X₀ S₀ : Scheme.{u}) (g : X₀ ⟶ S₀), IsProper g → IsAffine S₀ →
      IsLocallyNoetherian S₀ → ∀ G : X₀.Modules, _root_.SheafOfModules.IsCoherent G → ∀ n : ℕ,
        Module.Finite Γ(S₀, ⊤) ((ModuleCat.restrictScalars g.appTop.hom).obj
          (((moduleGlobalSections X₀).rightDerived n).obj G)))
    (A : Type u) [CommRing A] (hN : IsNoetherianRing A) (X₀ : Scheme.{u})
    (g : X₀ ⟶ Spec (.of A)) (hg : IsProper g) (G : X₀.Modules)
    (hG : _root_.SheafOfModules.IsCoherent G) (n : ℕ) :
    Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ g.appTop).hom).obj
        (((moduleGlobalSections X₀).rightDerived n).obj G)) := by
  have := hg
  have hΓ := h X₀ (Spec (.of A)) g hg inferInstance (isLocallyNoetherian_Spec.2 hN) G hG n
  have hsurj : Function.Surjective (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2
  exact moduleFinite_compHom_of_surjective
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom hsurj
    ((ModuleCat.restrictScalars g.appTop.hom).obj
      (((moduleGlobalSections X₀).rightDerived n).obj G))

/-- **The ring-base and abstract-affine-base shapes of [Stacks, Tag 02O6] are equivalent**, each
quantified over all of its own data.

So the finiteness theorem may be proved at whichever of the two spellings is convenient. The
dévissage development of this repository concludes at the left-hand shape and the consumers that
turn [Stacks, Tag 02O6] into [Stacks, Tag 0EX4] ask for the right-hand one. -/
theorem moduleFinite_cohomology_ringBase_iff_moduleFinite_cohomology :
    (∀ (A : Type u) [CommRing A], IsNoetherianRing A → ∀ (X₀ : Scheme.{u})
        (g : X₀ ⟶ Spec (.of A)), IsProper g →
        ∀ G : X₀.Modules, _root_.SheafOfModules.IsCoherent G → ∀ n : ℕ, Module.Finite A
          ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ g.appTop).hom).obj
            (((moduleGlobalSections X₀).rightDerived n).obj G))) ↔
      (∀ (X₀ S₀ : Scheme.{u}) (g : X₀ ⟶ S₀), IsProper g → IsAffine S₀ →
        IsLocallyNoetherian S₀ → ∀ G : X₀.Modules, _root_.SheafOfModules.IsCoherent G → ∀ n : ℕ,
          Module.Finite Γ(S₀, ⊤) ((ModuleCat.restrictScalars g.appTop.hom).obj
            (((moduleGlobalSections X₀).rightDerived n).obj G))) :=
  ⟨moduleFinite_cohomology_of_moduleFinite_cohomology_ringBase,
    moduleFinite_cohomology_ringBase_of_moduleFinite_cohomology⟩

/-! ### The finite-type clause of Tag 0EX4 over a locally Noetherian base -/

/-- **The finite-type clause of [Stacks, Tag 0EX4] over a locally Noetherian base, from
[Stacks, Tag 02O6] at a ring base.** For `f : X ⟶ Y` proper with `Y` locally Noetherian and `F`
quasi-coherent of finite type, `R ᵈ f_* F` is of finite type in every degree `d`, given the
finiteness theorem for every Noetherian ring.

This is `…TopDegreeFiniteType.isFiniteType_rightDerived_of_moduleFinite_cohomology` with its
hypothesis moved to the shape in which every proof of [Stacks, Tag 02O6] in this repository
concludes. There is no hypothesis on the fibres of `f`: over a locally Noetherian base the bound
is provably inert. -/
theorem isFiniteType_rightDerived_of_forall_moduleFinite_cohomology_ringBase {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian Y] (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] (d : ℕ)
    (h : ∀ (A : Type u) [CommRing A], IsNoetherianRing A → ∀ (X₀ : Scheme.{u})
      (g : X₀ ⟶ Spec (.of A)), IsProper g →
      ∀ G : X₀.Modules, _root_.SheafOfModules.IsCoherent G → ∀ n : ℕ, Module.Finite A
        ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ g.appTop).hom).obj
          (((moduleGlobalSections X₀).rightDerived n).obj G))) :
    (((Scheme.Modules.pushforward f).rightDerived d).obj F).IsFiniteType :=
  isFiniteType_rightDerived_of_moduleFinite_cohomology f F d
    (moduleFinite_cohomology_of_moduleFinite_cohomology_ringBase h)

/-- **Clause (2) of [Stacks, Tag 0EX4] over a locally Noetherian base, conditional on
[Stacks, Tag 02O6] at a ring base.** The statement of the tag's finite-type clause with exactly
two hypotheses added — `IsLocallyNoetherian Y` and the finiteness theorem — and nothing else
changed; in particular the fibre-dimension bound is retyped as the tag states it.

The bound is carried and never used, which is why the binder is named `_hdim`: over a locally
Noetherian base the content of the clause in degree `d` does not depend on the fibres of `f` at
all. -/
theorem isFiniteType_rightDerived_of_forall_topologicalKrullDim_fiber_le_of_ringBase
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian Y] (d : ℕ)
    (_hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞))
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (h : ∀ (A : Type u) [CommRing A], IsNoetherianRing A → ∀ (X₀ : Scheme.{u})
      (g : X₀ ⟶ Spec (.of A)), IsProper g →
      ∀ G : X₀.Modules, _root_.SheafOfModules.IsCoherent G → ∀ n : ℕ, Module.Finite A
        ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ g.appTop).hom).obj
          (((moduleGlobalSections X₀).rightDerived n).obj G))) :
    (((Scheme.Modules.pushforward f).rightDerived d).obj F).IsFiniteType :=
  isFiniteType_rightDerived_of_forall_moduleFinite_cohomology_ringBase f F d h

/-- **The finite-type clause of [Stacks, Tag 0EX4] over locally Noetherian bases is equivalent to
[Stacks, Tag 02O6] at a ring base**, each side quantified over all of its own data.

This is what shows the implication above weakens nothing: the hypothesis family is neither
stronger nor weaker than the conclusion family. Composed with
`…TopDegreeFiniteType.forall_isFiniteType_rightDerived_iff_forall_moduleFinite_cohomology`, which
is the same equivalence at the abstract-affine shape. -/
theorem forall_isFiniteType_rightDerived_iff_forall_moduleFinite_cohomology_ringBase :
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y), IsProper f → IsLocallyNoetherian Y →
        ∀ F : X.Modules, F.IsQuasicoherent → F.IsFiniteType →
          ∀ d : ℕ, (((Scheme.Modules.pushforward f).rightDerived d).obj F).IsFiniteType) ↔
      (∀ (A : Type u) [CommRing A], IsNoetherianRing A → ∀ (X₀ : Scheme.{u})
        (g : X₀ ⟶ Spec (.of A)), IsProper g →
        ∀ G : X₀.Modules, _root_.SheafOfModules.IsCoherent G → ∀ n : ℕ, Module.Finite A
          ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ g.appTop).hom).obj
            (((moduleGlobalSections X₀).rightDerived n).obj G))) :=
  forall_isFiniteType_rightDerived_iff_forall_moduleFinite_cohomology.trans
    moduleFinite_cohomology_ringBase_iff_moduleFinite_cohomology.symm

/-- **The finite-type clause of [Stacks, Tag 0EX4] over a locally Noetherian base, from the
dévissage input of [Stacks, Tag 02O6].** The hypothesis is not the finiteness theorem but the
supply of resolving modules it is proved from: over every Noetherian ring, every coherent module
on a proper scheme is a quotient of a coherent module whose cohomology is finite in every degree.

That is the hypothesis of
`AlgebraicGeometry.forall_moduleFinite_cohomology_ringBase_of_exists_epi`, which is where the
devissage of this repository stops, and on projective space it is supplied by the Čech
computation of [Stacks, Tag 01XT] together with clause (1) of [Stacks, Tag 01YS] through
`AlgebraicGeometry.exists_isCoherent_and_forall_moduleFinite_and_epi_of_epi_biprodPow`. -/
theorem isFiniteType_rightDerived_of_forall_exists_epi_ringBase {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian Y] (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] (d : ℕ)
    (hgen : ∀ (A : Type u) [CommRing A], IsNoetherianRing A → ∀ (X₀ : Scheme.{u})
      (g : X₀ ⟶ Spec (.of A)), IsProper g →
      ∀ G : X₀.Modules, _root_.SheafOfModules.IsCoherent G →
        ∃ E : X₀.Modules, _root_.SheafOfModules.IsCoherent E ∧
          (∀ n : ℕ, Module.Finite A
            ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ g.appTop).hom).obj
              (((moduleGlobalSections X₀).rightDerived n).obj E))) ∧ ∃ φ : E ⟶ G, Epi φ) :
    (((Scheme.Modules.pushforward f).rightDerived d).obj F).IsFiniteType :=
  isFiniteType_rightDerived_of_forall_moduleFinite_cohomology_ringBase f F d (by
    intro A inst hN X₀ g hg
    have := hN
    have := hg
    exact AlgebraicGeometry.forall_moduleFinite_cohomology_ringBase_of_exists_epi A g
      (hgen A hN X₀ g hg))

end Stacks.AlgebraicGeometry.TopDegreeFiniteType

end
