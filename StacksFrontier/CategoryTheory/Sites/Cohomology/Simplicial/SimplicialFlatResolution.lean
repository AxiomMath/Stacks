module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoverTensorExactness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRetract
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.AugmentationDerivedBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.ProjectionDerivedLowerShriek
import StacksCore.Tactic.StacksAttribute

/-!
# Flat resolutions of simplicial modules: step 2 of Stacks 09D2

The second step of the proof of [Stacks, Tag 09D2] reads

> Every such complex is quasi-isomorphic to a bounded above complex whose terms are flat
> modules, see Modules on Sites, Lemma 18.28.8. Thus it suffices to prove the lemma for a flat
> `A_•`-module `F`.

Modules on Sites, Lemma 18.28.8 is [Stacks, Tag 03EW]; its part (4), that every sheaf of modules
on a site is a quotient of a flat one, is
`Stacks.SheafOfModules.FlatCover.exists_epi_from_isFlat`, and the passage from a quotient to a
resolution of a bounded above complex is [Stacks, Tag 05T7],
`CochainComplex.exists_quasiIso_prop`. This file puts the two together at the site `Δ × C` of
[Stacks, Tag 09D0], where a sheaf of modules over the sheaf of rings associated to a simplicial
sheaf of rings `A_•` is a simplicial `A_•`-module ([Stacks, Tag 09D1]).

## Main results

* `Stacks.SimplicialModules.isFlat_of_isZero`: a zero sheaf of modules is flat.
* `Stacks.SimplicialModules.exists_epi_isFlat_simplicial`: **[Stacks, Tag 03EW] part (4) at the
  simplicial site** — every simplicial `A_•`-module is a quotient of a flat one.
* `Stacks.SimplicialModules.exists_isFlat_resolution`: **step 2 of the proof of
  [Stacks, Tag 09D2]** — every cochain complex of simplicial `A_•`-modules vanishing in degrees
  `> a` receives a degreewise epimorphic quasi-isomorphism from a cochain complex, again
  vanishing in degrees `> a`, all of whose terms are flat.
* `Stacks.SimplicialModules.exists_isFlat_resolution_of_isLE`: the same for a complex whose
  *cohomology* vanishes in degrees `> a`, which is the form in which the step applies to an
  object of `D(A_•)` after the first one.

## Implementation notes

**Which category the statement is in.** [Stacks, Tag 09D1] defines a simplicial `A_•`-module to
be a sheaf of modules over the sheaf of rings on `Δ × C` associated to `A_•`. That sheaf of rings
is `Stacks.SimplicialModules.simplicialCommRingSheaf`, read as a sheaf of rings by
`Stacks.SheafOfModules.Tensor.ringSheaf`, which is the spelling
`Stacks.SheafOfModules.FlatCover.exists_epi_from_isFlat` and
`AlgebraicGeometry.SheafOfModules.IsFlat` are stated at. The statements below are therefore given
for an arbitrary sheaf of commutative rings on a site and then specialised to
`simplicialCommRingSheaf`, whose sheaves of modules are the category of [Stacks, Tag 09D1].

**Flatness of a zero object.** [Stacks, Tag 05T7] asks the class of objects the resolution is
built from to contain a zero object. The sections of a zero sheaf of modules are a zero module,
which is flat, so its underlying presheaf of modules is objectwise flat; the sheaf associated to
an objectwise flat presheaf of modules is flat ([Stacks, Tag 03ET]) and the counit of
sheafification is invertible at a sheaf, so a zero sheaf of modules is flat.

**Sheafification on the simplicial site.** The side conditions of `exists_epi_from_isFlat` — that
abelian-group presheaves on `Δ × C` sheafify, and that sheafification inverts exactly the locally
bijective maps — hold on every site whose objects and morphisms lie in the coefficient universe,
by transport from a small model
(`CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall` and
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall`). `Δ`
contributes nothing to either universe, `SimplexCategory` being a `Type` with `Type`-valued homs,
so they are available here with no hypothesis on `C` beyond smallness, and with them the abelian
structure on sheaves of modules — which [Stacks, Tag 05T7] needs — is found by instance search.

## References

* [Stacks Project, Tag 09D2](https://stacks.math.columbia.edu/tag/09D2)
* [Stacks Project, Tag 09D1](https://stacks.math.columbia.edu/tag/09D1)
* [Stacks Project, Tag 09D0](https://stacks.math.columbia.edu/tag/09D0)
* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
* [Stacks Project, Tag 03ET](https://stacks.math.columbia.edu/tag/03ET)
* [Stacks Project, Tag 05T7](https://stacks.math.columbia.edu/tag/05T7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SheafOfModules (ringPresheaf)

universe u

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

namespace Stacks.SimplicialModules

section Site

variable {D : Type u} [Category.{u} D] {K : GrothendieckTopology D}
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
  (O : Sheaf K CommRingCat.{u})

/-- **A zero sheaf of modules is flat.** Its sections are a zero module, hence flat, so its
underlying presheaf of modules is objectwise flat; the sheaf associated to an objectwise flat
presheaf of modules is flat ([Stacks, Tag 03ET]), and the counit of sheafification is invertible
at a sheaf. -/
theorem isFlat_of_isZero
    {N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O)}
    (hN : IsZero N) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := O) N := by
  let a : ringPresheaf O.obj ⟶ (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O).obj := 𝟙 _
  have hli : Presheaf.IsLocallyInjective K a :=
    Presheaf.isLocallyInjective_of_injective K a fun _ _ _ h => h
  have hls : Presheaf.IsLocallySurjective K a :=
    Presheaf.isLocallySurjective_of_surjective K a fun _ x => ⟨x, rfl⟩
  have hval : AlgebraicGeometry.SheafOfModules.PresheafOfModules.IsFlat (O := O.obj)
      (Stacks.SheafOfModules.FlatCover.valPresheaf O N) := by
    apply AlgebraicGeometry.SheafOfModules.PresheafOfModules.isFlat_of_objectwise_flat
    intro V
    have : Subsingleton ((Stacks.SheafOfModules.FlatCover.valPresheaf O N).obj V) :=
      ModuleCat.isZero_iff_subsingleton.1
        (Functor.map_isZero
          (PresheafOfModules.evaluation (ringPresheaf O.obj) V)
          (Functor.map_isZero
            (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O)) hN))
    infer_instance
  have hsharp := Stacks.SheafOfModules.FlatSheafification.isFlat_sheafification K
    (O := O.obj) (Osharp := O) a (F := Stacks.SheafOfModules.FlatCover.valPresheaf O N) hval
  have hiso : IsIso ((PresheafOfModules.sheafificationAdjunction a).counit.app N) :=
    NatIso.isIso_app_of_isIso _ N
  exact Stacks.SheafOfModules.FlatRetract.isFlat_of_iso O
    (asIso ((PresheafOfModules.sheafificationAdjunction a).counit.app N)) hsharp

/-- Flatness, as an object property of sheaves of modules. This is the class the resolution of
[Stacks, Tag 05T7] is built from. -/
def isFlatProperty :
    ObjectProperty (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O)) :=
  fun N => AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := O) N

/-- The zero sheaf of modules is flat, so the flat sheaves of modules contain a zero object. -/
instance isFlatProperty_containsZero
    [HasSheafify K AddCommGrpCat.{u}] : (isFlatProperty O).ContainsZero := by
  obtain ⟨Z, hZ⟩ := HasZeroObject.zero
    (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O))
  exact ⟨Z, hZ, isFlat_of_isZero O hZ⟩

end Site

/-! ### The simplicial site -/

section Simplicial

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- Sheafification of abelian-group-valued presheaves exists for the topology on `Δ × C`
inherited along the projection to `C`. -/
instance simplicialProductTopology_hasSheafify :
    HasSheafify (projectionTopology C J) AddCommGrpCat.{u} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u, u, u}
    (projectionTopology C J)

/-- For the topology on `Δ × C` inherited along the projection to `C`, a morphism of
abelian-group-valued presheaves becomes an isomorphism after sheafification exactly when it is
locally bijective. -/
instance simplicialProductTopology_wEqualsLocallyBijective :
    (projectionTopology C J).WEqualsLocallyBijective AddCommGrpCat.{u} := by
  let : ((equivSmallModel.{u} (SimplexCategory × C)).inverse.inducedTopology
      (projectionTopology C J)).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstance
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, _, u, _, u}
    (projectionTopology C J)

variable (A : SimplicialObject (Sheaf J CommRingCat.{u}))

/-- **[Stacks, Tag 03EW] part (4) at the simplicial site of [Stacks, Tag 09D0].** Every
simplicial `A_•`-module — that is, every sheaf of modules over the sheaf of rings on `Δ × C`
associated to a simplicial sheaf of commutative rings `A_•`, as in [Stacks, Tag 09D1] — receives
an epimorphism from a flat one. -/
@[stacks 03EW "part (4) at the simplicial site Δ × C of 09D0"]
theorem exists_epi_isFlat_simplicial
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (simplicialCommRingSheaf J A))) :
    ∃ (N : SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (simplicialCommRingSheaf J A)))
      (p : N ⟶ M),
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
        (O := simplicialCommRingSheaf J A) N ∧ Epi p :=
  Stacks.SheafOfModules.FlatCover.exists_epi_from_isFlat (simplicialCommRingSheaf J A) M

/-- Every simplicial `A_•`-module receives an epimorphism from an object of `isFlatProperty`. -/
private theorem exists_epi_isFlatProperty (N : SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (simplicialCommRingSheaf J A))) :
    ∃ (P : SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (simplicialCommRingSheaf J A)))
      (_ : isFlatProperty (simplicialCommRingSheaf J A) P) (p : P ⟶ N), Epi p :=
  let ⟨P, p, hP, hp⟩ := exists_epi_isFlat_simplicial J A N
  ⟨P, hP, p, hp⟩

/-- **Step 2 of the proof of [Stacks, Tag 09D2].** Every cochain complex of simplicial
`A_•`-modules which vanishes in degrees `> a` receives a degreewise epimorphic
quasi-isomorphism from a cochain complex, again vanishing in degrees `> a`, all of whose terms
are flat.

This is the step whose source text is "every such complex is quasi-isomorphic to a bounded above
complex whose terms are flat modules, see Modules on Sites, Lemma 18.28.8": the cited lemma is
[Stacks, Tag 03EW], whose part (4) at this site is
`Stacks.SimplicialModules.exists_epi_isFlat_simplicial`, and the passage from a flat quotient of
each object to a resolution of a bounded above complex is [Stacks, Tag 05T7].

It carries no [Stacks, Tag 09D2] attribute. Tag 09D2 is a single lemma and this is a step of its
*proof*, not a numbered part of its statement: it mentions neither `L π_!`, nor the derived tensor
product, nor an object of `D(A_•)`. The tag belongs on a declaration stating the lemma. -/
theorem exists_isFlat_resolution (a : ℤ)
    (M : CochainComplex
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (simplicialCommRingSheaf J A))) ℤ)
    [M.IsStrictlyLE a] :
    ∃ (L : CochainComplex
        (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (simplicialCommRingSheaf J A))) ℤ)
      (f : L ⟶ M) (_ : ∀ n, Epi (f.f n)) (_ : QuasiIso f)
      (_ : ∀ n, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
        (O := simplicialCommRingSheaf J A) (L.X n)), L.IsStrictlyLE a :=
  (CochainComplex.exists_quasiIso_prop _ (exists_epi_isFlatProperty J A) a).1 M

/-- **Step 2 of the proof of [Stacks, Tag 09D2], for a complex that is bounded above in
cohomology.** This is the form the step takes after the first one: an object of `D(A_•)`
supported in degrees `≤ a` is represented by a complex, vanishing in degrees `> a`, all of whose
terms are flat. -/
theorem exists_isFlat_resolution_of_isLE (a : ℤ)
    (M : CochainComplex
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (simplicialCommRingSheaf J A))) ℤ)
    [M.IsLE a] :
    ∃ (L : CochainComplex
        (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (simplicialCommRingSheaf J A))) ℤ)
      (f : L ⟶ M) (_ : QuasiIso f)
      (_ : ∀ n, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
        (O := simplicialCommRingSheaf J A) (L.X n)), L.IsStrictlyLE a :=
  (CochainComplex.exists_quasiIso_prop _ (exists_epi_isFlatProperty J A) a).2 M

end Simplicial

end Stacks.SimplicialModules

end
