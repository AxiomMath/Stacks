module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ChangeOfRingsAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicFunctions
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Meromorphic sections of a module on an algebraic space

Let `F` be an algebraic space over a scheme `S` and let `M` be a sheaf of `𝒪_F`-modules on its
small étale site.  The sheaf of *meromorphic sections* of `M` is `M ⊗_{𝒪_F} 𝒦_F`, the extension
of scalars of `M` along the canonical map `𝒪_F ⟶ 𝒦_F` into the sheaf of meromorphic functions,
and a *meromorphic section* of `M` is a global section of that sheaf.  Equivalently, it is the
sheafification of the presheaf of sectionwise localizations `U ↦ 𝒮_F(U)⁻¹ M(U)`.

A meromorphic section of `M` is *regular* when the map `𝒦_F ⟶ 𝒦_F(M)` it induces is injective.

## Main definitions

* `AlgebraicGeometry.Space.meromorphicRingedSite` is the small étale site of `F` carrying the
  sheaf of meromorphic functions as its structure sheaf.
* `AlgebraicGeometry.Space.meromorphicSectionSheaf` is `𝒦_F(M)` and
  `AlgebraicGeometry.Space.MeromorphicSection` its module of global sections.
* `AlgebraicGeometry.Space.IsRegularMeromorphicSection` is regularity of a meromorphic section.

## Implementation notes

Extension of scalars is `Stacks.PresheafOfModules.ChangeOfRings.changeOfRings` of Stacks 03CU;
the sheafification of the resulting presheaf of modules is what Stacks 0EN5 describes as the
sheafification of the sectionwise localizations, the two being identified by Stacks 0EMD.

The module universe changes in the construction.  The small étale site has objects in
`Type (u + 1)` while its rings of sections live in `Type u`, so sheafifying presheaves of
modules on it needs abelian groups in a universe at least `u + 1`; the module sheaf one starts
from, however, must be allowed to have sections in `Type u`, since `M = 𝒪_F` is the case
`𝒦_F(𝒪_F) = 𝒦_F`.  So extension of scalars is performed in the module universe `max u z` of the
input and then lifted to `max (u + 1) z` before sheafification.  The sheafification instances
in that universe are obtained by transport from a small model of the site, as for the structure
sheaf, and are recorded here because the library's own instances fix the coefficient universe to
`u`.

Regularity of a meromorphic section is expressed chartwise, by injectivity of multiplication by
its value on each étale chart, rather than as a monomorphism of sheaves; this is what lets the
sheaf of meromorphic sections live in a larger universe than the sheaf of meromorphic
functions.  Stacks 0ENB and its applications concern an invertible module, but regularity itself
does not use invertibility, so it is defined for an arbitrary module sheaf.

## References

* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
* [Stacks Project, Tag 0ENB](https://stacks.math.columbia.edu/tag/0ENB)
-/

@[expose] public section

open CategoryTheory Opposite

universe u z

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- Sheafification of presheaves of abelian groups on the small étale site of `F`, in a universe
containing the objects of the site, together with the characterization of local equivalences as
locally bijective morphisms.

Both are transported from a small model of the site, as in
`AlgebraicGeometry.Space.SmallEtale.instHasSheafify`; that instance fixes the universe of the
coefficients to the universe `u` of the schemes, which is too small for sheafifying presheaves
of modules whose sections are indexed by the objects of the site. -/
noncomputable def moduleSheafificationData :
    Σ' L : ((SmallEtale B S hS F)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) z}) ⥤
      Sheaf (SmallEtale.topology B S hS F) AddCommGrpCat.{max (u + 1) z},
      Nonempty (L ⊣ sheafToPresheaf (SmallEtale.topology B S hS F)
        AddCommGrpCat.{max (u + 1) z}) ∧
      (SmallEtale.topology B S hS F).WEqualsLocallyBijective AddCommGrpCat.{max (u + 1) z} := by
  have smallSiteInstances (C : Type (max (u + 1) z)) [SmallCategory C]
      (K : GrothendieckTopology C) :
      HasSheafify K AddCommGrpCat.{max (u + 1) z} ∧
        K.WEqualsLocallyBijective AddCommGrpCat.{max (u + 1) z} :=
    ⟨inferInstance, inferInstance⟩
  have := (smallSiteInstances _ ((equivSmallModel.{max (u + 1) z} _).inverse.inducedTopology
    (SmallEtale.topology B S hS F))).1
  have := (smallSiteInstances _ ((equivSmallModel.{max (u + 1) z} _).inverse.inducedTopology
    (SmallEtale.topology B S hS F))).2
  have : HasSheafify (SmallEtale.topology B S hS F) AddCommGrpCat.{max (u + 1) z} :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, max (u + 1) z}
      (SmallEtale.topology B S hS F) _
  exact ⟨presheafToSheaf (SmallEtale.topology B S hS F) _,
    ⟨sheafificationAdjunction (SmallEtale.topology B S hS F) _⟩,
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{_, _, _, _,
      max (u + 1) z} (SmallEtale.topology B S hS F)⟩

/-- Presheaves of abelian groups on the small étale site of `F`, in a universe containing the
objects of the site, admit sheafification.

Priority 50, below the `low` of `AlgebraicGeometry.Space.SmallEtale.instHasSheafify`: the
section universe `max (u + 1) z` is not determined by the goal, so at any higher priority search
tries this ahead of the instances pinned at the universe `u` of the schemes and then stalls on
the universe constraint. -/
noncomputable instance (priority := 50) moduleHasWeakSheafify :
    HasWeakSheafify (SmallEtale.topology B S hS F) AddCommGrpCat.{max (u + 1) z} :=
  ⟨⟨(moduleSheafificationData.{u, z} B S hS F).1,
    (moduleSheafificationData.{u, z} B S hS F).2.1⟩⟩

/-- The local equivalences of presheaves of abelian groups on the small étale site of `F`, in a
universe containing the objects of the site, are exactly the locally bijective morphisms.
Priority 50, for the reason given on `AlgebraicGeometry.Space.moduleHasWeakSheafify`. -/
instance (priority := 50) moduleWEqualsLocallyBijective :
    (SmallEtale.topology B S hS F).WEqualsLocallyBijective AddCommGrpCat.{max (u + 1) z} :=
  (moduleSheafificationData.{u, z} B S hS F).2.2

/-- The small étale site of the algebraic space `F`, endowed with its sheaf of meromorphic
functions `𝒦_F` as structure sheaf. -/
noncomputable abbrev meromorphicRingedSite (hF : IsAlgebraicSpace B S hS F) :
    RingedSite.{u + 1, u, u} where
  C := SmallEtale B S hS F
  J := SmallEtale.topology B S hS F
  O := meromorphicFunctionSheaf B S hS F hF

/-- Extension of scalars of a sheaf of `𝒪_F`-modules along `𝒪_F ⟶ 𝒦_F`, as a presheaf of
`𝒦_F`-modules lifted to a universe in which the small étale site admits sheafification. -/
noncomputable def meromorphicSectionPresheaf (hF : IsAlgebraicSpace B S hS F)
    (M : Modules.{u, max u z} B S hS F hF) :
    PresheafOfModules.{max (u + 1) z}
      (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS F hF).O).obj := by
  let hP : PresheafOfModules.{max u z}
      (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS F hF).O).obj :=
    (Stacks.PresheafOfModules.ChangeOfRings.changeOfRings
      (toMeromorphicFunctionSheaf B S hS F hF).hom).obj M.val
  letI (U : (SmallEtale B S hS F)ᵒᵖ) :
      Module
          ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS F hF).O).obj.obj U)
        ((hP.presheaf ⋙ AddCommGrpCat.uliftFunctor.{u + 1}).obj U) :=
    inferInstanceAs
      (Module
          ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS F hF).O).obj.obj U)
        (ULift.{u + 1} (hP.obj U)))
  exact PresheafOfModules.ofPresheaf
    (hP.presheaf ⋙ AddCommGrpCat.uliftFunctor.{u + 1}) fun _ _ f r m =>
      ULift.ext _ _ (hP.map_smul f r m.down)

/-- The sheaf `𝒦_F(M)` of *meromorphic sections* of a sheaf of `𝒪_F`-modules `M`: the extension
of scalars of `M` along `𝒪_F ⟶ 𝒦_F`, sheafified. -/
@[stacks 0EN5 "part (1)"]
noncomputable abbrev meromorphicSectionSheaf (hF : IsAlgebraicSpace B S hS F)
    (M : Modules.{u, max u z} B S hS F hF) :
    SheafOfModules.{max (u + 1) z}
      (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS F hF).O) :=
  letI := moduleHasWeakSheafify.{u, z} B S hS F
  letI := moduleWEqualsLocallyBijective.{u, z} B S hS F
  (PresheafOfModules.sheafification
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS F hF).O).obj)).obj
    (meromorphicSectionPresheaf.{u, z} B S hS F hF M)

/-- A *meromorphic section* of a sheaf of `𝒪_F`-modules `M` is a global section of the sheaf
`𝒦_F(M)` of meromorphic sections of `M`. -/
@[stacks 0EN5 "part (2)"]
noncomputable abbrev MeromorphicSection (hF : IsAlgebraicSpace B S hS F)
    (M : Modules.{u, max u z} B S hS F hF) : Type _ :=
  (meromorphicSectionSheaf.{u, z} B S hS F hF M).sections

/-- A meromorphic section `s` of a sheaf of `𝒪_F`-modules `L` is *regular* when the induced map
`𝒦_F ⟶ 𝒦_F(L)`, multiplication by `s`, is injective; this is tested on every étale chart of `F`. -/
@[stacks 0ENB, ega "IV 20.1.8" "regular section defn"]
noncomputable abbrev IsRegularMeromorphicSection (hF : IsAlgebraicSpace B S hS F)
    (L : Modules.{u, max u z} B S hS F hF)
    (s : MeromorphicSection.{u, z} B S hS F hF L) : Prop :=
  ∀ V : SmallEtale B S hS F,
    Function.Injective fun r : (Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS F hF).O).obj.obj (op V) =>
      r • s.eval (op V)

end AlgebraicGeometry.Space

end
