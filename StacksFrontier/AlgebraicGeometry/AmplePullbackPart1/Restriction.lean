module

public import StacksFrontier.AlgebraicGeometry.AmplePullbackPart1.TensorPowerTensor
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.Nonvanishing

/-!
# Global sections of a module restricted to an open subscheme

`Γ(U.ι^* G, ⊤) ≅ Γ(G, U)` for `U : X.Opens` and `G : X.Modules`, where the restriction is the
module pullback along the open immersion of `U`.

`StacksFrontier/AlgebraicGeometry/AmpleQuasiAffinePullback/Basic.lean` lists this comparison as the
third of the four inputs needed for part (1) of [Stacks, Tag 0892], saying that
`Stacks.NonvanishingPullback.pullbackGlobalSection` is the forward map for an arbitrary morphism
and that "the inverse for an open immersion is what turns the ampleness that
`Stacks.RelativeAmple.IsRelativelyAmple` asserts on the subscheme `f⁻¹V` into sections of
`L ^⊗ n` over the open `f⁻¹V` of `X`". **It is already available**: it is three existing facts
composed, two of which hold by `rfl`.

## Main definitions

* `Stacks.AmplePullbackPart1.restrictIsoPullback`: the restriction of `G` along `U.ι` in Mathlib's
  `AlgebraicGeometry.Scheme.Modules.restrictFunctor` sense is isomorphic to the module pullback
  `RingedSpaceModuleAdjunction.modulePullback U.ι.toLRSHom.toShHom`.
* `Stacks.AmplePullbackPart1.restrictGlobalSectionsIso`: **the comparison.** The global sections
  of the restriction of `G` to `U` are the sections of `G` over the image of the ambient open of
  `U`, which is `U`.
* `Stacks.AmplePullbackPart1.sectionOfRestrictGlobalSection`: the comparison composed with the
  transport along `AlgebraicGeometry.Scheme.Opens.ι_image_top`, giving a section of `G` over `U`
  on the nose. This is the map a consumer wants.
* `Stacks.AmplePullbackPart1.sectionOfRestrictGlobalSection_pullbackGlobalSection`: the
  comparison carries the pullback of a global section along `U.ι` to its restriction to `U`.

## Main results

* `Stacks.AmplePullbackPart1.modulePullback_obj_eq_pullback_obj`: the repository's module pullback
  along a morphism of schemes **is** Mathlib's `AlgebraicGeometry.Scheme.Modules.pullback`, by
  `rfl`. `StacksFrontier/AlgebraicGeometry/IdealSheafRestrict/Basic.lean` records this in prose
  (`structureSheafRing X.toSheafedSpace = X.ringCatSheaf`,
  `structureSheafHom f.toLRSHom.toShHom = f.toRingCatSheafHom`); here it is a statement.
* `Stacks.AmplePullbackPart1.restrictGlobalSections_eq`: the global sections of the Mathlib
  restriction **are** the sections over the image, by `rfl`. This is
  `AlgebraicGeometry.Scheme.Modules.restrictAppIso`, which is `Iso.refl`, read off at `⊤`.

## Implementation notes

**Why the comparison is not stated with `Γ(G, U)` on the right.** The two sides of
`AlgebraicGeometry.Scheme.Opens.ι_image_top`, `U.ι ''ᵁ ⊤` and `U`, are equal opens of `X` but not
the same term, so `Γ(G, U.ι ''ᵁ ⊤)` and `Γ(G, U)` are modules over the two spellings
`Γ(X, U.ι ''ᵁ ⊤)` and `Γ(X, U)` of one ring. An `Iso` between them would not typecheck: it would
have to live in two different instances of `ModuleCat`. The transport across that equality is
therefore a `G.presheaf.map (eqToHom _).op`, a semilinear map and not a morphism of either
`ModuleCat`, and it is kept separate in
`Stacks.AmplePullbackPart1.sectionOfRestrictGlobalSection`. This is the same device
`Stacks.AmpleQuasiAffinePullback.exists_isAffineOpen_basicOpen_of_isQuasiAffine` uses for the
structure sheaf.

**The isomorphism of modules is evaluated at `⊤` by hand.** `Γ(-, ⊤)` is not set up as a functor
on `U.toScheme.Modules` in this repository, and there is no `IsIso` instance for
`AlgebraicGeometry.Scheme.Modules.Hom.app` of an isomorphism, so the two cancellation equations
are discharged from `Hom.comp_app` and `Hom.id_app`, both `rfl` in Mathlib.

## What this does *not* give

The nonvanishing locus of the resulting section over `U` is not compared with the nonvanishing
locus of the section of the restriction it came from. `Stacks.Ample.nonvanishingLocus` is defined
for *global* sections only, so there is nothing yet to compare it to; that bookkeeping, and not
this comparison, is what the assembly of part (1) still owes besides [Stacks, Tag 01PW]. No tag
is attached.

## References

* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.AmplePullbackPart1

variable {X : Scheme.{u}} (U : X.Opens) (G : X.Modules)

/-- **The repository's module pullback along a morphism of schemes is Mathlib's.** This holds by
`rfl`: `structureSheafRing X.toSheafedSpace` is `X.ringCatSheaf` and
`structureSheafHom f.toLRSHom.toShHom` is `f.toRingCatSheafHom`. The two are nevertheless not
interchangeable to the elaborator, `AlgebraicGeometry.Scheme.Modules` and `TopCat.Sheaf` both
being plain definitions, which is why the identification is given a name. -/
theorem modulePullback_obj_eq_pullback_obj {Y : Scheme.{u}} (f : X ⟶ Y) (N : Y.Modules) :
    (modulePullback f.toLRSHom.toShHom).obj N = (Scheme.Modules.pullback f).obj N := rfl

/-- **The global sections of the restriction of `G` to `U` are the sections of `G` over the image
of the ambient open of `U`.** Mathlib's `AlgebraicGeometry.Scheme.Modules.restrictAppIso` is
`Iso.refl`, so this is an equality and not merely an isomorphism. -/
theorem restrictGlobalSections_eq :
    Γ((Scheme.Modules.restrictFunctor U.ι).obj G, (⊤ : U.toScheme.Opens)) =
      Γ(G, U.ι ''ᵁ (⊤ : U.toScheme.Opens)) := rfl

/-- **Restriction along the open immersion of `U` is the module pullback along it.** Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` at `G`, with the target read in the
repository's spelling by `Stacks.AmplePullbackPart1.modulePullback_obj_eq_pullback_obj`. -/
def restrictIsoPullback :
    (Scheme.Modules.restrictFunctor U.ι).obj G ≅ (modulePullback U.ι.toLRSHom.toShHom).obj G :=
  (Scheme.Modules.restrictFunctorIsoPullback U.ι).app G

/-- **`Γ(U.ι^* G, ⊤) ≅ Γ(G, U.ι ''ᵁ ⊤)`**, the third of the four inputs
`StacksFrontier/AlgebraicGeometry/AmpleQuasiAffinePullback/Basic.lean` lists as needed for part (1)
of [Stacks, Tag 0892].

The right-hand side is `Γ(G, U)` after `AlgebraicGeometry.Scheme.Opens.ι_image_top`; see
`Stacks.AmplePullbackPart1.sectionOfRestrictGlobalSection` for the composite, and the module
documentation for why the equality of opens cannot be absorbed into this isomorphism. -/
def restrictGlobalSectionsIso :
    Γ((modulePullback U.ι.toLRSHom.toShHom).obj G, (⊤ : U.toScheme.Opens)) ≅
      Γ(G, U.ι ''ᵁ (⊤ : U.toScheme.Opens)) where
  hom := Scheme.Modules.Hom.app (restrictIsoPullback U G).inv ⊤
  inv := Scheme.Modules.Hom.app (restrictIsoPullback U G).hom ⊤
  hom_inv_id :=
    congrArg (fun φ => Scheme.Modules.Hom.app φ ⊤) (restrictIsoPullback U G).inv_hom_id
  inv_hom_id :=
    congrArg (fun φ => Scheme.Modules.Hom.app φ ⊤) (restrictIsoPullback U G).hom_inv_id

/-- **A global section of the restriction of `G` to `U`, read as a section of `G` over `U`.**
`Stacks.AmplePullbackPart1.restrictGlobalSectionsIso` followed by the restriction map of `G`
along `AlgebraicGeometry.Scheme.Opens.ι_image_top`, which is an isomorphism of modules over two
spellings of one ring and so is taken as a plain presheaf transport. -/
def sectionOfRestrictGlobalSection
    (s : Γ((modulePullback U.ι.toLRSHom.toShHom).obj G, (⊤ : U.toScheme.Opens))) : Γ(G, U) :=
  ConcreteCategory.hom (G.presheaf.map (eqToHom U.ι_image_top.symm).op)
    (ConcreteCategory.hom (restrictGlobalSectionsIso U G).hom s)

/-- **The unit of the pullback adjunction along `U.ι`, at `⊤`, is the restriction map followed by
the comparison.** Restriction and pullback are both left adjoint to the pushforward along `U.ι`,
and the unique isomorphism between two left adjoints carries one unit to the other. -/
theorem pullbackPushforwardAdjunction_unit_app_top :
    Scheme.Modules.Hom.app
        ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app G) (⊤ : X.Opens)
      = G.presheaf.map (homOfLE (le_top : U.ι ''ᵁ (⊤ : U.toScheme.Opens) ≤ ⊤)).op ≫
          Scheme.Modules.Hom.app (restrictIsoPullback U G).hom (⊤ : U.toScheme.Opens) :=
  (congrArg (fun φ => Scheme.Modules.Hom.app φ (⊤ : X.Opens))
    (Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction U.ι)
      (Scheme.Modules.pullbackPushforwardAdjunction U.ι) G)).symm

/-- **The pullback of a global section along `U.ι` is its restriction to `U`, read through the
comparison.** -/
theorem pullbackGlobalSection_eq (g : Γ(G, ⊤)) :
    Stacks.NonvanishingPullback.pullbackGlobalSection U.ι G g
      = ConcreteCategory.hom (restrictGlobalSectionsIso U G).inv
          (ConcreteCategory.hom
            (G.presheaf.map (homOfLE (le_top : U.ι ''ᵁ (⊤ : U.toScheme.Opens) ≤ ⊤)).op) g) := by
  have h0 : Stacks.NonvanishingPullback.pullbackGlobalSection U.ι G g
      = ConcreteCategory.hom (Scheme.Modules.Hom.app
          ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app G) (⊤ : X.Opens)) g := rfl
  rw [h0, pullbackPushforwardAdjunction_unit_app_top U G]
  rfl

/-- **The comparison inverts the pullback of a global section.** The section of `G` over `U`
attached to `U.ι^* g` is the restriction of `g` to `U`. -/
theorem sectionOfRestrictGlobalSection_pullbackGlobalSection (g : Γ(G, ⊤)) :
    sectionOfRestrictGlobalSection U G
        (Stacks.NonvanishingPullback.pullbackGlobalSection U.ι G g)
      = ConcreteCategory.hom (G.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) g := by
  have hcomp : G.presheaf.map (homOfLE (le_top : U.ι ''ᵁ (⊤ : U.toScheme.Opens) ≤ ⊤)).op ≫
      G.presheaf.map (eqToHom U.ι_image_top.symm).op
      = G.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op := by
    rw [← Functor.map_comp, ← op_comp]
    congr 1
  have e1 : ConcreteCategory.hom (restrictGlobalSectionsIso U G).hom
        (Stacks.NonvanishingPullback.pullbackGlobalSection U.ι G g)
      = ConcreteCategory.hom
          (G.presheaf.map (homOfLE (le_top : U.ι ''ᵁ (⊤ : U.toScheme.Opens) ≤ ⊤)).op) g := by
    rw [pullbackGlobalSection_eq U G g, ← ConcreteCategory.comp_apply,
      (restrictGlobalSectionsIso U G).inv_hom_id]
    rfl
  calc sectionOfRestrictGlobalSection U G
        (Stacks.NonvanishingPullback.pullbackGlobalSection U.ι G g)
      = ConcreteCategory.hom (G.presheaf.map (eqToHom U.ι_image_top.symm).op)
          (ConcreteCategory.hom (restrictGlobalSectionsIso U G).hom
            (Stacks.NonvanishingPullback.pullbackGlobalSection U.ι G g)) := rfl
    _ = ConcreteCategory.hom (G.presheaf.map (eqToHom U.ι_image_top.symm).op)
          (ConcreteCategory.hom
            (G.presheaf.map (homOfLE (le_top : U.ι ''ᵁ (⊤ : U.toScheme.Opens) ≤ ⊤)).op) g) := by
        rw [e1]
    _ = ConcreteCategory.hom (G.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) g := by
        rw [← ConcreteCategory.comp_apply, hcomp]

end Stacks.AmplePullbackPart1

end
