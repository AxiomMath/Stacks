module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.GeneratedIdealSheaf
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.LocalCalculation
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.UnboundedGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.LerayForUnboundedSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.CohomologyOfModuleOverObject

/-!
# `RΓ(U, K) = RΓ(𝒞/U, K|_U)` with its module structure, for the unbounded derived category

Let `(𝒞, 𝒪)` be a ringed site and `U` an object of `𝒞`. [Stacks, Tag 0D6F] says that the
cohomology of `K ∈ D(𝒪)` over `U` is the cohomology of `K|_U` on the localized ringed site
`(𝒞/U, 𝒪_U)`. This file proves the statement **before passing to cohomology and with the
`𝒪(U)`-module structure kept**:

```
RΓ(U, -)  ≅  (-)|_U ⋙ RΓ(𝒞/U, -)   as functors  D(𝒪) ⥤ D(𝒪(U)).
```

`RΓ(U, -)` on the left is `AlgebraicGeometry.RingedSite.derivedSectionsOverObject` of
`LocalCalculation.lean`, the total right derived functor of `Γ(U, -)` with values in `D(𝒪(U))`;
`RΓ(𝒞/U, -)` on the right is
`AlgebraicGeometry.RingedSite.derivedGlobalSectionsOverUnbounded` of
`UnboundedGlobalSections.lean` on the ringed site `𝒞/U`, taken `𝒪(U)`-linearly along the ring
map which reads a section of `𝒪` over `U` as a global section of `𝒪_U`.

The `AddCommGrpCat`-valued form of the same comparison is
`Stacks.Cohomology.LerayUnbounded.derivedSectionsOverObjectIsoSlice`; what is added here is the
module structure, which is what a statement about derived completion along an ideal of `𝒪(U)`
needs, and which the forgetful version cannot see.

## Main definitions

* `AlgebraicGeometry.RingedSite.sectionsRingHomOfTerminal`: the ring map `𝒪(T) ⟶ Γ(𝒞, 𝒪)` reading
  a section over a terminal object `T` of the site as a global section.
* `AlgebraicGeometry.RingedSite.overSectionsRingHom`: the ring map `𝒪(U) ⟶ Γ(𝒞/U, 𝒪_U)` reading
  a section over `U` as a global section of the structure sheaf of the localized site; that is
  the previous map at the terminal object `𝟙 U` of the localized site.
* `AlgebraicGeometry.RingedSite.moduleGlobalSectionsOverIsoSectionsTerminal`: on a site with a
  terminal object `T`, `A`-linear global sections are `A`-linear sections over `T`.
* `AlgebraicGeometry.RingedSite.moduleSectionsOverIsoSlice`: the underived comparison
  `Γ(U, ℱ) ≅ Γ(𝒞/U, ℱ|_U)`, `𝒪(U)`-linearly.
* `AlgebraicGeometry.RingedSite.derivedSectionsOverObjectIsoSliceModule`: **the comparison
  above**, `RΓ(U, -) ≅ (-)|_U ⋙ RΓ(𝒞/U, -)`.

## Implementation notes

*Why a terminal object appears.* Global sections on a site are `Hom_𝒪(𝒪, -)`, and the identity
arrow of `U` is the terminal object of `𝒞/U` (`CategoryTheory.Over.mkIdTerminal`), so global
sections on the slice are sections over that object, which are the sections over `U` of the
original sheaf. The scalars match because restricting along the identity does nothing:
`sectionsEval_comp_overSectionsRingHom`.

*How the derived statement follows from the underived one.* Restriction to the slice is exact
and carries K-injective complexes to K-injective complexes ([Stacks, Tag 08FI],
`Stacks.Cohomology.Localization.isKInjective_over`), so the composite of the two total right
derived functors is the total right derived functor of the composite:
`Stacks.Cohomology.LerayUnbounded.derivedCompIso`. Derived restriction is then replaced by the
functor restriction induces on the unbounded derived categories, being exact, which is
`Stacks.Cohomology.Localization.derivedRestrictionIsoMapDerivedCategory`; that is the spelling
in which [Stacks, Tag 0A0F] states the restriction of a derived completion.

## References

* [Stacks Project, Tag 08FI](https://stacks.math.columbia.edu/tag/08FI)
* [Stacks Project, Tag 0D6F](https://stacks.math.columbia.edu/tag/0D6F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasSheafCompose_forget₂_ringCat

section TerminalSections

variable (Y : RingedSite.{u, u, u}) (A : Type u) [CommRing A]
  (ρ : A →+* RingCat.sectionsSubring ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj)

/-- **The compatible family of local sections determined by a value over a terminal object.**
Its value over `V` is the restriction of the given section along the unique arrow `V ⟶ T`. -/
def sectionsOfTerminalValue {T : Y.C} (hT : IsTerminal T)
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) (x : M.val.obj (op T)) :
    M.sections :=
  PresheafOfModules.sectionsMk (fun V => M.val.map (hT.from V.unop).op x) (fun V W g => by
    rw [← PresheafOfModules.map_comp_apply]
    exact PresheafOfModules.congr_map_apply _ (Quiver.Hom.unop_inj (hT.hom_ext _ _)) x)

/-- The component of `moduleGlobalSectionsOverIsoSectionsTerminal`: evaluation of a global
section over the terminal object `T` is an `A`-linear bijection from `Hom_𝒪(𝒪, ℱ)` to `ℱ(T)`.

It is injective because a compatible family is determined by its value over `T`, and surjective
because `sectionsOfTerminalValue` produces a family with a prescribed value there. The scalars
match because `a` acts on `Hom_𝒪(𝒪, ℱ)` by multiplication by the global section `ρ a`, whose
value over `T` is the scalar acting on `ℱ(T)`. -/
def moduleGlobalSectionsOverIsoSectionsTerminalApp {T : Y.C} (hT : IsTerminal T)
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    (moduleGlobalSectionsOver Y A ρ).obj M ≅
      (moduleSectionsOver Y T ((sectionsEval (op T)).comp ρ)).obj M :=
  LinearEquiv.toModuleIso (LinearEquiv.ofBijective
    ({ toFun := fun f => (M.unitHomEquiv f).val (op T)
       map_add' := fun _ _ => rfl
       map_smul' := fun a f => by
         rw [smul_moduleGlobalSectionsOver]
         exact ((f : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⟶ M).val.app
           (op T)).hom.map_smul _ _ } :
      (moduleGlobalSectionsOver Y A ρ).obj M →ₗ[A]
        (moduleSectionsOver Y T ((sectionsEval (op T)).comp ρ)).obj M)
    ⟨by
      intro f g hfg
      apply M.unitHomEquiv.injective
      refine PresheafOfModules.sections_ext _ _ (fun V => ?_)
      have hf := PresheafOfModules.sections_property (M.unitHomEquiv f) (hT.from V.unop).op
      have hg := PresheafOfModules.sections_property (M.unitHomEquiv g) (hT.from V.unop).op
      exact hf.symm.trans ((congrArg (M.val.map (hT.from V.unop).op) hfg).trans hg),
     by
      intro x
      refine ⟨M.unitHomEquiv.symm (sectionsOfTerminalValue Y hT M x), ?_⟩
      change (M.unitHomEquiv (M.unitHomEquiv.symm _)).val (op T) = x
      rw [Equiv.apply_symm_apply]
      refine (PresheafOfModules.congr_map_apply M.val
        (show (hT.from T).op = 𝟙 (op T) from Quiver.Hom.unop_inj (hT.hom_ext _ _)) x).trans ?_
      simp only [PresheafOfModules.map_id]
      rfl⟩)

/-- **`A`-linear global sections on a site with a terminal object `T` are the `A`-linear
sections over `T`.** The scalars on the right are those of `ρ` evaluated at `T`. -/
def moduleGlobalSectionsOverIsoSectionsTerminal {T : Y.C} (hT : IsTerminal T) :
    moduleGlobalSectionsOver Y A ρ ≅ moduleSectionsOver Y T ((sectionsEval (op T)).comp ρ) :=
  NatIso.ofComponents (moduleGlobalSectionsOverIsoSectionsTerminalApp Y A ρ hT)
    (fun _ => rfl)

/-- **A section of `𝒪` over a terminal object of the site, read as a global section**, as a ring
map `𝒪(T) ⟶ Γ(𝒞, 𝒪)`: the compatible family whose value over `V` is the restriction of the given
section along the unique arrow `V ⟶ T`.

This is the ring map along which a sheaf of `A`-algebras presented by a ring map `A ⟶ 𝒪(T)` is
read as one presented by `A ⟶ Γ(𝒞, 𝒪)`, which is the form
`AlgebraicGeometry.RingedSite.moduleGlobalSectionsOver` takes its scalars in. -/
def sectionsRingHomOfTerminal {T : Y.C} (hT : IsTerminal T) :
    ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj.obj (op T) →+*
      RingCat.sectionsSubring ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj where
  toFun b :=
    ⟨(Stacks.SheafOfModules.terminalSection ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) T hT
        b).val,
      (Stacks.SheafOfModules.terminalSection ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) T hT
        b).property⟩
  map_one' := by ext V; exact map_one _
  map_mul' _ _ := by ext V; exact map_mul _ _ _
  map_zero' := by ext V; exact map_zero _
  map_add' _ _ := by ext V; exact map_add _ _ _

/-- **The global section attached to a section over a terminal object has that section as its
value there**: the unique arrow `T ⟶ T` is the identity, and restricting along it changes
nothing. -/
theorem sectionsEval_comp_sectionsRingHomOfTerminal {T : Y.C} (hT : IsTerminal T) :
    (sectionsEval (X := Y) (op T)).comp (sectionsRingHomOfTerminal Y hT) =
      RingHom.id (((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj.obj (op T)) := by
  refine RingHom.ext (fun b => ?_)
  change ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj.map (hT.from T).op b = b
  rw [hT.from_self, op_id, ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj.map_id]
  rfl

end TerminalSections

section Slice

variable (X : RingedSite.{u, u, u}) (U : X.C)

/-- **A section of `𝒪` over `U`, read as a global section of the structure sheaf `𝒪_U` of the
localized ringed site `(𝒞/U, 𝒪_U)`**, as a ring map `𝒪(U) ⟶ Γ(𝒞/U, 𝒪_U)`. Its value over an
object `V ⟶ U` of `𝒞/U` is the restriction of the section along that arrow.

This is `AlgebraicGeometry.RingedSite.sectionsRingHomOfTerminal` at the terminal object `𝟙 U` of
the localized site. It is the ring map which makes `𝒪_U` a sheaf of `𝒪(U)`-algebras, and so the
one along which [Stacks, Tag 0BLX] is read on the localized site in [Stacks, Tag 0CQI]. -/
def overSectionsRingHom :
    sectionRing X U →+*
      RingCat.sectionsSubring ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)).obj :=
  sectionsRingHomOfTerminal (X.over U) (T := Over.mk (𝟙 U)) Over.mkIdTerminal

/-- **The global section of `𝒪_U` attached to a section of `𝒪` over `U` has that section as its
value over the terminal object**: restricting along the identity changes nothing. -/
theorem sectionsEval_comp_overSectionsRingHom :
    (sectionsEval (X := X.over U) (op (Over.mk (𝟙 U)))).comp (overSectionsRingHom X U) =
      RingHom.id (sectionRing X U) :=
  sectionsEval_comp_sectionsRingHomOfTerminal (X.over U) Over.mkIdTerminal

/-- The two readings of a section of `𝒪` over `U` as a global section of `𝒪_U` — through
`overSectionsRingHom` and through `globalSectionOfTerminalSection` — agree. -/
theorem globalSectionOfSections_overSectionsRingHom (b : sectionRing X U) :
    globalSectionOfSections (X := X.over U) (overSectionsRingHom X U b) =
      globalSectionOfTerminalSection (X := X.over U) Over.mkIdTerminal b := by
  refine (Presheaf.globalSectionsEquivSections _).injective (Subtype.ext (funext fun V => ?_))
  exact (globalSectionVal_globalSectionOfSections _ V).trans
    (globalSectionVal_globalSectionOfTerminalSection (X := X.over U) Over.mkIdTerminal b V).symm

/-- **[Stacks, Tag 0D6F] before deriving, `𝒪(U)`-linearly**: the sections of a sheaf of
`𝒪`-modules over `U` are the global sections of its restriction to `(𝒞/U, 𝒪_U)`, as
`𝒪(U)`-modules and naturally in the sheaf. -/
def moduleSectionsOverIsoSlice :
    SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U ⋙
        moduleGlobalSectionsOver (X.over U) (sectionRing X U) (overSectionsRingHom X U) ≅
      moduleSectionsOver X U (RingHom.id (sectionRing X U)) :=
  Functor.isoWhiskerLeft _
      (moduleGlobalSectionsOverIsoSectionsTerminal (X.over U) (sectionRing X U)
        (overSectionsRingHom X U) (T := Over.mk (𝟙 U)) Over.mkIdTerminal) ≪≫
    eqToIso (by rw [sectionsEval_comp_overSectionsRingHom]; rfl)

/-- Additivity of `𝒪(U)`-linear global sections on the localized site, in the spelling
`(𝒞/U, 𝒪_U)` rather than the one instance search reduces to. -/
instance additive_moduleGlobalSectionsOver_over :
    Functor.Additive
      (show SheafOfModules.{u} (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U) ⥤
          ModuleCat.{u} (sectionRing X U) from
        moduleGlobalSectionsOver (X.over U) (sectionRing X U) (overSectionsRingHom X U)) :=
  inferInstanceAs (moduleGlobalSectionsOver (X.over U) (sectionRing X U)
    (overSectionsRingHom X U)).Additive

/-- Additivity of `Γ(U, -)` with `𝒪(U)` as the base ring, in the spelling
`derivedSectionsOverObject` fixes. -/
instance additive_moduleSectionsOver_id :
    (moduleSectionsOver X U (RingHom.id (sectionRing X U))).Additive :=
  moduleSectionsOver_additive X U (RingHom.id (sectionRing X U))

/-- **[Stacks, Tag 0D6F] on the unbounded derived category, `𝒪(U)`-linearly.** Derived sections
over an object `U` of a ringed site are the derived global sections, on the localized ringed
site `(𝒞/U, 𝒪_U)`, of the restriction to that site — as functors `D(𝒪) ⥤ D(𝒪(U))`.

Restriction is exact and preserves K-injective complexes, so the composite of the two derived
functors is the derived functor of the composite
(`Stacks.Cohomology.LerayUnbounded.derivedCompIso`), and the composite is the sections over `U`
by `moduleSectionsOverIsoSlice`. -/
def derivedSectionsOverObjectIsoSliceModule :
    derivedSectionsOverObject X U ≅
      (SheafOfModules.overFunctor.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory ⋙
        derivedGlobalSectionsOverUnbounded (X.over U) (sectionRing X U)
          (overSectionsRingHom X U) :=
  (Stacks.Cohomology.LerayUnbounded.derivedCompIso
      (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U)
      (moduleGlobalSectionsOver (X.over U) (sectionRing X U) (overSectionsRingHom X U))
      (moduleSectionsOver X U (RingHom.id (sectionRing X U)))
      (moduleSectionsOverIsoSlice X U)
      (fun I hI => @Stacks.Cohomology.Localization.isKInjective_over _ _ X.J
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U I hI)).symm ≪≫
    Functor.isoWhiskerRight (Stacks.Cohomology.Localization.derivedRestrictionIsoMapDerivedCategory
      X U) _

end Slice

end AlgebraicGeometry.RingedSite

end
