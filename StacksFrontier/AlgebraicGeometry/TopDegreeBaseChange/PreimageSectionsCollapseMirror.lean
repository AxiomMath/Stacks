module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EdgeCompatPreimageRestrict
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EdgeCompatSectionsOverOpen

/-!
# The collapse mirror of [Stacks, Tag 01XK] at the pair `(Γ(f⁻¹V, -), res_{f^♯})`

The `ψ` side of conclusion (c) of [Stacks, Tag 0EX3] carries [Stacks, Tag 089W] inverted, in the
derived-sections reading
`Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward_inv_eq_lerayComparison`, at the
restricted morphism `AlgebraicGeometry.Scheme.Hom.resLE`. Printed from that statement, its fourth
factor is the crossing of the two models of the classical right derived functor
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` at the pair

> `(Γ(f⁻¹V, -) followed by restriction of scalars along f^♯,
>   Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSections f V)`,

and its fifth is restriction of scalars pulled out of the right derived functor. The `γ⁺` side
reads the same place at `RΓ(f⁻¹V, -)` with the scalars **outside**. This file supplies the one
identity that crosses that divide.

*Why the precomposition brick is not the one that does it.*
`…TopDegreeBaseChange.singleCompDerivedOpenSubscheme_hom_app_comp_compRightDerivedNatIso_hom` —
the bare-pair crossing of `OpenSubschemeSingleModelCrossing.lean` — is a **pre**composition
statement: it moves an *exact* functor `r` out of `Rⁿ(r ∘ w)` on the left. The degreewise functor
here is `Stacks.Cohomology.DerivedSectionsLeray.preimageSections f V`, which is
`Γ(f⁻¹V, -)` followed by restriction of scalars: the exact factor is on the **right** and the
derived factor on the left, so no instantiation of that brick reaches it — neither at
`r := Γ(f⁻¹V, -)`, which is the functor being derived and is not exact, nor at
`r := f_*`, which is not exact either. The applicable general statement is the collapse
**mirror**, `Stacks.EdgeCompat.singleCompDerived_hom_app_comp_rightDerivedCompNatIso_inv`
(`EdgeCompatCollapseMirror.lean`), which moves the **outer** functor out; this file is its
instantiation at the scalars pair, as `Stacks.EdgeCompat`
`.singleCompDerivedSections_hom_app_comp_rightDerivedCompNatIso_inv`
(`EdgeCompatSectionsOverOpen.lean`) is its instantiation at `(f_*, Γ(V, -))`.

Every datum the mirror asks for is already in `EdgeCompatPreimageRestrict.lean`: the comparison of
the two right derived functors is `Stacks.EdgeCompat.preimageSectionsModelComparison`, and the
coherence `hθ` is its characterising factorisation
`Stacks.EdgeCompat.preimageSectionsModelComparison_fac_app` composed with
`preimageSectionsCompUnit_app`, which reads
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.exactPostcomposeUnit` off its
construction. Nothing is assumed of `f`, of `V`, of the degree or of the object beyond the
pointwise homology-preservation hypothesis Grothendieck's comparison itself carries — and that
one is automatic here, restriction of scalars being exact.

## Main results

* `Stacks.EdgeCompat.exists_quasiIso_isKInjective_preimageSectionsRing`: K-injective resolutions
  of cochain complexes of `Γ(f⁻¹V, 𝒪_X)`-modules, which is what the edge morphism of the
  restriction of scalars needs. This is `CochainComplex.exists_quasiIso_isKInjective` with its two
  conjuncts in the order the edge morphism's API takes them.
* `Stacks.EdgeCompat.isRightDerivedFunctor_preimageRestrictScalars_mapDerivedCategory`:
  restriction of scalars along `f^♯` being exact, the functor it induces on derived categories is
  its own right derived functor, with `CategoryTheory.Functor.mapDerivedCategoryFactorsh` inverted
  as unit.
* `Stacks.EdgeCompat.singleCompDerivedPreimageSections_hom_app_comp_rightDerivedCompNatIso_inv`:
  **the identity.** The crossing of the two models of `Rⁿ(res_{f^♯} ∘ Γ(f⁻¹V, -))` at `E Z`,
  followed by Grothendieck's comparison inverted, is the degree-`n` cohomology of
  `preimageSectionsModelComparison` at `(E Z)[0]`, then the edge morphism of restriction of
  scalars at `RΓ(f⁻¹V, (E Z)[0])`, then restriction of scalars applied to the crossing of the two
  models of `RΓ(f⁻¹V, -)` at `E Z`.
* `Stacks.EdgeCompat.singleCompDerivedPreimageSectionsComp_hom_app_comp_rightDerivedCompNatIso`
  `_inv`: the same at the spelling `f_* ⋙ Γ(V, -)` of the degreewise functor, which is the one the
  `ψ` side's fourth factor is written at. `RingedSpaceModuleAdjunction.modulePushforward` is not
  reducible, so a statement at one spelling does not match the other; nothing is proved, the
  inhabitant being the one above.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison (derivedHomologyComparison)

universe u

namespace Stacks.EdgeCompat

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] RingedSpaceModuleAdjunction.preservesLimits_modulePushforward
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (V : Opens Y.carrier)

/-- **K-injective resolutions of complexes of `Γ(f⁻¹V, 𝒪_X)`-modules.** The edge morphism of
restriction of scalars along `f^♯` is indexed by resolutions in its source category, and
`CochainComplex.exists_quasiIso_isKInjective` supplies them; only the order of the two conjuncts
differs from the one `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison`
`.derivedHomologyComparison` takes. -/
theorem exists_quasiIso_isKInjective_preimageSectionsRing
    (K : CochainComplex (ModuleCat.{u}
      ((structureSheafRing X).obj.obj (op ((opensMap f).obj V)))) ℤ) :
    ∃ (I : CochainComplex (ModuleCat.{u}
      ((structureSheafRing X).obj.obj (op ((opensMap f).obj V)))) ℤ) (g : K ⟶ I),
      I.IsKInjective ∧ QuasiIso g := by
  obtain ⟨I, g, hg, hI⟩ := CochainComplex.exists_quasiIso_isKInjective K
  exact ⟨I, g, hI, hg⟩

/-- **Restriction of scalars along `f^♯` is its own right derived functor.** It is exact, so
`CategoryTheory.Functor.mapDerivedCategoryFactorsh` is an isomorphism and the functor it induces
on derived categories inverts quasi-isomorphisms, which is all
`CategoryTheory.Functor.isRightDerivedFunctor_of_inverts` asks. -/
theorem isRightDerivedFunctor_preimageRestrictScalars_mapDerivedCategory :
    (preimageRestrictScalars f V).mapDerivedCategory.IsRightDerivedFunctor
      (preimageRestrictScalars f V).mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso
        (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ((opensMap f).obj V))))
        (ComplexShape.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts _ _
    (preimageRestrictScalars f V).mapDerivedCategoryFactorsh

/-- **`Stacks.EdgeCompat.preimageSectionsCompUnit` read off its construction.** It is
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.exactPostcomposeUnit`, whose component is
the comparison of the two spellings of the degreewise composite inverted, then
`CategoryTheory.Functor.mapDerivedCategoryFactorsh` for the restriction of scalars inverted, then
that functor applied to the unit of `RΓ(f⁻¹V, -)` — which is exactly the shape the collapse
mirror's coherence hypothesis asks for. The only step beyond `rfl` is the reassociation. -/
private theorem preimageSectionsCompUnit_app
    (L : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (preimageSectionsCompUnit f V).app L =
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
            (Iso.refl (sectionsOverOpen X ((opensMap f).obj V) ⋙ preimageRestrictScalars f V))
            (ComplexShape.up ℤ)).inv.app L) ≫
        (preimageRestrictScalars f V).mapDerivedCategoryFactorsh.inv.app
            (((sectionsOverOpen X ((opensMap f).obj V)).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj L) ≫
          (preimageRestrictScalars f V).mapDerivedCategory.map
            ((derivedSectionsOverOpenUnit X ((opensMap f).obj V)).app L) := by
  rw [← Category.assoc]
  rfl

/-! ### The collapse mirror at the pair `(Γ(f⁻¹V, -), res_{f^♯})` -/

section Mirror

variable {Dc : Type*} [Category* Dc]
  (E : Dc ⥤ SheafOfModules.{u} (structureSheafRing X)) (n : ℕ)

/-- **[Stacks, Tag 01XK]'s collapse factor for the pair `(Γ(f⁻¹V, -), res_{f^♯})`, at the
unbounded model.** For a morphism `f : X ⟶ Y` of ringed spaces, an open `V ⊆ Y`, a functor
`E : Dc ⥤ Mod(𝒪_X)` and a degree `n`, the crossing of the two models of the iterated derived
functor of `res_{f^♯} ∘ Γ(f⁻¹V, -)` at `E Z`, followed by Grothendieck's comparison
`Stacks.Cohomology.AffineBase.rightDerivedCompNatIso` inverted, is

> the degree-`n` cohomology of `Stacks.EdgeCompat.preimageSectionsModelComparison` at `(E Z)[0]`,
> then the edge morphism of restriction of scalars along `f^♯` at `RΓ(f⁻¹V, (E Z)[0])`, then
> restriction of scalars applied to the crossing of the two models of `RΓ(f⁻¹V, -)` at `E Z`.

This is `Stacks.EdgeCompat.singleCompDerived_hom_app_comp_rightDerivedCompNatIso_inv` at that
pair. The two right derived functors of the composite are
`Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSections` and `RΓ(f⁻¹V, -)` followed by
restriction of scalars, whose comparison is `preimageSectionsModelComparison` and whose coherence
is `preimageSectionsModelComparison_fac_app`.

Nothing is assumed of `f`, of `V` or of the object beyond `hpl`, the pointwise
homology-preservation hypothesis Grothendieck's comparison itself carries; restriction of scalars
being exact, `hpl` is `fun _ => inferInstance` at every instantiation. -/
theorem singleCompDerivedPreimageSections_hom_app_comp_rightDerivedCompNatIso_inv
    (hpl : ∀ Z : Dc, (preimageRestrictScalars f V).PreservesLeftHomologyOf
      ((((sectionsOverOpen X ((opensMap f).obj V)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (injectiveResolution (E.obj Z)).cocomplex).sc n))
    (Z : Dc)
    [(preimageRestrictScalars f V).PreservesLeftHomologyOf
      ((((sectionsOverOpen X ((opensMap f).obj V)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (injectiveResolution (E.obj Z)).cocomplex).sc n)] :
    (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
            (sectionsOverOpen X ((opensMap f).obj V) ⋙ preimageRestrictScalars f V)
            (derivedPreimageSections f V) (derivedPreimageSectionsUnit f V)
            (exists_quasiIso_isKInjective X) n).hom.app (E.obj Z) ≫
        (Stacks.Cohomology.AffineBase.rightDerivedCompNatIso E
          (sectionsOverOpen X ((opensMap f).obj V)) (preimageRestrictScalars f V) n
            hpl).inv.app Z =
      (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) (n : ℤ)).map
          ((preimageSectionsModelComparison f V).app
            ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj
              (E.obj Z))) ≫
        (derivedHomologyComparison (preimageRestrictScalars f V)
              (preimageRestrictScalars f V).mapDerivedCategory
              (preimageRestrictScalars f V).mapDerivedCategoryFactorsh.inv
              (exists_quasiIso_isKInjective_preimageSectionsRing f V) (n : ℤ)).app
            ((derivedSectionsOverOpen X ((opensMap f).obj V)).obj
              ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj
                (E.obj Z))) ≫
          (preimageRestrictScalars f V).map
            ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
              (sectionsOverOpen X ((opensMap f).obj V))
              (derivedSectionsOverOpen X ((opensMap f).obj V))
              (derivedSectionsOverOpenUnit X ((opensMap f).obj V))
              (exists_quasiIso_isKInjective X) n).hom.app (E.obj Z)) :=
  have := isRightDerivedFunctor_preimageRestrictScalars_mapDerivedCategory f V
  singleCompDerived_hom_app_comp_rightDerivedCompNatIso_inv E
    (sectionsOverOpen X ((opensMap f).obj V)) (preimageRestrictScalars f V) n
    (derivedSectionsOverOpen X ((opensMap f).obj V))
    (derivedSectionsOverOpenUnit X ((opensMap f).obj V))
    (preimageRestrictScalars f V).mapDerivedCategory
    (preimageRestrictScalars f V).mapDerivedCategoryFactorsh.inv
    (derivedPreimageSections f V) (derivedPreimageSectionsUnit f V)
    (preimageSectionsModelComparison f V) (exists_quasiIso_isKInjective X)
    (exists_quasiIso_isKInjective_preimageSectionsRing f V)
    (fun L => (preimageSectionsModelComparison_fac_app f V L).trans
      (preimageSectionsCompUnit_app f V L)) hpl Z

/-- **`singleCompDerivedPreimageSections_hom_app_comp_rightDerivedCompNatIso_inv` at the spelling
`f_* ⋙ Γ(V, -)` of the degreewise functor**, which is the one the `ψ` side's fourth factor is
written at and the one `Stacks.EdgeCompat.derivedPreimageSectionsUnitComp` lives at. The two
spellings are definitionally equal but `RingedSpaceModuleAdjunction.modulePushforward` is not
reducible, so a statement at one does not match the other; this mirrors
`Stacks.EdgeCompat.derivedHomologyComparison_preimageSectionsCompUnitComp_eq`. Nothing is proved:
the inhabitant is the one above. -/
theorem singleCompDerivedPreimageSectionsComp_hom_app_comp_rightDerivedCompNatIso_inv
    (hpl : ∀ Z : Dc, (preimageRestrictScalars f V).PreservesLeftHomologyOf
      ((((sectionsOverOpen X ((opensMap f).obj V)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (injectiveResolution (E.obj Z)).cocomplex).sc n))
    (Z : Dc)
    [(preimageRestrictScalars f V).PreservesLeftHomologyOf
      ((((sectionsOverOpen X ((opensMap f).obj V)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (injectiveResolution (E.obj Z)).cocomplex).sc n)] :
    (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
            (modulePushforward f ⋙ sectionsOverOpen Y V) (derivedPreimageSections f V)
            (derivedPreimageSectionsUnitComp f V)
            (exists_quasiIso_isKInjective X) n).hom.app (E.obj Z) ≫
        (Stacks.Cohomology.AffineBase.rightDerivedCompNatIso E
          (sectionsOverOpen X ((opensMap f).obj V)) (preimageRestrictScalars f V) n
            hpl).inv.app Z =
      (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) (n : ℤ)).map
          ((preimageSectionsModelComparison f V).app
            ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj
              (E.obj Z))) ≫
        (derivedHomologyComparison (preimageRestrictScalars f V)
              (preimageRestrictScalars f V).mapDerivedCategory
              (preimageRestrictScalars f V).mapDerivedCategoryFactorsh.inv
              (exists_quasiIso_isKInjective_preimageSectionsRing f V) (n : ℤ)).app
            ((derivedSectionsOverOpen X ((opensMap f).obj V)).obj
              ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj
                (E.obj Z))) ≫
          (preimageRestrictScalars f V).map
            ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
              (sectionsOverOpen X ((opensMap f).obj V))
              (derivedSectionsOverOpen X ((opensMap f).obj V))
              (derivedSectionsOverOpenUnit X ((opensMap f).obj V))
              (exists_quasiIso_isKInjective X) n).hom.app (E.obj Z)) :=
  singleCompDerivedPreimageSections_hom_app_comp_rightDerivedCompNatIso_inv f V E n hpl Z

end Mirror

end Stacks.EdgeCompat

end
