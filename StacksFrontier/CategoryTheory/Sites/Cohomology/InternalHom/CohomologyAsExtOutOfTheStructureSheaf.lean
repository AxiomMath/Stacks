module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.FromTheStructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomDegreeNaturality

/-!
# Cohomology is derived Hom out of the structure sheaf

Let `(C, O)` be a ringed site and let `M` be an object of the unbounded derived category `D(O)`
of `O`-modules. Its cohomology is the Hom out of the structure sheaf in the derived category:

`H^n(C, M) = Hom_{D(O)}(O[0], M[n]) = Ext^n_{D(O)}(O[0], M)`,

where `H^n(C, M)` is the degree-`n` cohomology of the derived global sections `RΓ(C, M)` of
Stacks 0D6I, and `O[0]` is the structure sheaf in degree zero. The identification is additive and
natural in `M`.

## Main results

* `AlgebraicGeometry.RingedSite.derivedGlobalSectionsExtEquiv`: the identification
  `H^n(C, M) ≃+ Hom_{D(O)}(O[0], M[n])`.
* `AlgebraicGeometry.RingedSite.derivedGlobalSectionsExtEquiv_naturality`: it is natural in `M` —
  the map induced on `H^n(C, -)` by a morphism `ψ : M ⟶ M'` of `D(O)` is carried to
  postcomposition with `ψ[n]`, so that the identification is one of functors `D(O) ⥤ Ab` and not
  merely of groups. The naturality is stated on an element, which is the shape the library's
  `AlgebraicGeometry.RingedSite.globalDerivedHomDegreeEquiv_naturality` has and the shape the
  consumers use.

## Implementation notes

The identification is the composite of two earlier results, evaluated at the structure sheaf.

The first input is the all-degrees identification
`AlgebraicGeometry.RingedSite.globalDerivedHomDegreeEquiv` of Tag 0B6E,

`H^n(RΓ(C, RSheafHom(K, M))) = Hom_{D(O)}(K, M[n])`,

together with its naturality in both variables,
`AlgebraicGeometry.RingedSite.globalDerivedHomDegreeEquiv_naturality`. The second is
`AlgebraicGeometry.RingedSite.derivedStructureSheafHomNatIso` of Tag 08JD, the natural
isomorphism `RSheafHom(O[0], -) ≅ 𝟭` saying that the derived internal Hom out of the structure
sheaf is the identity functor on `D(O)`. Taking derived global sections of the second and feeding
it into the first at `K = O[0]` gives the statement, and the naturality is the naturality of the
two inputs — the second variable of the first input, and the natural isomorphism of the second.

*No hypothesis beyond the ambient ones is used.* `M` is an arbitrary object of the unbounded
derived category: no boundedness, no quasi-coherence, no hypothesis on the site beyond the
standing instances that the derived internal Hom of a ringed site already needs (sheafification
for abelian groups, local bijectivity of the weak equivalences, and the additivity and existence
of the degreewise tensor product that `AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor`
carries).

*The degree-zero case.* At `n = 0` this is
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv` of Tag 08JA read at
`K = O[0]`; for arbitrary `n` the degree is moved into the covariant variable by
`AlgebraicGeometry.RingedSite.globalDerivedHomDegreeEquiv`.

## References

* [Stacks Project, Tag 0B6E](https://stacks.math.columbia.edu/tag/0B6E)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
* [Stacks Project, Tag 0D6I](https://stacks.math.columbia.edu/tag/0D6I)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections
open Stacks.Cohomology.SiteModules

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})

variable [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- Derived global sections of the identification `RSheafHom(O[0], M) ≅ M`, on degree-`n`
cohomology: an additive isomorphism from `H^n(RΓ(C, M))` to `H^n(RΓ(C, RSheafHom(O[0], M)))`. -/
def derivedGlobalSectionsStructureSheafHomEquiv
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (n : ℤ) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        ((derivedModuleGlobalSections X).obj M) : Type u) ≃+
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        ((derivedModuleGlobalSections X).obj
          (((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).obj M)) : Type u) :=
  ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).mapIso
    ((derivedModuleGlobalSections X).mapIso
      (derivedStructureSheafHomIso X M).symm)).addCommGroupIsoToAddEquiv

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- `derivedGlobalSectionsStructureSheafHomEquiv` sends a class `ξ` to its image under the map
induced on degree-`n` cohomology by derived global sections of `M ≅ RSheafHom(O[0], M)`. -/
theorem derivedGlobalSectionsStructureSheafHomEquiv_apply
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (n : ℤ)
    (ξ : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
      ((derivedModuleGlobalSections X).obj M) : Type u)) :
    derivedGlobalSectionsStructureSheafHomEquiv X M n ξ =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
        ((derivedModuleGlobalSections X).map (derivedStructureSheafHomIso X M).inv) ξ :=
  rfl

/-- Two morphisms of `D(Ab)` applied in succession to a degree-`n` cohomology class act as their
composite. -/
private theorem homology_map_comp_apply {n : ℤ}
    {Z Z' Z'' : DerivedCategory AddCommGrpCat.{u}} (a : Z ⟶ Z') (b : Z' ⟶ Z'')
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj Z : Type u)) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map b
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map a x) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map (a ≫ b) x := by
  rw [CategoryTheory.Functor.map_comp]
  rfl

/-- **Cohomology is derived Hom out of the structure sheaf.** For an object `M` of the unbounded
derived category of `O`-modules on a ringed site `(C, O)` and every integer `n`, the degree-`n`
cohomology of the derived global sections `RΓ(C, M)` is the group of morphisms `O[0] ⟶ M[n]` in
`D(O)`, that is the `Ext`-group `Ext^n_{D(O)}(O[0], M)`:

`H^n(C, M) = Hom_{D(O)}(O[0], M[n])`.

The identification is additive, and it is natural in `M` by
`AlgebraicGeometry.RingedSite.derivedGlobalSectionsExtEquiv_naturality`. There is no hypothesis
on `M`: it is an arbitrary object of the unbounded derived category.

It is the composite of the all-degrees identification
`AlgebraicGeometry.RingedSite.globalDerivedHomDegreeEquiv` of Tag 0B6E at `K = O[0]` with the
identification `RSheafHom(O[0], M) ≅ M` of Tag 08JD
(`AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso`) under derived global sections. -/
def derivedGlobalSectionsExtEquiv
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (n : ℤ) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        ((derivedModuleGlobalSections X).obj M) : Type u) ≃+
      (derivedStructureSheaf X ⟶ M⟦n⟧) :=
  (derivedGlobalSectionsStructureSheafHomEquiv X M n).trans
    (globalDerivedHomDegreeEquiv X (derivedStructureSheaf X) M n)

/-- The identification of cohomology with derived Hom out of the structure sheaf, written out on
an element: derived global sections of the identification `M ≅ RSheafHom(O[0], M)`, followed by
the degree-`n` identification of the global derived hom at `K = O[0]`. -/
theorem derivedGlobalSectionsExtEquiv_apply
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (n : ℤ)
    (ξ : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
      ((derivedModuleGlobalSections X).obj M) : Type u)) :
    derivedGlobalSectionsExtEquiv X M n ξ =
      globalDerivedHomDegreeEquiv X (derivedStructureSheaf X) M n
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
          ((derivedModuleGlobalSections X).map (derivedStructureSheafHomIso X M).inv) ξ) :=
  rfl

/-- **The identification of cohomology with derived Hom out of the structure sheaf is natural in
`M`.** For a morphism `ψ : M ⟶ M'` of `D(O)` the map induced on degree-`n` cohomology of derived
global sections is carried by
`AlgebraicGeometry.RingedSite.derivedGlobalSectionsExtEquiv` to postcomposition with `ψ[n]`.

So `H^n(C, -) = Hom_{D(O)}(O[0], (-)[n])` is an identification of functors `D(O) ⥤ Ab` and not
merely of groups. -/
theorem derivedGlobalSectionsExtEquiv_naturality
    {M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (ψ : M ⟶ M') (n : ℤ)
    (ξ : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
      ((derivedModuleGlobalSections X).obj M) : Type u)) :
    derivedGlobalSectionsExtEquiv X M' n
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
          ((derivedModuleGlobalSections X).map ψ) ξ) =
      derivedGlobalSectionsExtEquiv X M n ξ ≫
        (CategoryTheory.shiftFunctor
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            n).map ψ := by
  -- The two sides differ by the naturality of `RSheafHom(O[0], -) ≅ 𝟭` and by the naturality of
  -- the degree-`n` identification of the global derived hom in its covariant variable.
  have hiso : ψ ≫ (derivedStructureSheafHomIso X M').inv =
      (derivedStructureSheafHomIso X M).inv ≫
        ((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).map ψ := by
    rw [Iso.comp_inv_eq, Category.assoc, derivedStructureSheafHomIso_naturality X ψ,
      Iso.inv_hom_id_assoc]
  have hRG : (derivedModuleGlobalSections X).map ψ ≫
        (derivedModuleGlobalSections X).map (derivedStructureSheafHomIso X M').inv =
      (derivedModuleGlobalSections X).map (derivedStructureSheafHomIso X M).inv ≫
        (derivedModuleGlobalSections X).map
          (((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).map ψ) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, hiso]
  have hmap : (((derivedSheafHomBifunctor X).map (𝟙 (derivedStructureSheaf X)).op).app M ≫
        ((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).map ψ) =
      ((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).map ψ := by
    simp
  have hnat := globalDerivedHomDegreeEquiv_naturality X (𝟙 (derivedStructureSheaf X)) ψ n
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
      ((derivedModuleGlobalSections X).map (derivedStructureSheafHomIso X M).inv) ξ)
  rw [hmap, Category.id_comp] at hnat
  rw [derivedGlobalSectionsExtEquiv_apply, derivedGlobalSectionsExtEquiv_apply,
    homology_map_comp_apply, hRG, ← homology_map_comp_apply]
  exact hnat

end AlgebraicGeometry.RingedSite

end
