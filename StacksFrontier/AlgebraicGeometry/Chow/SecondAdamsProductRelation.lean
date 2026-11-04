module

public import StacksFrontier.AlgebraicGeometry.Chow.SecondAdamsSymmetricFiltration
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricSquareTensorSequence

/-!
# The product relation for `Sym²` and the second Adams operator

Let `X` be a scheme and `ℰ`, `ℱ` finite locally free `𝒪_X`-modules. The short exact sequence

`0 → ⋀²ℰ ⊗ ⋀²ℱ → Sym²(ℰ ⊗ ℱ) → Sym²ℰ ⊗ Sym²ℱ → 0`

gives in `K₀(Vect(X))` the product relation
`[Sym²(ℰ ⊗ ℱ)] = [⋀²ℰ ⊗ ⋀²ℱ] + [Sym²ℰ ⊗ Sym²ℱ]`. Consequently
`AlgebraicGeometry.VectorBundleKZero.SquarePowersData X` holds for every scheme `X`, and
`K₀(Vect(X))` carries the second Adams operation `ψ²` of [Stacks, Tag 0FEJ].

## Main results

* `AlgebraicGeometry.VectorBundleKZero.classOf_sym_tensor_of_isFiniteLocallyFree`: the product
  relation.
* `AlgebraicGeometry.VectorBundleKZero.squarePowersData`: `SquarePowersData X` holds for every
  scheme `X`.
* `AlgebraicGeometry.VectorBundleKZero.exists_secondAdamsOperator_of_scheme`: the ring map `ψ²`
  with `ψ²[ℰ] = [Sym²ℰ] - [⋀²ℰ]`, `ψ²[ℒ] = [ℒ^{⊗2}]`, commuting with every ring map realising
  pullback.

## References

* [Stacks Project, Tag 0FEJ](https://stacks.math.columbia.edu/tag/0FEJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.FiniteLocallyFree TopologicalSpace

universe u

namespace AlgebraicGeometry.VectorBundleKZero

variable {X : Scheme.{u}}

/-- **The product relation for `Sym²`.** For finite locally free `ℰ`, `ℱ` on a scheme,
`[Sym²(ℰ ⊗ ℱ)] = [⋀²ℰ ⊗ ⋀²ℱ] + [Sym²ℰ ⊗ Sym²ℱ]` in `K₀(Vect(X))`. -/
theorem classOf_sym_tensor_of_isFiniteLocallyFree (E F : X.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hF : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F) :
    classOf X (secondSymmetricPower X (Scheme.Modules.tensorObjRingedSpace X E F)) =
      classOf X (Scheme.Modules.tensorObjRingedSpace X
          (secondExteriorPower X E) (secondExteriorPower X F)) +
        classOf X (Scheme.Modules.tensorObjRingedSpace X
          (secondSymmetricPower X E) (secondSymmetricPower X F)) := by
  let J := Opens.grothendieckTopology (X : TopCat)
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := Sheaf.toRingCat J X.sheaf) E := isFiniteLocallyFree_toSheaf hE
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := Sheaf.toRingCat J X.sheaf) F := isFiniteLocallyFree_toSheaf hF
  let W := Scheme.Modules.tensorObjRingedSpace X E F
  let AE := SheafOfModules.algebras J E
  let AF := SheafOfModules.algebras J F
  let AW := SheafOfModules.algebras J W
  have hS := SheafOfModules.SymSquareTensor.shortExact_cauchy AE.symmetricGenerator
    AE.symmetric_isSymmetricAlgebra AF.symmetricGenerator AF.symmetric_isSymmetricAlgebra
    AW.symmetricGenerator AW.symmetric_isSymmetricAlgebra AE.exteriorGenerator
    AE.exterior_isExteriorAlgebra AF.exteriorGenerator AF.exterior_isExteriorAlgebra
    (fun x => Stacks.SheafOfModules.TopWedge.free_stalk E x)
    (fun x => Stacks.SheafOfModules.TopWedge.free_stalk F x)
  have tensor : ∀ A B : X.Modules, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) A →
      IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) B →
      IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
        (Scheme.Modules.tensorObjRingedSpace X A B) :=
    fun A B hA hB => @isFiniteLocallyFree_tensorObj X A B hA hB
  exact @classOf_shortExact X _ _ _ _ _ hS.mono_f hS.epi_g _
    (tensor _ _ (isFiniteLocallyFree_secondExteriorPower E hE)
      (isFiniteLocallyFree_secondExteriorPower F hF))
    (isFiniteLocallyFree_secondSymmetricPower W (tensor E F hE hF))
    (tensor _ _ (isFiniteLocallyFree_secondSymmetricPower E hE)
      (isFiniteLocallyFree_secondSymmetricPower F hF)) hS.exact

/-- `SquarePowersData X` holds for every scheme `X`: finite local freeness of the two squares,
the two filtration relations and the two product relations. -/
theorem squarePowersData (X : Scheme.{u}) : SquarePowersData X :=
  SquarePowersData.of_classOf_sym_tensor fun E F hE hF =>
    classOf_sym_tensor_of_isFiniteLocallyFree E F hE hF

/-- For a scheme `X` there is a ring map `ψ² : K₀(Vect(X)) → K₀(Vect(X))` which sends `[ℒ]` to
`[ℒ^{⊗2}]` when `ℒ` is invertible and is compatible with pullbacks; on the class of a finite
locally free module `ℰ` it is `ψ²([ℰ]) = [Sym² ℰ] - [⋀² ℰ]`. The compatibility with pullbacks
along `f : Y ⟶ X` is the commutation with any ring map of Grothendieck rings sending `[ℰ]` to
`[f^*ℰ]` on finite locally free modules. -/
theorem exists_secondAdamsOperator_of_scheme (X : Scheme.{u}) :
    ∃ ψ : VectorBundleKZero X →+* VectorBundleKZero X,
      (∀ E : X.Modules, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
          ψ (classOf X E) =
            classOf X (secondSymmetricPower X E) - classOf X (secondExteriorPower X E)) ∧
        (∀ L : X.Modules,
          ∀ _ : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L,
            ψ (classOf X L) = classOf X (Scheme.Modules.tensorObjRingedSpace X L L)) ∧
        (∀ (Y : Scheme.{u}) (f : Y ⟶ X) (p : VectorBundleKZero X →+* VectorBundleKZero Y),
          (∀ E : X.Modules, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
              p (classOf X E) = classOf Y ((Scheme.Modules.pullback f).obj E)) →
            (∀ E : X.Modules, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
              IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf)
                ((Scheme.Modules.pullback f).obj E)) →
              ∀ a : VectorBundleKZero X,
                secondAdamsAddHom (squarePowersData Y) (p a) = p (ψ a)) := by
  obtain ⟨ψ, h₁, h₂, h₃⟩ := exists_secondAdamsOperator X (squarePowersData X)
  exact ⟨ψ, h₁, h₂, fun Y f p hp hflf a => h₃ Y f (squarePowersData Y) p hp hflf a⟩

end AlgebraicGeometry.VectorBundleKZero

end
