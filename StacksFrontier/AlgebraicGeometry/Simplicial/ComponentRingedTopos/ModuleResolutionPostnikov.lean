module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleResolution
public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerResolutionPostnikov
import StacksCore.Tactic.StacksAttribute

/-!
# The Postnikov system and the derived colimit of the module resolution

Let `S` be a simplicial-site situation and `O` a sheaf of rings on its total site. The lower
shriek images `g_{n!} O_n` of the component structure sheaves form an alternating-face
resolution `… → g_{2!} O_2 → g_{1!} O_1 → g_{0!} O_0` of `O` in the category `Mod(O)` of
sheaves of `O`-modules; that resolution is Stacks 0D9B,
`CategoryTheory.SimplicialSiteSituation.nonempty_simplicialModuleResolution`.

Read as a cochain complex `L` supported in degrees `≤ 0`, with `g_{n!} O_n` in degree `-n`, that
resolution is a complex to which the brutal-truncation machinery of
`StacksDraft.BrutalPostnikov` applies: putting `Xₙ = g_{n!} O_n` and
`Yₙ = (g_{n!} O_n → … → g_{0!} O_0)[-n]`, the brutal-truncation triangles
`Yₙ₊₁ ⟶ Xₙ₊₁ ⟶ Yₙ ⟶ Yₙ₊₁[1]` form a Postnikov system for `… ⟶ X₂ ⟶ X₁ ⟶ X₀`, and `L` is the
derived colimit of the tower `Yₙ[n]`. Since the augmentation of the resolution is a
quasi-isomorphism, the object of `D(O)` represented by `L` is `O` itself, so the second
statement reads `O = hocolim Yₙ[n]`.

Both statements persist under any exact functor `T` of `D(O)` — for the Postnikov system
without further hypotheses, for the derived colimit when `T` also commutes with countable
direct sums. The functor the source uses is `T = - ⊗^L_O K` for an object `K` of `D(O)`, for
which `T(O) = K`, `T(Xₙ) = (g_{n!} O_n) ⊗^L_O K` and
`T(Yₙ) = (g_{n!} O_n → … → g_{0!} O_0)[-n] ⊗^L_O K`.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.moduleResolutionComplex`: the resolution of Stacks
  0D9B as a cochain complex of `O`-modules supported in degrees `≤ 0`.
* `CategoryTheory.SimplicialSiteSituation.moduleResolutionTerm` and `.moduleResolutionTot`: the
  objects `Xₙ` and `Yₙ` of `D(O)`.
* `CategoryTheory.SimplicialSiteSituation.moduleResolutionSystem`: the tower `n ↦ Yₙ[n]`.
* `CategoryTheory.SimplicialSiteSituation.moduleResolutionPostnikovSystem` and
  `.map_moduleResolutionPostnikovSystem`: the Postnikov system of the brutal-truncation
  triangles, and its image under an exact functor.

## Main results

* `CategoryTheory.SimplicialSiteSituation.moduleResolutionDerivedIso`: the complex represents
  the structure sheaf, `L = O` in `D(O)`.
* `CategoryTheory.SimplicialSiteSituation.isHomotopyColimit_moduleResolutionSystem` and
  `.isHomotopyColimit_map_moduleResolutionSystem`: `O = hocolim Yₙ[n]`, and its image under an
  exact functor commuting with countable direct sums.

## Implementation notes

The resolution is carried as an explicit argument `D : SimplicialModuleResolutionActual S O`
rather than chosen from Stacks 0D9B, so that the objects `Xₙ` are *literally* the lower shriek
images `g_{n!} O_n` — that is what the field `lowerShriekDegreeEq` of
`SimplicialModuleResolutionActual` records, and it is what
`moduleResolutionComplexXIso` reads off. One such `D` exists by
`nonempty_simplicialModuleResolution`.

As in `StacksFrontier/CategoryTheory/Sites/Simplicial/IntegerResolutionPostnikov.lean`, which
proves the same two statements for the integral resolution, the conclusions are stated for an
arbitrary exact functor of `D(O)` in place of `- ⊗^L_O K`: the source's proof uses nothing
about that functor beyond exactness and, for the derived colimit, commutation with countable
direct sums. Instantiating the functor at the derived tensor product is not done here, because
the derived tensor product of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/Interface.lean` is built on a ringed
site with a *commutative* structure sheaf, whereas the resolution of Stacks 0D9B is available
for a sheaf of possibly noncommutative rings; the two are therefore not stated over the same
category of modules.

Postnikov systems are finite, so the system attached to the infinite complex
`… ⟶ X₂ ⟶ X₁ ⟶ X₀` is recorded as one system for every truncation length `N`, all of them cut
out of the same family of triangles.

## References

* [Stacks Project, Tag 0D9Q](https://stacks.math.columbia.edu/tag/0D9Q)
* [Stacks Project, Tag 0D9B](https://stacks.math.columbia.edu/tag/0D9B)
* [Stacks Project, Tag 0D7Z](https://stacks.math.columbia.edu/tag/0D7Z)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open StacksDraft.BrutalPostnikov
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

section Colimits

variable {S : SimplicialSiteSituation.{u}} (O : Sheaf S.totalTopology RingCat.{u})

/-- Colimits over `ℕ` are exact in the category of sheaves of `O`-modules on the total site:
that category is Grothendieck abelian for the universe of the site, so filtered colimits of
that size are exact, and a category with exact filtered colimits of one size has them for
every smaller size. -/
instance hasExactColimitsOfShape_nat_sheafOfModules :
    HasExactColimitsOfShape ℕ (SheafOfModules.{u} O) :=
  (AB5OfSize_of_univLE.{0, 0, u, u} (SheafOfModules.{u} O)).ofShape ℕ

end Colimits

section Complex

variable {S : SimplicialSiteSituation.{u}} {O : Sheaf S.totalTopology RingCat.{u}}
  (D : SimplicialModuleResolutionActual S O)

/-- The resolution `… → g₂!O₂ → g₁!O₁ → g₀!O₀` of Stacks 0D9B, read as a cochain complex of
sheaves of `O`-modules on the total site supported in degrees `≤ 0`, with `g_{n!}Oₙ` in degree
`-n`. -/
def moduleResolutionComplex : CochainComplex (SheafOfModules.{u} O) ℤ :=
  D.complex.extend (ComplexShape.embeddingUpIntLE 0)

/-- In degree `-n` the cochain complex of the module resolution is `g_{n!}Oₙ`. -/
def moduleResolutionComplexXIso (n : ℕ) :
    (moduleResolutionComplex D).X (-(n : ℤ)) ≅
      (componentModuleLowerShriek S O ⦋n⦌).obj
        (SheafOfModules.unit (componentRingSheaf S O ⦋n⦌)) :=
  HomologicalComplex.extendXIso _ (ComplexShape.embeddingUpIntLE 0) (i := n) (by simp) ≪≫
    eqToIso (D.lowerShriekDegreeEq n)

/-- The cochain complex of the module resolution is concentrated in degrees `≤ 0`: it is
extended by zero from the embedding of those degrees. -/
instance isStrictlyLE_moduleResolutionComplex :
    CochainComplex.IsStrictlyLE (moduleResolutionComplex D) 0 := by
  dsimp only [moduleResolutionComplex]
  infer_instance

/-- The augmentation of the resolution of Stacks 0D9B, read as a map of chain complexes into
the structure sheaf placed in degree zero. -/
def moduleResolutionChainAugmentation :
    D.complex ⟶ (ChainComplex.single₀ (SheafOfModules.{u} O)).obj (SheafOfModules.unit O) :=
  (ChainComplex.toSingle₀Equiv D.complex (SheafOfModules.unit O)).symm
    ⟨D.augmentation, D.augmentation_comp⟩

/-- The augmentation is a quasi-isomorphism: that is exactly what it means for
`… → g₂!O₂ → g₁!O₁ → g₀!O₀ → O → 0` to be exact. -/
instance quasiIso_moduleResolutionChainAugmentation :
    QuasiIso (moduleResolutionChainAugmentation D) := by
  refine ⟨fun n => ?_⟩
  match n with
  | 0 =>
      rw [ChainComplex.quasiIsoAt₀_iff,
        ShortComplex.quasiIso_iff_of_zeros'
          ((HomologicalComplex.shortComplexFunctor' (SheafOfModules.{u} O)
            (ComplexShape.down ℕ) 1 0 0).map (moduleResolutionChainAugmentation D))
          (D.complex.shape 0 0 (by simp))
          (HomologicalComplex.single_obj_d (ComplexShape.down ℕ) 0
            (SheafOfModules.unit O) 1 0)
          (HomologicalComplex.single_obj_d (ComplexShape.down ℕ) 0
            (SheafOfModules.unit O) 0 0)]
      exact ⟨D.exact_zero, D.augmentation_epi⟩
  | (n + 1) =>
      rw [quasiIsoAt_iff_exactAt' (moduleResolutionChainAugmentation D) (n + 1)
        (ChainComplex.exactAt_succ_single_obj (SheafOfModules.unit O) n)]
      exact D.exact_positive (n + 1) (by omega)

/-- The augmentation of the module resolution, extended to cochain complexes in degrees
`≤ 0`. -/
def moduleResolutionExtendedAugmentation :
    moduleResolutionComplex D ⟶
      ((ChainComplex.single₀ (SheafOfModules.{u} O)).obj
        (SheafOfModules.unit O)).extend (ComplexShape.embeddingUpIntLE 0) :=
  HomologicalComplex.extendMap (moduleResolutionChainAugmentation D)
    (ComplexShape.embeddingUpIntLE 0)

/-- The augmentation extended to cochain complexes, `moduleResolutionExtendedAugmentation`, is a
quasi-isomorphism. -/
instance quasiIso_moduleResolutionExtendedAugmentation :
    QuasiIso (moduleResolutionExtendedAugmentation D) := by
  dsimp only [moduleResolutionExtendedAugmentation, moduleResolutionComplex]
  rw [HomologicalComplex.quasiIso_extendMap_iff]
  infer_instance

/-- The augmentation of the module resolution, read on the cochain complex of
`moduleResolutionComplex`. -/
def moduleResolutionAugmentation :
    moduleResolutionComplex D ⟶
      (HomologicalComplex.single (SheafOfModules.{u} O) (ComplexShape.up ℤ) 0).obj
        (SheafOfModules.unit O) :=
  moduleResolutionExtendedAugmentation D ≫
    (HomologicalComplex.extendSingleIso (C := SheafOfModules.{u} O)
      (ComplexShape.embeddingUpIntLE 0) (SheafOfModules.unit O) 0 0 (by simp)).hom

/-- The augmentation `moduleResolutionAugmentation` of the module resolution onto the structure
sheaf in degree zero is a quasi-isomorphism. -/
instance quasiIso_moduleResolutionAugmentation :
    QuasiIso (moduleResolutionAugmentation D) := by
  dsimp only [moduleResolutionAugmentation]
  infer_instance

end Complex

section Derived

universe z

variable {S : SimplicialSiteSituation.{u}} {O : Sheaf S.totalTopology RingCat.{u}}
  [HasDerivedCategory.{z} (SheafOfModules.{u} O)]
  (D : SimplicialModuleResolutionActual S O)

/-- Countable direct sums exist in the derived category of sheaves of `O`-modules on the total
site: that category has direct sums indexed by the universe of the site, and `ℕ` is equivalent
to a type of that universe. -/
instance hasCoproduct_nat_derivedSheafOfModules
    (F : ℕ → DerivedCategory (SheafOfModules.{u} O)) : HasCoproduct F := by
  have h₁ : HasColimitsOfShape (Discrete (ULift.{u} ℕ))
      (DerivedCategory (SheafOfModules.{u} O)) :=
    Stacks.Injectives.hasCoproducts_derivedCategory _ (ULift.{u} ℕ)
  have : HasColimitsOfShape (Discrete ℕ) (DerivedCategory (SheafOfModules.{u} O)) :=
    hasColimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift)
  infer_instance

/-- **The module resolution represents the structure sheaf.** The object of `D(O)` given by the
complex `… → g₂!O₂ → g₁!O₁ → g₀!O₀` is `O` itself. -/
def moduleResolutionDerivedIso :
    (DerivedCategory.Q (C := SheafOfModules.{u} O)).obj (moduleResolutionComplex D) ≅
      (DerivedCategory.singleFunctor (SheafOfModules.{u} O) 0).obj (SheafOfModules.unit O) :=
  asIso ((DerivedCategory.Q (C := SheafOfModules.{u} O)).map
    (moduleResolutionAugmentation D))

/-- The object `Xₙ = g_{n!}Oₙ` of `D(O)`, concentrated in degree zero. -/
abbrev moduleResolutionTerm (n : ℕ) : DerivedCategory (SheafOfModules.{u} O) :=
  term (A := SheafOfModules.{u} O) (moduleResolutionComplex D) n

/-- The object `Yₙ = (g_{n!}Oₙ → … → g_{0!}O₀)[-n]` of `D(O)`. -/
abbrev moduleResolutionTot (n : ℕ) : DerivedCategory (SheafOfModules.{u} O) :=
  tot (A := SheafOfModules.{u} O) (moduleResolutionComplex D) n

/-- The differential `Xₙ₊₁ ⟶ Xₙ` of the complex `… ⟶ X₂ ⟶ X₁ ⟶ X₀` in `D(O)`. -/
abbrev moduleResolutionTermDiff (n : ℕ) :
    moduleResolutionTerm D (n + 1) ⟶ moduleResolutionTerm D n :=
  termDiff (A := SheafOfModules.{u} O) (moduleResolutionComplex D) n

/-- The canonical map `Yₙ ⟶ Xₙ`, the projection onto the bottom term `g_{n!}Oₙ`. -/
abbrev moduleResolutionTotProj (n : ℕ) :
    moduleResolutionTot D n ⟶ moduleResolutionTerm D n :=
  totProj (A := SheafOfModules.{u} O) (moduleResolutionComplex D) n

/-- The identification of `Xₙ` with `g_{n!}Oₙ` placed in degree zero. -/
def moduleResolutionTermIso (n : ℕ) :
    moduleResolutionTerm D n ≅
      (DerivedCategory.singleFunctor (SheafOfModules.{u} O) 0).obj
        ((componentModuleLowerShriek S O ⦋n⦌).obj
          (SheafOfModules.unit (componentRingSheaf S O ⦋n⦌))) :=
  (DerivedCategory.singleFunctor (SheafOfModules.{u} O) 0).mapIso
    (moduleResolutionComplexXIso D n)

/-- The system `n ↦ Yₙ[n] = (g_{n!}Oₙ → … → g_{0!}O₀)` of brutal truncations of the module
resolution, as a system of objects of `D(O)`. -/
abbrev moduleResolutionSystem : ℕ ⥤ DerivedCategory (SheafOfModules.{u} O) :=
  truncTower (A := SheafOfModules.{u} O) (moduleResolutionComplex D) ⋙ DerivedCategory.Q

/-- The triangle `Yₙ₊₁ ⟶ Xₙ₊₁ ⟶ Yₙ ⟶ Yₙ₊₁[1]` attached to the module resolution is
distinguished, with `Yₙ₊₁ ⟶ Xₙ₊₁` the canonical projection onto the bottom term `g_{n+1!}Oₙ₊₁`;
applying an exact functor `T` of `D(O)` — such as `- ⊗^L_O K` for an object `K` — gives the
corresponding triangle on `T(Xₙ)` and `T(Yₙ)`. -/
theorem distinguished_map_truncTriangle_moduleResolution
    (T : DerivedCategory (SheafOfModules.{u} O) ⥤ DerivedCategory (SheafOfModules.{u} O))
    [T.CommShift ℤ] [T.IsTriangulated] (n : ℕ) :
    T.mapTriangle.obj
        (truncTriangleAt (A := SheafOfModules.{u} O) (moduleResolutionComplex D)
          (-((n : ℤ) + 1))) ∈
      distTriang (DerivedCategory (SheafOfModules.{u} O)) :=
  T.map_distinguished _ (truncTriangleAt_distinguished _ _)

/-- **Stacks 0D9Q(2) for the structure sheaf.** The structure sheaf of the total site is the
derived colimit of the system `Yₙ[n]` of brutal truncations of its module resolution. -/
theorem isHomotopyColimit_moduleResolutionSystem :
    IsHomotopyColimit (moduleResolutionSystem D)
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} O) 0).obj (SheafOfModules.unit O)) :=
  isHomotopyColimit_of_iso
    (isHomotopyColimit_truncTower (A := SheafOfModules.{u} O) (moduleResolutionComplex D))
    (moduleResolutionDerivedIso D)

/-- **Stacks 0D9Q(1) for the structure sheaf.** For each length `N`, the brutal-truncation
triangles `Yₙ₊₁ ⟶ Xₙ₊₁ ⟶ Yₙ ⟶ Yₙ₊₁[1]` of the module resolution are a Postnikov system
(Derived Categories, Definition 0D7Z) for `X_N ⟶ ⋯ ⟶ X₁ ⟶ X₀`, where `Xₙ = g_{n!}Oₙ`. -/
def moduleResolutionPostnikovSystem (N : ℕ) :
    Triangulated.PostnikovSystem
      (fun i : Fin (N + 1) => moduleResolutionTerm D (i : ℕ))
      (fun i : Fin N => moduleResolutionTermDiff D (i : ℕ)) :=
  postnikovSystem (A := SheafOfModules.{u} O) (moduleResolutionComplex D) N

/-- **Stacks 0D9Q(1).** For an exact functor `T` of `D(O)` — such as `- ⊗^L_O K` for an object
`K` of `D(O)` — the images under `T` of the brutal-truncation triangles of the module
resolution are a Postnikov system for `T(X_N) ⟶ ⋯ ⟶ T(X₁) ⟶ T(X₀)`, where `Xₙ = g_{n!}Oₙ`. -/
@[stacks 0D9Q "part (1), the Postnikov system, for an exact functor in place of - ⊗^L_O K"]
def map_moduleResolutionPostnikovSystem
    (T : DerivedCategory (SheafOfModules.{u} O) ⥤ DerivedCategory (SheafOfModules.{u} O))
    [T.CommShift ℤ] [T.IsTriangulated] (N : ℕ) :
    Triangulated.PostnikovSystem
      (fun i : Fin (N + 1) => T.obj (moduleResolutionTerm D (i : ℕ)))
      (fun i : Fin N => T.map (moduleResolutionTermDiff D (i : ℕ))) :=
  (moduleResolutionPostnikovSystem D N).map T

/-- **Stacks 0D9Q(2).** For an exact functor `T` of `D(O)` commuting with countable direct
sums — such as `- ⊗^L_O K` for an object `K` of `D(O)`, for which `T(O) = K` — the object
`T(O)` is the derived colimit of the system `T(Yₙ[n])`. -/
@[stacks 0D9Q "part (2), the homotopy colimit, for an exact functor in place of - ⊗^L_O K"]
theorem isHomotopyColimit_map_moduleResolutionSystem
    (T : DerivedCategory (SheafOfModules.{u} O) ⥤ DerivedCategory (SheafOfModules.{u} O))
    [T.CommShift ℤ] [T.IsTriangulated]
    [PreservesColimit (Discrete.functor (moduleResolutionSystem D).obj) T] :
    IsHomotopyColimit (moduleResolutionSystem D ⋙ T)
      (T.obj ((DerivedCategory.singleFunctor (SheafOfModules.{u} O) 0).obj
        (SheafOfModules.unit O))) :=
  (isHomotopyColimit_moduleResolutionSystem D).map T

end Derived


end CategoryTheory.SimplicialSiteSituation

end
