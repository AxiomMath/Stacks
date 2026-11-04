module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorSquareTensorSequence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricStalkSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerPresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness

/-!
# The short exact sequence `0 ⟶ ⋀²(F) ⟶ T²(F) ⟶ Sym²(F) ⟶ 0` of sheaves of modules

Let `(X, O♯)` be a topological space with a sheaf of commutative rings and let `F` be a sheaf of
`O♯`-modules. The antisymmetriser `⋀²(F) ⟶ T²(F)` and the quotient `T²(F) ⟶ Sym²(F)` form a
complex of sheaves of modules which is exact at its middle term, and the sequence

`0 ⟶ ⋀²(F) ⟶ T²(F) ⟶ Sym²(F) ⟶ 0`

is short exact when every stalk of `F` is a free module over the corresponding stalk of `O♯`, for
instance when `F` is finite locally free. No hypothesis on `2` is made.

## Main definitions

* `SheafOfModules.extSymSheafShortComplex`: the complex `⋀²(F) ⟶ T²(F) ⟶ Sym²(F)` of sheaves of
  modules.
* `SheafOfModules.extSymSheafShortComplexIso`: its identification with the sheafification of the
  sectionwise complex.

## Main results

* `PresheafOfModules.tensorPowStalkL_stalkMapL_extTwoToTensorHom`: the stalk of the sectionwise
  antisymmetriser is the antisymmetriser of the stalk, under the comparisons of Stacks Tag 01CH.
* `PresheafOfModules.injective_stalkMapL_extTwoToTensorHom`: that stalk map is injective when the
  stalk of `F` is free.
* `SheafOfModules.sheafifyStalkLinearEquiv_naturality`: the stalk map of the sheafification of a
  morphism of presheaves of modules is the stalk map of that morphism.
* `SheafOfModules.mono_moduleSheafification_map_of_injective_stalkMapL`: sheafification turns a
  stalkwise injective morphism of presheaves of modules into a monomorphism.
* `SheafOfModules.mono_exteriorSquareToTensorPiece`: the antisymmetriser `⋀²(F) ⟶ T²(F)` is a
  monomorphism when every stalk of `F` is free.
* `SheafOfModules.extSymSheafShortComplex_exact`: the complex is exact at its middle term.
* `SheafOfModules.shortExact_extSymSheafShortComplex`: the sequence
  `0 ⟶ ⋀²(F) ⟶ T²(F) ⟶ Sym²(F) ⟶ 0` is short exact when every stalk of `F` is free.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 01CH](https://stacks.math.columbia.edu/tag/01CH)
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace

universe u

/-! ### The stalk of the sectionwise antisymmetriser -/

namespace PresheafOfModules

variable {X : TopCat.{u}} {R : X.Presheaf CommRingCat.{u}}
  (F : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})) (x : X)

/-- **The stalk of the sectionwise antisymmetriser is the antisymmetriser of the stalk.** Read
through the comparisons of Stacks Tag 01CH for the presheaf of sectionwise exterior squares and
the presheaf of sectionwise tensor squares, the stalk map of
`PresheafOfModules.extTwoToTensorHom` is `TensorAlgebra.extTwoToTensor` over the stalk ring. -/
theorem tensorPowStalkL_stalkMapL_extTwoToTensorHom
    (t : ↑(TopCat.Presheaf.stalk (extPow 2 F).presheaf x)) :
    tensorPowStalkL F x 2 (stalkMapL x (extTwoToTensorHom F) t) =
      TensorAlgebra.extTwoToTensor (extPowStalkL F x 2 t) := by
  obtain ⟨U, hU, y, rfl⟩ := TopCat.Presheaf.exists_germ_eq (extPow 2 F).presheaf t
  refine Eq.trans (congrArg (tensorPowStalkL F x 2)
    (stalkMapL_germ x (extTwoToTensorHom F) U hU y)) ?_
  refine Eq.trans (tensorPowStalkL_germ F x 2 U hU _) ?_
  refine Eq.trans ?_ (congrArg (TensorAlgebra.extTwoToTensor (R := ↑(R.stalk x)))
    (extPowStalkL_germ F x 2 U hU y)).symm
  exact (TensorAlgebra.extTwoToTensor_powMapₛₗ (R.germ U x hU).hom (germₛₗ F x U hU) y).symm

/-- **The stalk map of the sectionwise antisymmetriser is injective** when the stalk of `F` is a
free module over the stalk ring. -/
theorem injective_stalkMapL_extTwoToTensorHom
    (hfree : Module.Free ↑(R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x)) :
    Function.Injective (stalkMapL x (extTwoToTensorHom F)) := by
  have := hfree
  intro t t' h
  refine extPowStalkL_injective F x 2 (TensorAlgebra.injective_extTwoToTensor ?_)
  exact (tensorPowStalkL_stalkMapL_extTwoToTensorHom F x t).symm.trans
    ((congrArg (tensorPowStalkL F x 2) h).trans
      (tensorPowStalkL_stalkMapL_extTwoToTensorHom F x t'))

end PresheafOfModules

/-! ### Stalk maps of morphisms of sheaves of modules, read over the presheaf of rings -/

namespace SheafOfModules

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}

section StalkMapL

variable {N₁ N₂ N₃ : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

/-- The stalk map of a composite of morphisms of sheaves of modules is the composite of the
stalk maps, in the `CommRingCat`-linear spelling of `PresheafOfModules.stalkMapL`. -/
theorem stalkMapL_valHom_comp (f : N₁ ⟶ N₂) (g : N₂ ⟶ N₃) (x : ↥X)
    (t : ↑(TopCat.Presheaf.stalk N₁.val.presheaf x)) :
    PresheafOfModules.stalkMapL x (SymPresentation.valHom (f ≫ g)) t =
      PresheafOfModules.stalkMapL x (SymPresentation.valHom g)
        (PresheafOfModules.stalkMapL x (SymPresentation.valHom f) t) := by
  obtain ⟨U, hU, y, rfl⟩ := TopCat.Presheaf.exists_germ_eq N₁.val.presheaf t
  refine Eq.trans (PresheafOfModules.stalkMapL_germ x _ U hU y) ?_
  refine Eq.trans ?_ (congrArg (PresheafOfModules.stalkMapL x (SymPresentation.valHom g))
    (PresheafOfModules.stalkMapL_germ x (SymPresentation.valHom f) U hU y)).symm
  exact (PresheafOfModules.stalkMapL_germ x (SymPresentation.valHom g) U hU _).symm

end StalkMapL

/-! ### Sheafification does not change the stalk map -/

/-- **The stalk of the sheafification of a morphism of presheaves of modules is the stalk map of
that morphism**, read through the comparison `SheafOfModules.sheafifyStalkLinearEquiv` saying
that sheafification does not change stalks. -/
theorem sheafifyStalkLinearEquiv_naturality
    {P Q : PresheafOfModules.{u} (Osharp.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
    (φ : P ⟶ Q) (x : ↥X) (s : ↑(TopCat.Presheaf.stalk P.presheaf x)) :
    PresheafOfModules.stalkMapL x
        (SymPresentation.valHom ((PresheafOfModules.moduleSheafification
          (Opens.grothendieckTopology ↥X) (𝟙 Osharp.obj)).map φ))
        (sheafifyStalkLinearEquiv P x s) =
      sheafifyStalkLinearEquiv Q x (PresheafOfModules.stalkMapL x φ s) := by
  obtain ⟨U, hU, y, rfl⟩ := TopCat.Presheaf.exists_germ_eq P.presheaf s
  refine Eq.trans (congrArg (PresheafOfModules.stalkMapL x _)
    (sheafifyStalkLinearEquiv_germ P x U hU y)) ?_
  refine Eq.trans (PresheafOfModules.stalkMapL_germ x _ U hU _) ?_
  refine Eq.trans ?_ (congrArg (sheafifyStalkLinearEquiv Q x)
    (PresheafOfModules.stalkMapL_germ x φ U hU y)).symm
  refine Eq.trans ?_ (sheafifyStalkLinearEquiv_germ Q x U hU _).symm
  have hnat := (PresheafOfModules.sheafificationAdjunction
    (toRingCatMap (Opens.grothendieckTopology ↥X) (𝟙 Osharp.obj))).unit.naturality φ
  exact congrArg (TopCat.Presheaf.germ ((PresheafOfModules.moduleSheafification
      (Opens.grothendieckTopology ↥X) (𝟙 Osharp.obj)).obj Q).val.presheaf U x hU)
    (congrArg (fun h : P ⟶ PresheafOfModules.sheafifyRestrict
        (toRingCatMap (Opens.grothendieckTopology ↥X) (𝟙 Osharp.obj)) Q =>
      PresheafOfModules.Hom.app h (op U) y) hnat).symm

/-- **Sheafification turns a stalkwise injective morphism of presheaves of modules into a
monomorphism of sheaves of modules.** -/
theorem mono_moduleSheafification_map_of_injective_stalkMapL
    {P Q : PresheafOfModules.{u} (Osharp.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
    (φ : P ⟶ Q)
    (hφ : ∀ x : ↥X, Function.Injective (PresheafOfModules.stalkMapL x φ)) :
    Mono ((PresheafOfModules.moduleSheafification (Opens.grothendieckTopology ↥X)
      (𝟙 Osharp.obj)).map φ) := by
  rw [AlgebraicGeometry.SheafOfModules.mono_iff_injective_stalkMap]
  intro x a b hab
  obtain ⟨sa, rfl⟩ := (sheafifyStalkLinearEquiv P x).surjective a
  obtain ⟨sb, rfl⟩ := (sheafifyStalkLinearEquiv P x).surjective b
  refine congrArg (sheafifyStalkLinearEquiv P x) (hφ x ?_)
  refine (sheafifyStalkLinearEquiv Q x).injective ?_
  refine (sheafifyStalkLinearEquiv_naturality φ x sa).symm.trans ?_
  refine Eq.trans ?_ (sheafifyStalkLinearEquiv_naturality φ x sb)
  exact (SymPresentation.stalkMap_apply _ x _).symm.trans
    (hab.trans (SymPresentation.stalkMap_apply _ x _))

/-- **A stalkwise injective morphism of presheaves of modules sheafifies to a monomorphism even
after transport along isomorphisms of the source and the target.** -/
theorem mono_isoComp_moduleSheafification_map
    {P Q : PresheafOfModules.{u} (Osharp.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
    (φ : P ⟶ Q)
    (hφ : ∀ x : ↥X, Function.Injective (PresheafOfModules.stalkMapL x φ))
    {Np Nq : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
    (ep : Np ≅ (PresheafOfModules.moduleSheafification (Opens.grothendieckTopology ↥X)
      (𝟙 Osharp.obj)).obj P)
    (eq : Nq ≅ (PresheafOfModules.moduleSheafification (Opens.grothendieckTopology ↥X)
      (𝟙 Osharp.obj)).obj Q) :
    Mono (ep.hom ≫ (PresheafOfModules.moduleSheafification (Opens.grothendieckTopology ↥X)
      (𝟙 Osharp.obj)).map φ ≫ eq.inv) := by
  have := mono_moduleSheafification_map_of_injective_stalkMapL φ hφ
  infer_instance

/-! ### The short exact sequence -/

section ShortExact

variable {G : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

/-- **The antisymmetriser `⋀²(F) ⟶ T²(F)` of sheaves of modules is a monomorphism** as soon as
every stalk of `F` is a free module over the corresponding stalk of the sheaf of rings — as it is
when `F` is finite locally free. -/
theorem mono_exteriorSquareToTensorPiece
    (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) G)
    (hfree : ∀ x : ↥X, Module.Free ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk G.val.presheaf x)) :
    Mono (exteriorSquareToTensorPiece (Opens.grothendieckTopology ↥X) A) := by
  rw [exteriorSquareToTensorPiece]
  refine mono_isoComp_moduleSheafification_map _ (fun x => ?_) _ _
  exact PresheafOfModules.injective_stalkMapL_extTwoToTensorHom _ x (hfree x)

/-- **The three-term complex `⋀²(F) ⟶ T²(F) ⟶ Sym²(F)` of sheaves of modules.** -/
def extSymSheafShortComplex
    (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) G) :
    ShortComplex (SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)) :=
  ShortComplex.mk (exteriorSquareToTensorPiece (Opens.grothendieckTopology ↥X) A)
    (symmetricPowerQuotHom (Opens.grothendieckTopology ↥X) A 2)
    (exteriorSquareToTensorPiece_comp_symmetricPowerQuotHom (Opens.grothendieckTopology ↥X) A)

/-- The first square identifying the sheaf complex with the sheafification of the sectionwise
one: the antisymmetriser of sheaves of modules is by definition the sheafified sectionwise
antisymmetriser read through `exteriorPowerSheafifyIso` and `tensorPieceSheafifyIso`. -/
theorem exteriorPowerSheafifyIso_hom_comp_sheafifiedExtTwoToTensor
    (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) G) :
    (exteriorPowerSheafifyIso (Opens.grothendieckTopology ↥X) A 2).hom ≫
        (PresheafOfModules.moduleSheafification (Opens.grothendieckTopology ↥X)
          (𝟙 Osharp.obj)).map (PresheafOfModules.extTwoToTensorHom
            (valPresheaf (Opens.grothendieckTopology ↥X) G)) =
      exteriorSquareToTensorPiece (Opens.grothendieckTopology ↥X) A ≫
        (tensorPieceSheafifyIso (Opens.grothendieckTopology ↥X) A 2).hom := by
  rw [exteriorSquareToTensorPiece, Category.assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- The second square: the quotient map onto the symmetric square of sheaves of modules is by
definition the sheafified sectionwise quotient map read through `tensorPieceSheafifyIso` and
`symmetricPowerSheafifyIso`. -/
theorem tensorPieceSheafifyIso_hom_comp_sheafifiedSymQuot
    (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) G) :
    (tensorPieceSheafifyIso (Opens.grothendieckTopology ↥X) A 2).hom ≫
        (PresheafOfModules.moduleSheafification (Opens.grothendieckTopology ↥X)
          (𝟙 Osharp.obj)).map (PresheafOfModules.symQuotHom
            (valPresheaf (Opens.grothendieckTopology ↥X) G) 2) =
      symmetricPowerQuotHom (Opens.grothendieckTopology ↥X) A 2 ≫
        (symmetricPowerSheafifyIso (Opens.grothendieckTopology ↥X) A 2).hom := by
  rw [symmetricPowerQuotHom, Category.assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- Sheafification of presheaves of modules preserves zero morphisms. -/
instance preservesZeroMorphisms_moduleSheafification :
    (PresheafOfModules.moduleSheafification (Opens.grothendieckTopology ↥X)
      (𝟙 Osharp.obj)).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_isLeftAdjoint _

/-- **The complex `⋀²(F) ⟶ T²(F) ⟶ Sym²(F)` of sheaves of modules is the sheafification of the
sectionwise one**, by the three isomorphisms exhibiting the powers of `F` as the sheafifications
of the presheaves of sectionwise powers. -/
def extSymSheafShortComplexIso
    (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) G) :
    extSymSheafShortComplex A ≅
      (PresheafOfModules.extSymShortComplex
          (valPresheaf (Opens.grothendieckTopology ↥X) G)).map
        (PresheafOfModules.moduleSheafification (Opens.grothendieckTopology ↥X)
          (𝟙 Osharp.obj)) :=
  ShortComplex.isoMk (exteriorPowerSheafifyIso (Opens.grothendieckTopology ↥X) A 2)
    (tensorPieceSheafifyIso (Opens.grothendieckTopology ↥X) A 2)
    (symmetricPowerSheafifyIso (Opens.grothendieckTopology ↥X) A 2)
    (exteriorPowerSheafifyIso_hom_comp_sheafifiedExtTwoToTensor A)
    (tensorPieceSheafifyIso_hom_comp_sheafifiedSymQuot A)

/-- **The complex `⋀²(F) ⟶ T²(F) ⟶ Sym²(F)` of sheaves of modules is exact at the middle
term**, with no hypothesis on `F`. -/
theorem extSymSheafShortComplex_exact
    (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) G) :
    (extSymSheafShortComplex A).Exact := by
  have : PreservesFiniteLimits (PresheafOfModules.moduleSheafification
    (Opens.grothendieckTopology ↥X) (𝟙 Osharp.obj)) := inferInstance
  have : PreservesFiniteColimits (PresheafOfModules.moduleSheafification
    (Opens.grothendieckTopology ↥X) (𝟙 Osharp.obj)) := inferInstance
  exact (ShortComplex.exact_iff_of_iso (extSymSheafShortComplexIso A)).2
    ((PresheafOfModules.extSymShortComplex_exact
      (valPresheaf (Opens.grothendieckTopology ↥X) G)).map _)

/-- **The sequence `0 ⟶ ⋀²(F) ⟶ T²(F) ⟶ Sym²(F) ⟶ 0` of sheaves of modules is short exact**
whenever every stalk of `F` is free — in particular whenever `F` is finite locally free. -/
theorem shortExact_extSymSheafShortComplex
    (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) G)
    (hfree : ∀ x : ↥X, Module.Free ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk G.val.presheaf x)) :
    (extSymSheafShortComplex A).ShortExact :=
  ShortComplex.ShortExact.mk' (extSymSheafShortComplex_exact A)
    (mono_exteriorSquareToTensorPiece A hfree)
    (epi_symmetricPowerQuotHom (Opens.grothendieckTopology ↥X) A 2)

end ShortExact

end SheafOfModules

end
