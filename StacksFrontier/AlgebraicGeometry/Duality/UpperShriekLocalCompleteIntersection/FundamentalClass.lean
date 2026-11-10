module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekLocalCompleteIntersection.ConstantRank
public import StacksFrontier.AlgebraicGeometry.Duality.FundamentalClassDeterminantSource
public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.SchemeMiddleExact
public import StacksFrontier.AlgebraicGeometry.ConormalComparison.IdealSheafComparison
public import StacksFrontier.AlgebraicGeometry.Conormal.QuotientFactorization
public import StacksFrontier.AlgebraicGeometry.Thickenings.UnramifiedPairSplitConormalSequence
public import StacksFrontier.AlgebraicGeometry.DeRham.ExteriorPowerPullback
public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.SmoothAtCriterion

/-!
# The map `∧^{d-c} Ω_{X/Y} ⟶ ∧^c 𝒩 ⊗ ∧^d Ω_{P/Y}|_X` of [Stacks, Tag 0E9Z]

Let `i : X ⟶ U` be a closed immersion into an open `U` of a scheme `P` smooth of relative
dimension `d` over `Y`, whose conormal sheaf is finite locally free of rank `c`. Applying
[Stacks, Tag 0E9Y] to the conormal sequence `𝒞_{X/P} ⟶ Ω_{P/Y}|_X ⟶ Ω_{X/Y} ⟶ 0`
([Stacks, Tag 01UZ]) gives a map `∧^{d-c} Ω_{X/Y} ⟶ ∧^c 𝒩 ⊗ ∧^d Ω_{P/Y}|_X`, `𝒩` the normal
sheaf of `i`, which is an isomorphism on the stalk at `x` exactly when `c ≤ d` and the stalk of
`Ω_{X/Y}` at `x` is free of rank `d - c`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe u

attribute [local implicit_reducible] structureSheafRing AlgebraicGeometry.SheafedSpace.sheaf
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.Duality

section Source

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {E₁ E₀ F : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (A₁ : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) E₁)
  (A₀ : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) E₀)
  (AF : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) F)
  (A₁d : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X)
    (dualMod E₁))
  (α : E₁ ⟶ E₀) (π : E₀ ⟶ F) (hαπ : α ≫ π = 0)
  (hS : (ShortComplex.mk α π hαπ).Exact) (r₁ : ℕ)

/-- **[Stacks, Tag 0E9Y], read on the stalk**: the canonical map is bijective on the stalk at
`x` if and only if `r₁ ≤ r₀` and the stalk `F_x` is free of rank `r₀ - r₁`. -/
theorem bijective_stalkMapL_sheafDeterminantMap_iff_basis [Epi π]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₁ r₁] (r₀ : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₀ r₀]
    (x : ↥X) [IsLocalRing ↑(TopCat.Presheaf.stalk Osharp.obj x)] :
    Function.Bijective (PresheafOfModules.stalkMapL x
        (sheafDeterminantMap A₁ A₀ AF A₁d α π hαπ hS r₁ r₀).val) ↔
      r₁ ≤ r₀ ∧ Nonempty (Module.Basis (Fin (r₀ - r₁)) ↑(TopCat.Presheaf.stalk Osharp.obj x)
        ↑(TopCat.Presheaf.stalk F.val.presheaf x)) := by
  by_cases h : r₁ ≤ r₀
  · have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₀
        (r₁ + (r₀ - r₁)) := by rwa [Nat.add_sub_cancel' h]
    rw [and_iff_right h]
    unfold sheafDeterminantMap
    rw [dite_eq_left h, bijective_stalkMapL_iso_comp_iff, bijective_stalkMapL_comp_iso_iff,
      bijective_stalkMapL_detSourceMap_iff]
    exact bijective_stalkMapL_detSheafPairing_iff A₁ A₀ AF α π hαπ hS r₁ (r₀ - r₁) x
  · exact iff_of_false (fun hb => h ((bijective_stalkMapL_sheafDeterminantMap_iff A₁ A₀ AF A₁d
      α π hαπ hS r₁ r₀ x).1 hb).1) (fun h' => h h'.1)

end Source

section LocallyRingedSpace

variable (Y : AlgebraicGeometry.LocallyRingedSpace.{u})
  {E₁ E₀ F : _root_.SheafOfModules.{u}
    (toRingCat (Opens.grothendieckTopology ↥Y.toRingedSpace.carrier) Y.toRingedSpace.sheaf)}
  (α : E₁ ⟶ E₀) (π : E₀ ⟶ F) (hαπ : α ≫ π = 0)
  (hS : (ShortComplex.mk α π hαπ).Exact) (r₁ r₀ : ℕ)

/-- **[Stacks, Tag 0E9Y], read on the stalk.** The canonical map
`⋀^{r₀ - r₁} F ⟶ ⋀^{r₁}(E₁^∨) ⊗ ⋀^{r₀} E₀` is an isomorphism on the stalk at `x` if and only if
`r₁ ≤ r₀` and the stalk `F_x` is free of rank `r₀ - r₁`. -/
theorem isIso_stalkMap_locallyRingedSpaceDeterminantMap_iff_basis [Epi π]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₁ r₁]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₀ r₀]
    (x : ↥Y.toRingedSpace.carrier) :
    IsIso (AlgebraicGeometry.SheafOfModules.stalkMap
        (toRingCat (Opens.grothendieckTopology ↥Y.toRingedSpace.carrier) Y.toRingedSpace.sheaf) x
        (locallyRingedSpaceDeterminantMap Y α π hαπ hS r₁ r₀)) ↔
      r₁ ≤ r₀ ∧ Nonempty (Module.Basis (Fin (r₀ - r₁))
        ↑(TopCat.Presheaf.stalk Y.toRingedSpace.sheaf.obj x)
        ↑(TopCat.Presheaf.stalk F.val.presheaf x)) := by
  have : IsLocalRing ↑(TopCat.Presheaf.stalk Y.toRingedSpace.sheaf.obj x) := Y.isLocalRing x
  rw [ConcreteCategory.isIso_iff_bijective]
  exact bijective_stalkMapL_sheafDeterminantMap_iff_basis
    (_root_.SheafOfModules.ringedSpaceAlgebras Y.toRingedSpace E₁)
    (_root_.SheafOfModules.ringedSpaceAlgebras Y.toRingedSpace E₀)
    (_root_.SheafOfModules.ringedSpaceAlgebras Y.toRingedSpace F)
    (_root_.SheafOfModules.ringedSpaceAlgebras Y.toRingedSpace (dualMod E₁)) α π hαπ hS r₁ r₀ x

end LocallyRingedSpace

namespace ClosedOpenProperFactorization

open Stacks.AlgebraicGeometry.RegularIdealSheaf

variable {X P Y : Scheme.{u}} (U : P.Opens) (i : X ⟶ U.toScheme) (g : P ⟶ Y)
  [IsClosedImmersion i] (d c : ℕ) [SmoothOfRelativeDimension d g]

/-- The conormal sheaf of `i`, as an object of `X.Modules`. -/
abbrev conormalModules : X.Modules := Stacks.Conormal.conormalSheaf i

/-- **`𝒞_i ≅ 𝒞_{X/P}`**: the conormal sheaf of the closed immersion `i : X ⟶ U` is the conormal
sheaf of the immersion `i ≫ U.ι : X ⟶ P` that the conormal sequence of [Stacks, Tag 01UZ] is
built on. -/
def conormalSheafCompOpenIso :
    conormalModules U i ≅ Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSheaf (i ≫ U.ι) :=
  (Stacks.Immersion.conormalSheafSelfIso i).symm ≪≫
    (Stacks.Conormal.conormalSheafIsoPullbackIdealSheaf (i ≫ U.ι) U i rfl).symm ≪≫
    (Stacks.ConormalSequenceUnramifiedPair.conormalSheafComparisonIso (i ≫ U.ι)).symm

/-- The first arrow of the conormal sequence of `i ≫ U.ι` over `g`, read on `𝒞_i`. -/
abbrev conormalArrow :
    conormalModules U i ⟶ (Scheme.Modules.pullback (i ≫ U.ι)).obj
      (Scheme.Hom.relativeDifferentials g) :=
  (conormalSheafCompOpenIso U i).hom ≫ Stacks.ConormalSequenceRight.conormalDifferential (i ≫ U.ι) g

/-- The second arrow of the conormal sequence of `i ≫ U.ι` over `g`. -/
abbrev differentialsArrow :
    (Scheme.Modules.pullback (i ≫ U.ι)).obj (Scheme.Hom.relativeDifferentials g) ⟶
      Scheme.Hom.relativeDifferentials ((i ≫ U.ι) ≫ g) :=
  (Stacks.ConormalSequenceRight.conormalShortComplex (i ≫ U.ι) g).g

/-- The composite `𝒞_i ⟶ (i ≫ U.ι)^* Ω_{P/Y} ⟶ Ω_{X/Y}` of `conormalArrow` and `differentialsArrow`
is zero. -/
theorem conormalArrow_comp_differentialsArrow :
    conormalArrow U i g ≫ differentialsArrow U i g = 0 :=
  (Category.assoc _ _ _).trans (((conormalSheafCompOpenIso U i).hom ≫=
    (Stacks.ConormalSequenceRight.conormalShortComplex (i ≫ U.ι) g).zero).trans comp_zero)

/-- The short complex `𝒞_i ⟶ (i ≫ U.ι)^* Ω_{P/Y} ⟶ Ω_{X/Y}` is exact. -/
theorem exact_conormalArrow :
    (ShortComplex.mk _ _ (conormalArrow_comp_differentialsArrow U i g)).Exact := by
  refine ShortComplex.exact_of_iso ?_
    (Stacks.ConormalSequenceRight.conormalShortComplex_exact (i ≫ U.ι) g)
  refine ShortComplex.isoMk (conormalSheafCompOpenIso U i).symm (Iso.refl _) (Iso.refl _) ?_ ?_
  · change (conormalSheafCompOpenIso U i).inv ≫ conormalArrow U i g =
      Stacks.ConormalSequenceRight.conormalDifferential (i ≫ U.ι) g ≫ 𝟙 _
    exact (Iso.inv_hom_id_assoc (conormalSheafCompOpenIso U i) _).trans (Category.comp_id _).symm
  · change differentialsArrow U i g ≫ 𝟙 _ = 𝟙 _ ≫ differentialsArrow U i g
    exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- The map `differentialsArrow : (i ≫ U.ι)^* Ω_{P/Y} ⟶ Ω_{X/Y}` is an epimorphism. -/
theorem epi_differentialsArrow :
    Epi (C := _root_.SheafOfModules (toRingCat
      (Opens.grothendieckTopology ↥X.toLocallyRingedSpace.toRingedSpace.carrier)
      X.toLocallyRingedSpace.toRingedSpace.sheaf)) (differentialsArrow U i g) :=
  Stacks.ConormalSequenceRight.epi_conormalShortComplex_g (i ≫ U.ι) g

omit [IsClosedImmersion i] in
/-- The pullback `(i ≫ U.ι)^* Ω_{P/Y}` of the relative differentials is finite locally free of rank
`d`. -/
theorem isFiniteLocallyFreeOfRank_pullback_relativeDifferentials :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := toRingCat (Opens.grothendieckTopology ↥X.toLocallyRingedSpace.toRingedSpace.carrier)
        X.toLocallyRingedSpace.toRingedSpace.sheaf)
      ((Scheme.Modules.pullback (i ≫ U.ι)).obj (Scheme.Hom.relativeDifferentials g)) d := by
  have := Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials g d
  exact AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (i ≫ U.ι) _ d

/-- The exterior powers of the ringed space of `X` are those of `X`. -/
theorem exteriorPower_ringedSpaceAlgebras (F : X.Modules) (n : ℕ) :
    (_root_.SheafOfModules.ringedSpaceAlgebras X.toLocallyRingedSpace.toRingedSpace F).exteriorPower
      n = Scheme.Modules.exteriorPower F n :=
  rfl

/-- The tensor product of sheaves of modules on the ringed space of `X` is the one of `X`. -/
theorem tensorSheafBifunctor_obj_eq (A B : X.Modules) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toLocallyRingedSpace.toRingedSpace.presheaf,
          X.toLocallyRingedSpace.toRingedSpace.IsSheaf⟩).obj A).obj B =
      Scheme.Modules.tensorObjRingedSpace X A B :=
  rfl

/-- The dual of the conormal sheaf of `i` is the normal sheaf of `i`. -/
theorem dualMod_conormalModules :
    dualMod (conormalModules U i) = Stacks.Divisors.normalSheaf i :=
  rfl

variable [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
    (R := toRingCat (Opens.grothendieckTopology ↥X.toLocallyRingedSpace.toRingedSpace.carrier)
      X.toLocallyRingedSpace.toRingedSpace.sheaf) (conormalModules U i) c]

/-- The canonical map of [Stacks, Tag 0E9Y] for the conormal sequence of `i ≫ U.ι` over `g`. -/
def determinantMap :
    Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials ((i ≫ U.ι) ≫ g))
        ((d : ℤ) - c) ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toLocallyRingedSpace.toRingedSpace.presheaf,
            X.toLocallyRingedSpace.toRingedSpace.IsSheaf⟩).obj
        ((_root_.SheafOfModules.ringedSpaceAlgebras X.toLocallyRingedSpace.toRingedSpace
            (dualMod (conormalModules U i))).exteriorPower c)).obj
          ((_root_.SheafOfModules.ringedSpaceAlgebras X.toLocallyRingedSpace.toRingedSpace
            ((Scheme.Modules.pullback (i ≫ U.ι)).obj
              (Scheme.Hom.relativeDifferentials g))).exteriorPower d) :=
  haveI := isFiniteLocallyFreeOfRank_pullback_relativeDifferentials U i g d
  haveI := epi_differentialsArrow U i g
  locallyRingedSpaceDeterminantMap X.toLocallyRingedSpace (conormalArrow U i g)
    (differentialsArrow U i g) (conormalArrow_comp_differentialsArrow U i g)
    (exact_conormalArrow U i g) c d

/-- `∧^c 𝒩 ⊗ ∧^d((i ≫ U.ι)^* Ω_{P/Y}) ≅ ∧^c 𝒩 ⊗ (i ≫ U.ι)^* ∧^d Ω_{P/Y}`. -/
def tensorExteriorPowerPullbackIso :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toLocallyRingedSpace.toRingedSpace.presheaf,
          X.toLocallyRingedSpace.toRingedSpace.IsSheaf⟩).obj
      ((_root_.SheafOfModules.ringedSpaceAlgebras X.toLocallyRingedSpace.toRingedSpace
          (dualMod (conormalModules U i))).exteriorPower c)).obj
        ((_root_.SheafOfModules.ringedSpaceAlgebras X.toLocallyRingedSpace.toRingedSpace
          ((Scheme.Modules.pullback (i ≫ U.ι)).obj
            (Scheme.Hom.relativeDifferentials g))).exteriorPower d) ≅
      Scheme.Modules.tensorObjRingedSpace X
        (Scheme.Modules.exteriorPower (Stacks.Divisors.normalSheaf i) c)
        (pulledBackDeterminant U i g d) :=
  Functor.mapIso _
    (Scheme.Modules.exteriorPowerPullbackIso (i ≫ U.ι) (Scheme.Hom.relativeDifferentials g)
      d).symm ≪≫ eqToIso (tensorSheafBifunctor_obj_eq _ _)

/-- **The map `∧^{d-c} Ω_{X/Y} ⟶ ∧^c 𝒩 ⊗ (i ≫ U.ι)^* ∧^d Ω_{P/Y}`** of [Stacks, Tag 0E9Z]: the
canonical map of [Stacks, Tag 0E9Y] for the conormal sequence, followed by
`∧^d((i ≫ U.ι)^* Ω_{P/Y}) ≅ (i ≫ U.ι)^* ∧^d Ω_{P/Y}`. -/
def fundamentalClassMap :
    Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials ((i ≫ U.ι) ≫ g))
        ((d : ℤ) - c) ⟶
      Scheme.Modules.tensorObjRingedSpace X
        (Scheme.Modules.exteriorPower (Stacks.Divisors.normalSheaf i) c)
        (pulledBackDeterminant U i g d) :=
  determinantMap U i g d c ≫ (tensorExteriorPowerPullbackIso U i g d c).hom

/-- **The isomorphism locus of the map of [Stacks, Tag 0E9Z]**: its stalk at `x` is an
isomorphism exactly when `c ≤ d` and the stalk of `Ω_{X/Y}` at `x` is free of rank `d - c`. -/
theorem isIso_stalkMap_fundamentalClassMap_iff (x : X) :
    IsIso (AlgebraicGeometry.SheafOfModules.stalkMap
        (toRingCat (Opens.grothendieckTopology
          ↥X.toLocallyRingedSpace.toRingedSpace.carrier)
          X.toLocallyRingedSpace.toRingedSpace.sheaf) x
        (fundamentalClassMap U i g d c)) ↔
      c ≤ d ∧ Nonempty (Module.Basis (Fin (d - c))
        ↑(TopCat.Presheaf.stalk X.toLocallyRingedSpace.toRingedSpace.sheaf.obj x)
        ↑(TopCat.Presheaf.stalk
          (Scheme.Hom.relativeDifferentials ((i ≫ U.ι) ≫ g)).val.presheaf x)) := by
  have := isFiniteLocallyFreeOfRank_pullback_relativeDifferentials U i g d
  let R := toRingCat (Opens.grothendieckTopology ↥X.toLocallyRingedSpace.toRingedSpace.carrier)
    X.toLocallyRingedSpace.toRingedSpace.sheaf
  let e := tensorExteriorPowerPullbackIso U i g d c
  have hcomp : AlgebraicGeometry.SheafOfModules.stalkMap R x (fundamentalClassMap U i g d c) =
      AlgebraicGeometry.SheafOfModules.stalkMap R x (determinantMap U i g d c) ≫
        AlgebraicGeometry.SheafOfModules.stalkMap R x e.hom :=
    (AlgebraicGeometry.SheafOfModules.stalkFunctor R x).map_comp _ _
  have : IsIso (AlgebraicGeometry.SheafOfModules.stalkMap R x e.hom) :=
    (AlgebraicGeometry.SheafOfModules.stalkFunctor R x).map_isIso e.hom
  rw [hcomp, isIso_comp_right_iff]
  have := epi_differentialsArrow U i g
  exact isIso_stalkMap_locallyRingedSpaceDeterminantMap_iff_basis X.toLocallyRingedSpace
    (conormalArrow U i g) (differentialsArrow U i g) (conormalArrow_comp_differentialsArrow U i g)
    (exact_conormalArrow U i g) c d x

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
    (R := toRingCat (Opens.grothendieckTopology ↥X.toLocallyRingedSpace.toRingedSpace.carrier)
      X.toLocallyRingedSpace.toRingedSpace.sheaf) (conormalModules U i) c] in
/-- The rank of the conormal sheaf of `i ≫ U.ι` is the rank of the conormal sheaf of `i`. -/
theorem isFiniteLocallyFreeOfRank_conormalSheaf_comp
    [h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := toRingCat (Opens.grothendieckTopology ↥X.toLocallyRingedSpace.toRingedSpace.carrier)
        X.toLocallyRingedSpace.toRingedSpace.sheaf) (conormalModules U i) c] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := toRingCat (Opens.grothendieckTopology ↥X.toLocallyRingedSpace.toRingedSpace.carrier)
        X.toLocallyRingedSpace.toRingedSpace.sheaf)
      (Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSheaf (i ≫ U.ι) : X.Modules) c :=
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (conormalSheafCompOpenIso U i) h

/-- **The stalk of the map of [Stacks, Tag 0E9Z] at `x` is an isomorphism exactly when the
composite `X ⟶ P ⟶ Y` is smooth at `x`.** -/
theorem isIso_stalkMap_fundamentalClassMap_iff_smoothAt [IsLocallyNoetherian Y]
    (x : X) :
    IsIso (AlgebraicGeometry.SheafOfModules.stalkMap
        (toRingCat (Opens.grothendieckTopology
          ↥X.toLocallyRingedSpace.toRingedSpace.carrier)
          X.toLocallyRingedSpace.toRingedSpace.sheaf) x
        (fundamentalClassMap U i g d c)) ↔
      InfinitesimalLifting.SmoothAt ((i ≫ U.ι) ≫ g) x := by
  have := isFiniteLocallyFreeOfRank_pullback_relativeDifferentials U i g d
  have := isFiniteLocallyFreeOfRank_conormalSheaf_comp U i c
  have : Smooth g := SmoothOfRelativeDimension.smooth d g
  rw [isIso_stalkMap_fundamentalClassMap_iff,
    Stacks.ConormalSequenceRight.smoothAt_iff_nonempty_basis (i ≫ U.ι) g c d x]

end ClosedOpenProperFactorization

end Stacks.Duality
