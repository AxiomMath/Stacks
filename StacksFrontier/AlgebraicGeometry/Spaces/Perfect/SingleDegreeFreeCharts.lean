module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartPointLifts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartSheaves
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SingleDegreeRankOpenSubspace
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalTypesOfModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreeOfIntRank
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UnitEndomorphisms

/-!
# The points at which a derived module is free of a given rank in a given degree

Let `X` be an algebraic space and `E` an object of `D(𝒪_X)`. An object `K` of the derived
category of an algebraic space is *free of rank `r` in degree `i`* when it is isomorphic to the
free module `𝒪^{⊕r}` placed in degree `i`. This property is stable under derived pullback along
every morphism. The set of points of `X` lying in the image of an étale chart on which `E` is
free of rank `r` in degree `i` is open.

## Main definitions

* `AlgebraicGeometry.Space.IsFreeOfRankInDegree`: `K ≅ 𝒪^{⊕r}[-i]`.
* `AlgebraicGeometry.Space.singleDegreeFreePoints`: the points of `X` in the image of an étale
  chart on which `E` is free of rank `r` in degree `i`.

## Main results

* `AlgebraicGeometry.Space.IsFreeOfRankInDegree.derivedPullback`: stability under `Lf^*`.
* `AlgebraicGeometry.Space.isOpen_singleDegreeFreePoints`: openness.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An object of `D(𝒪_Z)` is *free of rank `r` in degree `i`* when it is isomorphic to the free
module `𝒪^{⊕r}` placed in degree `i`. -/
def IsFreeOfRankInDegree {Z : AlgebraicSpaces B S hS}
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)))
    (i r : ℤ) : Prop :=
  ∃ n : ℕ, (n : ℤ) = r ∧ Nonempty (K ≅ (DerivedCategory.singleFunctor _ i).obj
    (SheafOfModules.free (R := ringedToposStructureRingSheaf B S hS Z) (ULift.{u} (Fin n))))

/-- Being free of rank `r` in degree `i` is stable under derived pullback. -/
theorem IsFreeOfRankInDegree.derivedPullback {Y Z : AlgebraicSpaces B S hS}
    {K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))} {i r : ℤ}
    (hK : IsFreeOfRankInDegree K i r) (f : Y ⟶ Z) :
    IsFreeOfRankInDegree ((smallEtaleDerivedModulePullback B S hS f).obj K) i r := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hK
  have hflat := isFlat_of_isRetractOfFiniteFree B S hS
    (SheafOfModules.free (R := ringedToposStructureRingSheaf B S hS Z) (ULift.{u} (Fin n)))
    ⟨n, (Stacks.SheafOfModules.freeULiftFinIsoBiproduct (smallEtaleRingedTopos B S hS Z).O n).hom,
      (Stacks.SheafOfModules.freeULiftFinIsoBiproduct (smallEtaleRingedTopos B S hS Z).O n).inv,
      Iso.hom_inv_id _⟩
  obtain ⟨e'⟩ := nonempty_smallEtaleDerivedModulePullback_obj_singleFunctor_iso f _ i hflat
  exact ⟨n, hn, ⟨(smallEtaleDerivedModulePullback B S hS f).mapIso e ≪≫ e' ≪≫
    (DerivedCategory.singleFunctor _ i).mapIso
      (RingedToposHom.pullbackModulesFreeIso (X := smallEtaleRingedTopos B S hS Y)
        (Y := smallEtaleRingedTopos B S hS Z) (smallEtaleRingedToposHom B S hS f) _).symm⟩⟩

/-- Being free of rank `r` in degree `i` is invariant under isomorphism. -/
theorem IsFreeOfRankInDegree.of_iso {Z : AlgebraicSpaces B S hS}
    {K K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))} {i r : ℤ}
    (hK : IsFreeOfRankInDegree K i r) (e : K ≅ K') : IsFreeOfRankInDegree K' i r := by
  obtain ⟨n, hn, ⟨e'⟩⟩ := hK
  exact ⟨n, hn, ⟨e.symm ≪≫ e'⟩⟩

variable (B S hS) {X : AlgebraicSpaces B S hS}

/-- The points of `X` lying in the image of an étale chart `V` on which the derived pullback of `E`
is free of rank `r` in degree `i`. -/
def singleDegreeFreePoints
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (i r : ℤ) : Set (points B S hS X.1) :=
  {x | ∃ V : SmallEtale B S hS X.1,
    x ∈ Set.range (pointsMap B S hS (yoneda.obj V.1.left) V.1.hom) ∧
      IsFreeOfRankInDegree
        ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E)
        i r}

/-- The points at which `E` is free of rank `r` in degree `i` form an open set. -/
theorem isOpen_singleDegreeFreePoints
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (i r : ℤ) : IsOpen (singleDegreeFreePoints B S hS E i r) := by
  have : singleDegreeFreePoints B S hS E i r = ⋃ V : {V : SmallEtale B S hS X.1 //
      IsFreeOfRankInDegree
        ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E)
        i r}, Set.range (pointsMap B S hS (yoneda.obj V.1.1.left) V.1.1.hom) := by
    ext x
    simp only [singleDegreeFreePoints, Set.mem_setOf_eq, Set.mem_iUnion]
    exact ⟨fun ⟨V, hx, hV⟩ => ⟨⟨V, hV⟩, hx⟩, fun ⟨V, hx⟩ => ⟨V.1, hx, V.2⟩⟩
  rw [this]
  exact isOpen_iUnion fun V => (isOpenMap_pointsMap_of_etale B S hS X.2 _ _ V.1.2).isOpen_range

end AlgebraicGeometry.Space

end
