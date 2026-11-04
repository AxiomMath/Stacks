module

public import StacksFrontier.Topology.Sheaves.Cohomology.KFlatAndDerivedPullback.ResolvingDatum
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatTensorShortExact
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories
public import StacksFrontier.Algebra.Homology.DerivedCategory.TriangleApproximation

/-!
# Degreewise pullback preserves a strictly perfect approximation

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `α : R ⟶ P` be a map of
K-flat complexes of `𝒪_Y`-modules which is an *approximation in degrees `> m`*: an isomorphism
on cohomology in every degree `> m` and a surjection on cohomology in degree `m`. The main
result says that `f^*α` is again such an approximation. This is the step of Stacks 09U7 at
which the base change is pushed through the approximation of Stacks 05TC.

## Main results

* `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.homologyBounds_modulePullback`: degreewise
  pullback along a morphism of ringed
  spaces preserves an approximation in degrees `> m` between K-flat complexes.
* `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.flatProperty`: flatness as an object property
  of `Mod(𝒪_Y)`, with the two inputs
  Stacks 05T7 asks of it: it contains a zero object, and every module is a quotient of a flat
  one.

## Implementation notes

The dictionary between "approximation in degrees `> m`" for the first map of a distinguished
triangle and "the third vertex is `≤ m - 1`" is general homological algebra and lives in
`StacksFrontier.Algebra.Homology.DerivedCategory.TriangleApproximation`, as
`DerivedCategory.triangle_obj₃_isLE_of_approximation` and
`DerivedCategory.approximation_of_triangle_isLE`; both directions are used below.

The argument is the dual of Stacks 05TC. The cone `C` of `α` is K-flat, and the hypotheses on
`α` say exactly that `C` has vanishing cohomology in degrees `≥ m`; Stacks 05T7 then produces
a quasi-isomorphism `s : F ⟶ C` from a complex `F` which is *strictly* bounded above by
`m - 1` and has flat terms, hence is K-flat by Stacks 06YQ. The second field of
`PullbackKFlatInput` applies to `s` — both ends are K-flat — so `f^*s` is a
quasi-isomorphism, and `f^*F` is strictly bounded above by `m - 1` because an additive functor
carries a zero object to a zero object. So `f^*C` has vanishing cohomology in degrees `≥ m`,
and `f^*C ≅ cone(f^*α)` carries that to the cone of `f^*α`, which is the conclusion read
backwards.

Every binder naming a complex is given the type `CochainComplex
  (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules _) ℤ`.
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y` is `StrictlyPerfect.OXMod Y` by
  `rfl`, but the instances of the tensor
product that K-flatness mentions are keyed on `Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf`, and
  against
another spelling of the ring sheaf they are searched for before the two are unified, which
fails; `StacksDraft.KFlat.modulePullback` is the degreewise pullback retyped for the same
reason.

## References

* [Stacks Project, Tag 05T7](https://stacks.math.columbia.edu/tag/05T7)
* [Stacks Project, Tag 05TC](https://stacks.math.columbia.edu/tag/05TC)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 09U7](https://stacks.math.columbia.edu/tag/09U7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry TopologicalSpace StrictlyPerfect ZeroObject

namespace AlgebraicGeometry.RingedSpace.KFlatDerivedPullback

universe v u

attribute [local instance] HasDerivedCategory.standard

/-! ### Cohomology of a complex versus cohomology of its image in the derived category -/

section Square

variable {A : Type u} [Category.{v} A]

/-- The two parallel edges of a commutative square whose other two edges are invertible are
epimorphisms together. -/
theorem epi_iff_of_isIso_sq {W X Y Z : A} (f : W ⟶ X) (g : Y ⟶ Z) (a : W ≅ Y) (b : X ≅ Z)
    (w : f ≫ b.hom = a.hom ≫ g) : Epi f ↔ Epi g := by
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · rw [show g = a.inv ≫ f ≫ b.hom by rw [w, Iso.inv_hom_id_assoc]]
    infer_instance
  · rw [show f = (a.hom ≫ g) ≫ b.inv by
      rw [← w, Category.assoc, Iso.hom_inv_id, Category.comp_id]]
    infer_instance

end Square

section Derived

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory A]

/-- Invertibility of the `i`-th homology of `Q α` is invertibility of the `i`-th homology map
of `α`: the two functors `Q ⋙ homologyFunctor i` and `HomologicalComplex.homologyFunctor i`
are isomorphic. -/
theorem isIso_homologyFunctor_map_Q_map_iff {K L : CochainComplex A ℤ} (α : K ⟶ L) (i : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor A i).map (DerivedCategory.Q.map α)) ↔
      IsIso (HomologicalComplex.homologyMap α i) :=
  NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors A i) α

/-- Surjectivity of the `i`-th homology of `Q α` is surjectivity of the `i`-th homology map of
`α`: the naturality square of `DerivedCategory.homologyFunctorFactors` at `α` has invertible
vertical maps. -/
theorem epi_homologyFunctor_map_Q_map_iff {K L : CochainComplex A ℤ} (α : K ⟶ L) (i : ℤ) :
    Epi ((DerivedCategory.homologyFunctor A i).map (DerivedCategory.Q.map α)) ↔
      Epi (HomologicalComplex.homologyMap α i) :=
  epi_iff_of_isIso_sq _ _ ((DerivedCategory.homologyFunctorFactors A i).app K)
    ((DerivedCategory.homologyFunctorFactors A i).app L)
    (DerivedCategory.homologyFunctorFactors_hom_naturality α i)

end Derived

/-! ### Flatness as an object property -/

/-- Flatness of a sheaf of `O_Y`-modules, read as a property of objects of `Mod(O_Y)`. -/
abbrev flatProperty (Y : RingedSpace.{u, u}) : ObjectProperty (Modules Y) :=
  fun M => AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) M

/-- **The zero sheaf of modules is flat.**  Tensoring on the right with it is the zero
endofunctor of `Mod(O_Y)`, because `M ⊗_{O_Y} -` is additive for every `M`, and a zero functor
preserves all limits and colimits. -/
instance containsZero_flatProperty (Y : RingedSpace.{u, u}) :
    (flatProperty Y).ContainsZero where
  exists_zero := by
    refine ⟨0, isZero_zero _, ?_⟩
    have hz : IsZero ((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).flip.obj
        (0 : Modules Y)) :=
      Functor.isZero _ fun G =>
        Functor.map_isZero ((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj G)
          (isZero_zero _)
    exact (Stacks.SheafOfModules.FlatCoproduct.isFlat_iff_exactFunctor_sheafTensor.{u, u} Y.sheaf
      (0 : Modules Y)).2
      ⟨⟨fun J _ _ => Functor.preservesLimitsOfShape_of_isZero _ hz J⟩,
        ⟨fun J _ _ => Functor.preservesColimitsOfShape_of_isZero _ hz J⟩⟩

/-- **Every sheaf of `O_Y`-modules is a quotient of a flat one**, which is Stacks 03EX's
`exists_epi_from_flat` read on a ringed space.  Together with
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.containsZero_flatProperty` this is what Stacks
  05T7 asks of the class of flat
modules. -/
theorem exists_flat_epi (Y : RingedSpace.{u, u}) (M : Modules Y) :
    ∃ (N : Modules Y) (_ : flatProperty Y N) (p : N ⟶ M), Epi p := by
  obtain ⟨N, π, hflat, hepi⟩ :=
    Stacks.SheafOfModules.FlatTensorShortExact.exists_epi_from_flat Y.sheaf M
  exact ⟨N, hflat, π, hepi⟩

/-! ### Degreewise pullback preserves an approximation -/

/-- **Degreewise pullback preserves an approximation between K-flat complexes.**  Let
`f : X ⟶ Y` be a morphism of ringed spaces and `α : R ⟶ P` a map of K-flat complexes of
`O_Y`-modules which is an isomorphism on cohomology in degrees `> m` and a surjection on
cohomology in degree `m`.  Then `f^*α` has the same two properties.

The cone of `α` is K-flat and, by the long exact sequence, has vanishing cohomology in degrees
`≥ m`; Stacks 05T7 resolves it by a complex `F` strictly bounded above by `m - 1` with flat
terms, which is K-flat by Stacks 06YQ.  Degreewise pullback inverts the quasi-isomorphism
`F ⟶ cone(α)` — both ends are K-flat — and carries `F` to a complex again strictly bounded
above by `m - 1`, so `f^*cone(α) ≅ cone(f^*α)` has vanishing cohomology in degrees `≥ m`. -/
theorem homologyBounds_modulePullback (h :
  AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.PullbackKFlatInput.{u})
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    {R P : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ} (α : R ⟶
      P) (m : ℤ)
    (hR : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y R) (hP :
      AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y P)
    (hiso : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j))
    (hepi : Epi (HomologicalComplex.homologyMap α m)) :
    (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap
        (((StacksDraft.KFlat.modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map α)
        j)) ∧
      Epi (HomologicalComplex.homologyMap
        (((StacksDraft.KFlat.modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map α)
        m) := by
  -- Step 1: the cone of `α` is `≤ m - 1` in the derived category.
  have hQC : (DerivedCategory.Q.obj (CochainComplex.mappingCone α)).IsLE (m - 1) :=
    DerivedCategory.triangle_obj₃_isLE_of_approximation
      (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle α))
      (DerivedCategory.mappingCone_triangle_distinguished α) m
      (fun i hi => (isIso_homologyFunctor_map_Q_map_iff α i).2 (hiso i hi))
      ((epi_homologyFunctor_map_Q_map_iff α m).2 hepi)
  have hCLE : (CochainComplex.mappingCone α).IsLE (m - 1) :=
    (DerivedCategory.isLE_Q_obj_iff _ _).1 hQC
  -- Step 2: resolve it by a strictly bounded above complex with flat terms (Stacks 05T7).
  obtain ⟨F, s, hs, hFflat, hFLE⟩ :=
    (CochainComplex.exists_quasiIso_prop (flatProperty Y) (exists_flat_epi Y) (m - 1)).2
      (CochainComplex.mappingCone α)
  -- Step 3: pull back; `f^*s` is a quasi-isomorphism and `f^*F` is still strictly `≤ m - 1`.
  have hFpLE : CochainComplex.IsStrictlyLE
      (((StacksDraft.KFlat.modulePullback f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj F) (m - 1) := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact Functor.map_isZero _ (F.isZero_of_isStrictlyLE (m - 1) i hi)
  have : IsIso (DerivedCategory.Q.map
      (((StacksDraft.KFlat.modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map s)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _
      (((StacksDraft.KFlat.modulePullback f).mapHomologicalComplex
        (ComplexShape.up ℤ)).map s)).2
      (h.quasiIso_pullback f s hs (kFlat_of_boundedAbove_of_flat Y F ⟨m - 1, hFLE⟩ hFflat)
        (kFlat_mappingCone Y α hR hP))
  have hQpC : (DerivedCategory.Q.obj (((StacksDraft.KFlat.modulePullback f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (CochainComplex.mappingCone α))).IsLE (m - 1) :=
    DerivedCategory.TStructure.t.isLE_of_iso
      (asIso (DerivedCategory.Q.map (((StacksDraft.KFlat.modulePullback f).mapHomologicalComplex
        (ComplexShape.up ℤ)).map s))) (m - 1)
  -- Step 4: identify the pullback of the cone with the cone of the pullback.
  have hcone : (DerivedCategory.Q.obj (CochainComplex.mappingCone
      (((StacksDraft.KFlat.modulePullback f).mapHomologicalComplex
        (ComplexShape.up ℤ)).map α))).IsLE (m - 1) :=
    DerivedCategory.TStructure.t.isLE_of_iso (DerivedCategory.Q.mapIso
      (CochainComplex.mappingCone.mapHomologicalComplexIso α
        (StacksDraft.KFlat.modulePullback f))) (m - 1)
  -- Step 5: read the conclusion off the cone triangle of `f^*α`.
  obtain ⟨h₁, h₂⟩ := DerivedCategory.approximation_of_triangle_isLE
    (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle
      (((StacksDraft.KFlat.modulePullback f).mapHomologicalComplex
        (ComplexShape.up ℤ)).map α)))
    (DerivedCategory.mappingCone_triangle_distinguished _) m hcone
  exact ⟨fun j hj => (isIso_homologyFunctor_map_Q_map_iff _ j).1 (h₁ j hj),
    (epi_homologyFunctor_map_Q_map_iff _ m).1 h₂⟩

end AlgebraicGeometry.RingedSpace.KFlatDerivedPullback

end
