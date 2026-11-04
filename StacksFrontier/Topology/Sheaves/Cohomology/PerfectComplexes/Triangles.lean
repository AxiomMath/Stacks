module

public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Defs
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.DerivedCharacterization
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.MappingCone

/-!
# Perfect objects and distinguished triangles

In the derived category of modules on a ringed space, perfectness is a two-out-of-three property
for distinguished triangles (Tag 08CR).

## Main results

* `Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₃_of_distinguished`,
  `Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₂_of_distinguished` and
  `Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₁_of_distinguished` are the three
  implications, for any model of the derived category.
* `Stacks.Cohomology.PerfectComplexTriangles.exists_mappingCone_iso_obj₃`: over any abelian
  category, the third vertex of a distinguished triangle whose first two vertices are represented
  by complexes is represented by the mapping cone of a chain map out of the first representative.
* `Stacks.Cohomology.PerfectComplexTriangles.strict_model_of_le`: a strictly perfect model of a
  perfect object over an open restricts to a smaller open, in any models of the derived categories
  of the open subspaces.

## Implementation notes

The argument takes place at the level of complexes. The first two vertices are represented by
perfect complexes `E₁` and `E₂`, and the first map of the triangle is a left fraction
`Q(γ) ≫ Q(s)⁻¹` with `s : E₂ ⟶ G` a quasi-isomorphism; by uniqueness of the third vertex of a
distinguished triangle, the third vertex is `Q` of the mapping cone of `γ : E₁ ⟶ G`
(`Stacks.Cohomology.PerfectComplexTriangles.exists_mappingCone_iso_obj₃`). The complex `G` is
perfect because `s` is a quasi-isomorphism, and the mapping cone of a morphism of perfect complexes
is perfect (`AlgebraicGeometry.RingedSpace.isPerfectComplex_mappingCone`). No derived category of
an open subspace occurs, so the three implications hold for any model of `D(O_X)`. The other two
implications follow by rotating the triangle.

Everything formal is stated over abstract abelian categories, which is not only tidier: each
such statement gets its own heartbeat budget, and elaborated against the ringed-space vocabulary
the same terms cost many times the default one.

The space, ring and module universes all coincide, as in the complex-level results the file builds
on, such as `AlgebraicGeometry.RingedSpace.isPerfectComplex_mappingCone`. The declarations whose
statements mention the derived categories of open subspaces take a family of models of those, at a
universe independent of that of `D(O_X)`.

## References

* [Stacks Project, Tag 08CR](https://stacks.math.columbia.edu/tag/08CR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace StrictlyPerfect

namespace AlgebraicGeometry.RingedSpace.PseudoCoherence

universe u

/-- Restriction to an open subspace preserves finite limits. -/
instance instPreservesFiniteLimitsRestrictModules (X : RingedSpace.{u, u})
    (U : Opens X.carrier) : PreservesFiniteLimits (restrictModules.{u} X U) :=
  Stacks.StrictlyPerfect.LocalRepresentation.restrictModules_preservesFiniteLimits X U

/-- Restriction to an open subspace preserves finite colimits. -/
instance instPreservesFiniteColimitsRestrictModules (X : RingedSpace.{u, u})
    (U : Opens X.carrier) : PreservesFiniteColimits (restrictModules.{u} X U) :=
  Stacks.StrictlyPerfect.LocalRepresentation.restrictModules_preservesFiniteColimits X U

instance {X Y : RingedSpace.{u, u}} (e : X ≅ Y) : (moduleEquivOfIso e).inverse.Additive :=
  ⟨by intros; ext U x; rfl⟩


instance instPreservesFiniteLimitsModuleEquivInverse {X Y : RingedSpace.{u, u}} (e : X ≅ Y) :
    PreservesFiniteLimits (moduleEquivOfIso e).inverse :=
  moduleEquivOfIso_preservesFiniteLimits e.symm

instance instPreservesFiniteColimitsModuleEquivInverse {X Y : RingedSpace.{u, u}} (e : X ≅ Y) :
    PreservesFiniteColimits (moduleEquivOfIso e).inverse :=
  moduleEquivOfIso_preservesFiniteColimits e.symm

end AlgebraicGeometry.RingedSpace.PseudoCoherence

namespace Stacks.Cohomology.PerfectComplexTriangles

universe u₁ u₂ u₃ v₁ v₂ v₃ w₁ w₂ w₃

/-! ### Exact functors and derived categories, over abstract abelian categories

Every step below is formal, and stating it abstractly gives each its own heartbeat budget: the
same terms elaborated against the ringed-space vocabulary are what forced the raised instance
and elaboration limits they replace. -/

section Abstract

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {E : Type u₃} [Category.{v₃} E] [Abelian E]

/-- **Isomorphic exact functors induce isomorphic functors on derived categories.** -/
def mapDerivedCategoryIsoOfNatIso [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    (F G : C ⥤ D) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    F.mapDerivedCategory ≅ G.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) _ _ _ _
    (F.mapDerivedCategoryFactors ≪≫
      Functor.isoWhiskerRight
        (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)) DerivedCategory.Q ≪≫
      G.mapDerivedCategoryFactors.symm)

/-- **The derived functor of a composite is the composite of the derived functors.** -/
def mapDerivedCategoryCompIso [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    [HasDerivedCategory.{w₃} E] (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    (F ⋙ G).mapDerivedCategory ≅ F.mapDerivedCategory ⋙ G.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) _ _ _ _
    ((F ⋙ G).mapDerivedCategoryFactors ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
          (ComplexShape.up ℤ)).symm DerivedCategory.Q ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ G.mapDerivedCategoryFactors.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight F.mapDerivedCategoryFactors.symm _ ≪≫
      Functor.associator _ _ _)

/-- **The third vertex of a distinguished triangle is a mapping cone.** In a distinguished
triangle of `D(C)` whose first two vertices are represented by complexes `E₁` and `E₂`, the third
vertex is represented by the mapping cone of a chain map `γ : E₁ ⟶ G` into a complex receiving a
quasi-isomorphism `s : E₂ ⟶ G`: the first map of the triangle is the left fraction
`Q(γ) ≫ Q(s)⁻¹` (`DerivedCategory.left_fac`), and the third vertex of a distinguished triangle is
determined by its first map up to isomorphism. -/
theorem exists_mappingCone_iso_obj₃ [HasDerivedCategory.{w₁} C]
    (T : Triangle (DerivedCategory C)) (hT : T ∈ distinguishedTriangles)
    {E₁ E₂ : CochainComplex C ℤ} (e₁ : DerivedCategory.Q.obj E₁ ≅ T.obj₁)
    (e₂ : DerivedCategory.Q.obj E₂ ≅ T.obj₂) :
    ∃ (G : CochainComplex C ℤ) (γ : E₁ ⟶ G) (s : E₂ ⟶ G), QuasiIso s ∧
      Nonempty (DerivedCategory.Q.obj (CochainComplex.mappingCone γ) ≅ T.obj₃) := by
  obtain ⟨G, γ, s, hs, hfac⟩ := DerivedCategory.left_fac (e₁.hom ≫ T.mor₁ ≫ e₂.inv)
  have hsq : e₁.hom ≫ T.mor₁ =
      DerivedCategory.Q.map γ ≫ ((asIso (DerivedCategory.Q.map s)).symm ≪≫ e₂).hom := by
    rw [Iso.trans_hom, Iso.symm_hom, asIso_inv, ← Category.assoc, ← hfac]
    simp
  obtain ⟨e, -⟩ := exists_iso_of_arrow_iso
    (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle γ)) T
    (DerivedCategory.mappingCone_triangle_distinguished γ) hT
    (Arrow.isoMk e₁ ((asIso (DerivedCategory.Q.map s)).symm ≪≫ e₂) hsq)
  exact ⟨G, γ, s, (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := s)).1 hs,
    ⟨Triangle.π₃.mapIso e⟩⟩

end Abstract

/-! ### Perfectness is local, and two-out-of-three in distinguished triangles -/

section Ringed

universe u d d'

variable {X : RingedSpace.{u, u}}

/-- A shift of a strictly perfect complex is strictly perfect. -/
theorem isStrictlyPerfect_shift {P : CochainComplex (OXMod.{u} X) ℤ}
    (hP : IsStrictlyPerfect P) (n : ℤ) : IsStrictlyPerfect (P⟦n⟧) :=
  ⟨hP.bounded.preimage (add_left_injective n).injOn, fun i => hP.directSummand (i + n)⟩

/-- The image of the preimage of `V` in `X.restrict U` is `V`, when `V ≤ U`. -/
theorem image_preimage_of_le {U V : Opens X.carrier} (hVU : V ≤ U) :
    U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj V) = V := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hVU hx⟩, hx, rfl⟩

open AlgebraicGeometry.RingedSpace.PseudoCoherence in
/-- **A local strict model restricts to a smaller open**, in any models of the derived categories
of the open subspaces. The model `P` over `U` and the restriction to `U` of a representative of
`K` are joined by a roof of quasi-isomorphisms (`CochainComplex.quasiIsoRoof_iff_nonempty_iso`),
and restriction to `V ≤ U` carries the roof to one over `V`. -/
theorem strict_model_of_le [HasDerivedCategory.{d} (OXMod.{u} X)]
    [∀ U : Opens X.carrier, HasDerivedCategory.{d'} (OXMod.{u, u} (X.restrict U.isOpenEmbedding))]
    {U V : Opens X.carrier} (hVU : V ≤ U) (K : DerivedCategory (OXMod.{u} X))
    (P : CochainComplex (OXMod.{u} (X.restrict U.isOpenEmbedding)) ℤ)
    (hP : IsStrictlyPerfect P)
    (eP : DerivedCategory.Q.obj P ≅ (restrictModules.{u} X U).mapDerivedCategory.obj K) :
    ∃ P' : CochainComplex (OXMod.{u} (X.restrict V.isOpenEmbedding)) ℤ,
      IsStrictlyPerfect P' ∧ Nonempty (DerivedCategory.Q.obj P' ≅
        (restrictModules.{u} X V).mapDerivedCategory.obj K) := by
  let E := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj E ≅ K := DerivedCategory.Q.objObjPreimageIso K
  have hr : CochainComplex.QuasiIsoRoof P (restrictComplex.{u} E U) :=
    (CochainComplex.quasiIsoRoof_iff_nonempty_iso _ _).2
      ⟨eP ≪≫ (restrictModules.{u} X U).mapDerivedCategory.mapIso e.symm ≪≫
        (restrictModules.{u} X U).mapDerivedCategoryFactors.app E⟩
  obtain ⟨i⟩ := (CochainComplex.quasiIsoRoof_iff_nonempty_iso _ _).1
    ((hr.map (AlgebraicGeometry.RingedSpace.restrictModulesOfLE X hVU)).precomp_right_iso
      (AlgebraicGeometry.RingedSpace.restrictComplexOfLEIso X hVU E).symm)
  exact ⟨_, AlgebraicGeometry.RingedSpace.isStrictlyPerfect_restrictModulesOfLE hVU hP,
    ⟨i ≪≫ ((restrictModules.{u} X V).mapDerivedCategoryFactors.app E).symm ≪≫
      (restrictModules.{u} X V).mapDerivedCategory.mapIso e⟩⟩

open AlgebraicGeometry.RingedSpace.PseudoCoherence in
/-- A shift of a perfect derived object is perfect. -/
theorem isPerfect_shift [HasDerivedCategory.{d} (OXMod.{u} X)]
    {K : DerivedCategory (OXMod.{u} X)} (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect K) (n :
      ℤ) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (K⟦n⟧) := by
  obtain ⟨E, hE, ⟨e⟩⟩ := hK
  refine ⟨E⟦n⟧, ?_, ⟨(DerivedCategory.Q.commShiftIso n).app E ≪≫
    (shiftFunctor _ n).mapIso e⟩⟩
  obtain ⟨I, U, hcover, hU⟩ := (Stacks.Cohomology.PerfectComplexes.isPerfectComplex_iff E).mp hE
  refine (Stacks.Cohomology.PerfectComplexes.isPerfectComplex_iff _).mpr ⟨I, U, hcover, fun i => ?_⟩
  obtain ⟨P, hP, f, hf⟩ := hU i
  let F := (restrictModules.{u} X (U i)).mapHomologicalComplex (ComplexShape.up ℤ)
  refine ⟨P⟦n⟧, isStrictlyPerfect_shift hP n, f⟦n⟧' ≫ ((F.commShiftIso n).app E).inv, ?_⟩
  infer_instance

/-- Perfectness of a derived object depends only on its isomorphism class. -/
theorem isPerfect_of_iso [HasDerivedCategory.{d} (OXMod.{u} X)]
    {K L : DerivedCategory (OXMod.{u} X)} (e : K ≅ L) (hK :
      Stacks.Cohomology.PerfectComplexes.IsPerfect K) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect L := by
  obtain ⟨E, hE, ⟨i⟩⟩ := hK
  exact ⟨E, hE, ⟨i ≪≫ e⟩⟩

/-- **Tag 08CR, third object.** The third object of a distinguished triangle is perfect if the
first two are. With perfect complexes `E₁`, `E₂` representing the first two vertices, the third
vertex is `Q` of the mapping cone of a chain map `γ : E₁ ⟶ G` with `E₂ ⟶ G` a quasi-isomorphism
(`Stacks.Cohomology.PerfectComplexTriangles.exists_mappingCone_iso_obj₃`); `G` is perfect along
with `E₂`, and the mapping cone of a morphism of perfect complexes is perfect
(`AlgebraicGeometry.RingedSpace.isPerfectComplex_mappingCone`). -/
@[stacks 08CR "third object"]
  theorem isPerfect_obj₃_of_distinguished [HasDerivedCategory.{d} (OXMod.{u} X)]
    (T : Triangle (DerivedCategory (OXMod.{u} X))) (hT : T ∈ distinguishedTriangles)
    (h₁ : Stacks.Cohomology.PerfectComplexes.IsPerfect T.obj₁) (h₂ :
      Stacks.Cohomology.PerfectComplexes.IsPerfect T.obj₂) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect T.obj₃ := by
  obtain ⟨E₁, hE₁, ⟨e₁⟩⟩ := h₁
  obtain ⟨E₂, hE₂, ⟨e₂⟩⟩ := h₂
  obtain ⟨G, γ, s, hs, ⟨e⟩⟩ := exists_mappingCone_iso_obj₃ T hT e₁ e₂
  exact ⟨CochainComplex.mappingCone γ,
    AlgebraicGeometry.RingedSpace.isPerfectComplex_mappingCone γ hE₁
      (AlgebraicGeometry.RingedSpace.IsPerfectComplex.of_quasiIso hE₂ s hs), ⟨e⟩⟩

/-- **Tag 08CR, second object.** -/
@[stacks 08CR "second object"]
  theorem isPerfect_obj₂_of_distinguished [HasDerivedCategory.{d} (OXMod.{u} X)]
    (T : Triangle (DerivedCategory (OXMod.{u} X))) (hT : T ∈ distinguishedTriangles)
    (h₁ : Stacks.Cohomology.PerfectComplexes.IsPerfect T.obj₁) (h₃ :
      Stacks.Cohomology.PerfectComplexes.IsPerfect T.obj₃) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect T.obj₂ :=
  isPerfect_obj₃_of_distinguished T.invRotate (inv_rot_of_distTriang T hT)
    (isPerfect_shift h₃ (-1)) h₁

/-- **Tag 08CR, first object.** -/
@[stacks 08CR "first object"]
  theorem isPerfect_obj₁_of_distinguished [HasDerivedCategory.{d} (OXMod.{u} X)]
    (T : Triangle (DerivedCategory (OXMod.{u} X))) (hT : T ∈ distinguishedTriangles)
    (h₂ : Stacks.Cohomology.PerfectComplexes.IsPerfect T.obj₂) (h₃ :
      Stacks.Cohomology.PerfectComplexes.IsPerfect T.obj₃) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect T.obj₁ :=
  isPerfect_of_iso (shiftShiftNeg T.obj₁ (1 : ℤ))
    (isPerfect_shift (isPerfect_obj₃_of_distinguished T.rotate (rot_of_distTriang T hT) h₂ h₃)
      (-1))

end Ringed

end Stacks.Cohomology.PerfectComplexTriangles

end
