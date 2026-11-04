module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveGlobalSectionsPerfectTwistStalk
public import StacksFrontier.Homology.TensorComplex.BifunctorSingleRightComplex
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePointUniverse
public import StacksFrontier.AlgebraicGeometry.BoundedFibreDescent.GeometricFibre

/-!
# Exactness of the twist complex of a resolution, checked on stalks

Let `Y` be a scheme, `Λ` a ring, not necessarily commutative, `G` a sheaf of `Λ`-modules on the
small étale site of `Y` whose stalks at a conservative family of points are finite projective,
`G[0] ⟶ I` a resolution and `R` a complex of finite free right `Λ`-modules with finitely many
nonzero terms, exact in a degree `j ≠ 0`. Then the total complex `R ⊠ I` of the twists is exact
in degree `j`: at a point its stalk is `Tot(R ⊗[Λ] I_Φ)`, quasi-isomorphic to `R ⊗[Λ] G_Φ`, and
tensoring with the finite projective module `G_Φ` is exact. This is the exactness input of the
dimension shifting in the proof of [Stacks, Tag 03TV].

## Main results

* `Stacks.SheafTwist.exactAt_twistComplex`: `R ⊠ I` is exact wherever `R` is, away from `0`.

## References

* [Stacks Project, Tag 03TV](https://stacks.math.columbia.edu/tag/03TV)
* [Stacks Project, Tag 05PP](https://stacks.math.columbia.edu/tag/05PP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry HomologicalComplex
open StacksDraft.Perfect StacksDraft.Perfect.TorTotal

universe u r

namespace Stacks.SheafTwist

variable {Λ : Type r} [Ring Λ] (D : BalancedDerivedTensoring.{r, max (u + 1) r} Λ)
  (Y : Scheme.{u})

/-- The stalk of a sheaf of `Λ`-modules at a point is additive, being left exact. -/
instance moduleSheafFiber_additive
    (Φ : GrothendieckTopology.Point.{max (u + 1) r} Y.smallEtaleTopology) :
    (Φ.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The stalk of a sheaf of `Λ`-modules at a point is exact. -/
instance moduleSheafFiber_preservesHomology
    (Φ : GrothendieckTopology.Point.{max (u + 1) r} Y.smallEtaleTopology) :
    (Φ.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- **The twist complex of a resolution is exact on stalks wherever `R` is exact away from `0`.**
At a point `Φ` whose stalk `G_Φ` is finite projective, the stalk of `R ⊠ I` in degree `j` is
exact when `R` is exact in degree `j ≠ 0`. -/
lemma exactAt_twistComplex_sheafFiber
    (R : CochainComplex (FiniteFree.{max (u + 1) r} Λ) ℤ) (e c : ℤ)
    (h : ∀ p, p < e ∨ c < p → IsZero (R.X p))
    (G : Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y)
    (I : CochainComplex (Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y) ℤ)
    (ι : (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G ⟶ I) [QuasiIso ι]
    [HasMapBifunctor R I (twist.{u, r} D Y) (ComplexShape.up ℤ)]
    (Φ : GrothendieckTopology.Point.{max (u + 1) r} Y.smallEtaleTopology)
    [Module.Finite Λ ((Φ.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)).obj G)]
    [Module.Projective Λ ((Φ.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)).obj G)]
    (j : ℤ) (_hj : j ≠ 0)
    (hR : (((ObjectProperty.ι (finiteFree.{max (u + 1) r} Λ)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj R).ExactAt j) :
    ((Φ.sheafFiber.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (twistComplex D Y R I)).ExactAt j := by
  let F := ObjectProperty.ι (finiteFree.{max (u + 1) r} Λ) ⋙ D.ordinary
  let IΦ := ((Φ.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj I
  let K := ((twist.{u, r} D Y).mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
    (ComplexShape.up ℤ)).obj R |>.obj I
  let K' := ((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
    (ComplexShape.up ℤ)).obj R).obj IΦ
  have hK := finite_support_of_columnBounds K e c (fun p hp =>
    isZero_of_forall_isZero_X fun q => ((twist.{u, r} D Y).map_isZero (h p hp)).obj (I.X q))
  have hK' := finite_support_of_columnBounds K' e c (fun p hp =>
    isZero_of_forall_isZero_X fun q => (F.map_isZero (h p hp)).obj (IΦ.X q))
  have : HasMapBifunctor R IΦ F (ComplexShape.up ℤ) :=
    HomologicalComplex₂.hasTotal_of_finite _ _ hK'
  have : (HomologicalComplex₂.TotalMap.mapBicomplex Φ.sheafFiber K).HasTotal
      (ComplexShape.up ℤ) := HomologicalComplex₂.hasTotal_of_iso
    (twistFiberBicomplexIso.{u, r} D Y Φ R I).symm (ComplexShape.up ℤ)
  -- the stalk of `R ⊠ I` is `Tot(R ⊗ I_Φ)`, read in abelian groups
  let eT : (Φ.sheafFiber.mapHomologicalComplex (ComplexShape.up ℤ)).obj (twistComplex D Y R I) ≅
      ((forget₂ (ModuleCat.{max (u + 1) r} ℤ) AddCommGrpCat.{max (u + 1) r}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (mapBifunctor R IΦ F (ComplexShape.up ℤ)) :=
    (HomologicalComplex₂.TotalMap.totalIsoOfFinite Φ.sheafFiber K hK).symm ≪≫
      HomologicalComplex₂.total.mapIso (twistFiberBicomplexIso.{u, r} D Y Φ R I)
        (ComplexShape.up ℤ) ≪≫
      HomologicalComplex₂.TotalMap.totalIsoOfFinite _ K' hK'
  rw [← exactAt_iff_of_quasiIsoAt eT.inv j]
  suffices hX : (mapBifunctor R IΦ F (ComplexShape.up ℤ)).ExactAt j from
    hX.map (forget₂ (ModuleCat.{max (u + 1) r} ℤ) AddCommGrpCat.{max (u + 1) r})
  let R' := ((ObjectProperty.ι (finiteFree.{max (u + 1) r} Λ)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj R
  have h' : ∀ p, p < e ∨ c < p → IsZero (R'.X p) := fun p hp =>
    (ObjectProperty.ι (finiteFree.{max (u + 1) r} Λ)).map_isZero (h p hp)
  have hB (K : CochainComplex (ModuleCat.{max (u + 1) r} Λ) ℤ) :
      HasMapBifunctor R' K D.ordinary (ComplexShape.up ℤ) :=
    hasMapBifunctor_of_bounds D.ordinary R' K e c h'
  show (mapBifunctor R' IΦ D.ordinary (ComplexShape.up ℤ)).ExactAt j
  -- `I_Φ` resolves `G_Φ`
  let M := (Φ.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)).obj G
  let eG : (CochainComplex.singleFunctor _ 0).obj M ≅
      ((Φ.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G) :=
    ((HomologicalComplex.singleMapHomologicalComplex
      (Φ.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)) (ComplexShape.up ℤ) 0).app G).symm
  let ψ : (CochainComplex.singleFunctor _ 0).obj M ⟶ IΦ :=
    eG.hom ≫ ((Φ.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map ι
  have : QuasiIso (((Φ.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map ι) := by
    have := moduleSheafFiber_additive.{u, r} (Λ := Λ) Y Φ
    have := moduleSheafFiber_preservesHomology.{u, r} (Λ := Λ) Y Φ
    exact HomologicalComplex.quasiIso_map_of_preservesHomology _ _
  have : QuasiIso ψ := inferInstance
  have hψ : QuasiIso (mapBifunctorMap (𝟙 R') ψ D.ordinary (ComplexShape.up ℤ)) :=
    quasiIso_mapBifunctorMap_right_of_bounds D.ordinary R' ψ
      (fun p => preservesHomology_ordinary_obj_of_free D (R.X p).obj) e c h'
  rw [← exactAt_iff_of_quasiIsoAt (mapBifunctorMap (𝟙 R') ψ D.ordinary (ComplexShape.up ℤ)) j,
    exactAt_iff_of_quasiIsoAt (HomologicalComplex.mapBifunctorSingleRightIso D.ordinary R' M).hom j]
  have := preservesHomology_ordinary_flip_obj_of_projective.{u, r} D M
  exact hR.map (D.ordinary.flip.obj M)

/-- The universe lift of the geometric point of `Y` attached to a point `y`, as a point of the
small étale site relative to the coefficient universe `max (u + 1) r`. -/
abbrev geometricSitePoint (y : Y) :
    GrothendieckTopology.Point.{max (u + 1) r} Y.smallEtaleTopology :=
  (Scheme.pointSmallEtale (Stacks.Etale.ofPoint y).hom).ulift.{max (u + 1) r}

/-- The lifted geometric points of `Y` form a conservative family. -/
lemma isConservativeFamilyOfPoints_geometricSitePoint :
    (ObjectProperty.ofObj (geometricSitePoint.{u, r} Y)).IsConservativeFamilyOfPoints :=
  Scheme.isConservative_pointSmallEtale_ulift.{r, u} (fun y : Y => (Stacks.Etale.ofPoint y).hom)
    (Set.eq_univ_of_forall fun y =>
      Set.mem_iUnion.2 ⟨y, default, Stacks.Etale.ofPoint_hom_base y _⟩)

/-- **The twist complex of a resolution is exact wherever `R` is, away from degree `0`**, when the
stalks of `G` at the geometric points of `Y` are finite projective: exactness is checked on stalks
(Stacks 05PP), where it is `exactAt_twistComplex_sheafFiber`. -/
theorem exactAt_twistComplex
    (R : CochainComplex (FiniteFree.{max (u + 1) r} Λ) ℤ) (e c : ℤ)
    (h : ∀ p, p < e ∨ c < p → IsZero (R.X p))
    (G : Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y)
    (hG : ∀ y : Y,
      Module.Finite Λ (((geometricSitePoint.{u, r} Y y).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).obj G) ∧
      Module.Projective Λ (((geometricSitePoint.{u, r} Y y).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).obj G))
    (I : CochainComplex (Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y) ℤ)
    (ι : (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G ⟶ I) [QuasiIso ι]
    [HasMapBifunctor R I (twist.{u, r} D Y) (ComplexShape.up ℤ)]
    (j : ℤ) (hj : j ≠ 0)
    (hR : (((ObjectProperty.ι (finiteFree.{max (u + 1) r} Λ)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj R).ExactAt j) :
    (twistComplex D Y R I).ExactAt j := by
  refine (Stacks.StalkExact.exact_iff_forall_sheafFiber_exact
    (isConservativeFamilyOfPoints_geometricSitePoint.{u, r} Y) _).2 fun Φ => ?_
  obtain ⟨Φ, hΦ⟩ := Φ
  obtain ⟨y⟩ := hΦ
  have := (hG y).1
  have := (hG y).2
  exact exactAt_twistComplex_sheafFiber D Y R e c h G I ι (geometricSitePoint.{u, r} Y y) j hj hR

end Stacks.SheafTwist

end
