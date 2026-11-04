module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedPerfectModel
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactDerivedHomologyComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.QcqsUnitCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPullbackPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisTag
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPushforwardDirectSums
public import StacksFrontier.Homology.Perfect.Characterizing
public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.AffineGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.QcqsOverAffine

/-!
# Perfect objects are compact in `D_QCoh` of a quasi-compact quasi-separated algebraic space

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S`. A perfect
object `E` of `D(𝒪_X)` is compact relative to `D_QCoh(𝒪_X)`: morphisms out of `E` commute with
direct sums of objects of `D_QCoh(𝒪_X)`. This is one half of Stacks 09M8 for algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.perfectIsQcohCompact_of_isElementaryDistinguishedSquare`: the
  Mayer–Vietoris step of the induction principle of Stacks 08GP.

## Implementation notes

The step across an elementary distinguished square `(U ⊆ W, V → W)` with intersection `P` is the
lower-shriek Mayer–Vietoris triangle of Stacks 08GV,
`j_{P!}E|_P ⟶ j_{U!}E|_U ⊕ j_{V!}E|_V ⟶ E ⟶ (j_{P!}E|_P)[1]`: the restrictions of a perfect
object along the étale morphisms `j` are perfect
(`AlgebraicGeometry.Space.isPerfect_smallEtaleDerivedModulePullback`), extension by zero keeps
relative compactness (`AlgebraicGeometry.Space.isQcohCompact_lowerShriek`), and relative
compactness passes to the third vertex of a distinguished triangle.

## References

* [Stacks Project, Tag 09M8](https://stacks.math.columbia.edu/tag/09M8)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Tag 08GV](https://stacks.math.columbia.edu/tag/08GV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Pretriangulated

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Every perfect object of `D(𝒪_W)` is compact relative to `D_QCoh(𝒪_W)`. -/
def PerfectIsQcohCompact (W : AlgebraicSpaces B S hS) : Prop :=
  ∀ E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2),
    RingedSite.IsPerfect (smallEtaleRingedSite B S hS W.1 W.2) E → IsQcohCompact B S hS W E

/-- The restriction of a perfect object along an étale morphism, followed by extension by zero,
is compact relative to `D_QCoh` as soon as perfect objects of the source are. -/
theorem isQcohCompact_lowerShriek_restrict_of_isPerfect {Z W : AlgebraicSpaces B S hS}
    (j : Z ⟶ W) (hj : IsEtale B S hS j.hom) (hZ : PerfectIsQcohCompact Z)
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS W.1 W.2) E) :
    IsQcohCompact B S hS W ((etaleModulePullback.{u, u} B S hS j hj ⋙
      etaleModuleLowerShriek B S hS j hj).mapDerivedCategory.obj E) := by
  have hres : RingedSite.IsPerfect (smallEtaleRingedSite B S hS Z.1 Z.2)
      ((etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory.obj E) := by
    obtain ⟨K, hK, ⟨e⟩⟩ := isPerfect_smallEtaleDerivedModulePullback j E hE
    exact ⟨K, hK, ⟨e ≪≫ (smallEtaleDerivedModulePullbackIsoEtale B S hS j hj).app E⟩⟩
  exact (isQcohCompact_lowerShriek j hj (hZ _ hres)).of_iso
    ((Stacks.DerivedFunctor.mapDerivedCategoryCompIso _ _).app E)

section Square

attribute [local instance] smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

include hsq in
/-- **The Mayer–Vietoris step.** For an elementary distinguished square `(U ⊆ W, V → W)` with
intersection `P`, if the perfect objects on `U`, `V` and `P` are compact relative to `D_QCoh`, so
are the perfect objects on `W`. -/
theorem perfectIsQcohCompact_of_isElementaryDistinguishedSquare
    (hU : PerfectIsQcohCompact (edsOpen B S hS hsq))
    (hV : PerfectIsQcohCompact (edsEtale B S hS hsq))
    (hP : PerfectIsQcohCompact (edsInter B S hS hsq)) :
    PerfectIsQcohCompact W := by
  intro E hE
  obtain ⟨δ, hT⟩ := (mayerVietoris_shortExact_and_mem_distTriang B S hS hsq).2 E
  exact IsQcohCompact.obj₃ _ hT
    (isQcohCompact_lowerShriek_restrict_of_isPerfect _ (isEtale_edsInterHom B S hS hsq) hP E hE)
    (IsQcohCompact.biprod
      (isQcohCompact_lowerShriek_restrict_of_isPerfect _ (isEtale_edsOpenHom B S hS hsq) hU E hE)
      (isQcohCompact_lowerShriek_restrict_of_isPerfect _ (isEtale_edsEtaleHom B S hS hsq) hV E hE))

end Square

/-! ### Compactness along a left adjoint -/

/-- A left adjoint whose right adjoint commutes with direct sums carries compact objects to
compact objects. -/
theorem isCompactObject_obj_of_adjunction {D E : Type*} [Category D] [Preadditive D]
    [Category E] [Preadditive E] {L : D ⥤ E} {G : E ⥤ D} [L.Additive] [G.Additive]
    (adj : L ⊣ G) [∀ I : Type u, PreservesColimitsOfShape (Discrete I) G] (K : D)
    (hK : IsCompactObject.{u} K) : IsCompactObject.{u} (L.obj K) := by
  classical
  refine ⟨@fun I _ A _ => ?_⟩
  have hc : IsColimit (Cofan.mk (G.obj (∐ A)) fun i => G.map (Sigma.ι A i)) :=
    (isColimitMapCoconeCofanMkEquiv G A (Sigma.ι A))
      (isColimitOfPreserves G (coproductIsCoproduct A))
  exact (bijective_cofanMap_map_iff_of_adjunction adj K (Sigma.ι A)).1
    (bijective_cofanMap K hK _ hc)

/-- **`Lf^*` preserves compact objects of `D_QCoh`** along a quasi-compact quasi-separated
morphism of algebraic spaces. -/
theorem isCompactObject_quasicoherentDerivedModulePullback {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) (hE : IsCompactObject.{u} E) :
    IsCompactObject.{u} ((quasicoherentDerivedModulePullback f).obj E) := by
  have := fun I : Type u => preservesCoproducts_quasicoherentDerivedPushforward B S hS f hfqc hfqs I
  have : (quasicoherentDerivedModulePullback (B := B) (S := S) (hS := hS) f).Additive :=
    (quasicoherentDerivedModuleAdjunction B S hS f hfqc hfqs).left_adjoint_additive
  have : (quasicoherentDerivedPushforward B S hS f hfqc hfqs).Additive :=
    (quasicoherentDerivedModuleAdjunction B S hS f hfqc hfqs).right_adjoint_additive
  exact isCompactObject_obj_of_adjunction (quasicoherentDerivedModuleAdjunction B S hS f hfqc hfqs)
    E hE

/-! ### Compact objects on an affine algebraic space are perfect -/

section Affine

attribute [local instance 10000] HasDerivedCategory.standard

/-- The image of a compact object of `D_QCoh` of a represented affine algebraic space under the
inverse of the equivalence with the derived category of modules is perfect. -/
private theorem isPerfect_inverse_obj_of_isCompactObject_yoneda (U : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (E : QuasicoherentDerivedCategory.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U))
    (hE : IsCompactObject.{u} E) :
    StacksDraft.Perfect.IsPerfect
      ((representedAffineDerivedEquivalence B S hS U).inverse.obj E) := by
  let e := representedAffineDerivedEquivalence B S hS U
  have : e.inverse.Additive := Functor.additive_of_preserves_binary_products _
  have : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  exact (StacksDraft.Perfect.isPerfect_iff_isCompactObject _).2
    ((isCompactObject_iff_isCompactObject_obj e.inverse E).1 hE)

/-- **Compact objects of `D_QCoh` of a represented affine algebraic space are perfect.** -/
theorem isPerfect_of_isCompactObject_yoneda (U : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (E : QuasicoherentDerivedCategory.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U))
    (hE : IsCompactObject.{u} E) :
    (smallEtaleRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).IsPerfect
      E.obj := by
  have hP := isPerfect_inverse_obj_of_isCompactObject_yoneda U E hE
  let e := representedAffineDerivedEquivalence B S hS U
  exact RingedSite.IsPerfect.of_iso _
    (isPerfect_representedAffineDerivedAssociated_obj B S hS U _ hP)
    ((ObjectProperty.ι _).mapIso (e.counitIso.app E))

/-- Compact objects of `D_QCoh` of a represented affine algebraic space have a strictly perfect
model. -/
theorem hasStrictlyPerfectModel_of_isCompactObject_yoneda (U : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (E : QuasicoherentDerivedCategory.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U))
    (hE : IsCompactObject.{u} E) :
    HasStrictlyPerfectModel B S hS (Y := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      E.obj := by
  have hP := isPerfect_inverse_obj_of_isCompactObject_yoneda U E hE
  let e := representedAffineDerivedEquivalence B S hS U
  exact (hasStrictlyPerfectModel_representedAffineDerivedAssociated_obj B S hS U _ hP).of_iso
    ((ObjectProperty.ι _).mapIso (e.counitIso.app E))

end Affine

/-- **Compact objects of `D_QCoh` of an affine algebraic space are perfect.** -/
theorem isPerfect_of_isCompactObject_of_isAffineSpace (X : AlgebraicSpaces B S hS)
    (hX : IsAffineSpace B S hS X.1) (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (hE : IsCompactObject.{u} E) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E.obj := by
  have hZ := B.contains_terminal
  obtain ⟨T₀, hT₀, ⟨i⟩⟩ := hX
  have := hT₀
  let T := chartOfIso B S hS T₀ i
  have hT : IsTerminal T := isTerminalChartOfIso T₀ i
  let p := chartToSpace B S hS X T
  have hpqc : IsQuasiCompact B S hS p.hom :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ X.2
      (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ ⟨T₀, hT₀, ⟨i⟩⟩)
      (isQuasiCompactSpace_yoneda_obj B S hS
        (show CompactSpace ((BigFppfOver.toScheme B S hS).obj T₀) from inferInstance)) p.hom
  have hpqs : IsQuasiSeparated B S hS p.hom :=
    isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ (chartSpace B S hS X T).2
      (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ (isAffineSpace_yoneda B S hS T₀ hT₀))
      p.hom
  have hmodel : HasStrictlyPerfectModel B S hS
      ((smallEtaleDerivedModulePullback B S hS p).obj E.obj) :=
    hasStrictlyPerfectModel_of_isCompactObject_yoneda T₀
      ((quasicoherentDerivedModulePullback p).obj E)
      (isCompactObject_quasicoherentDerivedModulePullback p hpqc hpqs E hE)
  refine isPerfect_of_hasStrictlyPerfectModel_chart E.obj fun U => ⟨fun _ _ => True, ?_,
    fun V g _ => hmodel.chartRestriction (hT.from V)⟩
  have : Sieve.generate (fun _ _ => True : Presieve U) = ⊤ :=
    eq_top_iff.2 fun W f _ => ⟨W, 𝟙 W, f, trivial, Category.id_comp f⟩
  rw [this]
  exact (SmallEtale.topology B S hS X.1).top_mem U

/-- **Stacks 09M8, compact implies perfect.** On a quasi-separated algebraic space a compact
object of `D_QCoh` is perfect. -/
theorem isPerfect_of_isCompactObject (X : AlgebraicSpaces B S hS)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) (hE : IsCompactObject.{u} E) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E.obj := by
  have hZ := B.contains_terminal
  refine isPerfect_of_hasStrictlyPerfectModel_chart E.obj fun U =>
    ⟨fun W _ => IsAffineChart B S hS X.1 W, generate_isAffineChart_mem_topology B S hS X U,
      fun V g hV => ?_⟩
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj V)) := hV
  let p := chartToSpace B S hS X V
  have hpqc : IsQuasiCompact B S hS p.hom :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ X.2 hqs
      (isQuasiCompactSpace_yoneda_obj B S hS (show CompactSpace ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS X.1).obj V)) from inferInstance)) p.hom
  have hpqs : IsQuasiSeparated B S hS p.hom :=
    isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ (chartSpace B S hS X V).2
      (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ
        (isAffineSpace_chartSpace B S hS X V hV)) p.hom
  exact hasStrictlyPerfectModel_of_isCompactObject_yoneda ((SmallEtale.toOver B S hS X.1).obj V)
    ((quasicoherentDerivedModulePullback p).obj E)
    (isCompactObject_quasicoherentDerivedModulePullback p hpqc hpqs E hE)

end AlgebraicGeometry.Space

end
