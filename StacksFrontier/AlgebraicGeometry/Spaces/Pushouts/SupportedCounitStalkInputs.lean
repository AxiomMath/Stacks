module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkCohomologyMap
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModuleStalkCartesianDictionary
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingStalkQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedSheafStalkAnyGeometricPointGeneral
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars

/-!
# Stalkwise inputs to Stacks 0AEU at the points of `f^{-1}Z`

Let `f : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S`, `Z ⊆ X` a closed subspace
with `f^{-1}Z ⟶ Z` an isomorphism and `f` flat at the points of `f^{-1}Z`, and `ȳ` a geometric
point of `Y` with image `x̄ = f(ȳ)`. The proof of Stacks 0AEU computes the stalk at `ȳ` of the
counit `Lf^*Rf_*Q ⟶ Q`. This file supplies three of its stalkwise inputs.

## Main results

* `AlgebraicGeometry.Space.isIso_directImageFiberMap_of_supportOfSheaf`: **the degree-zero case
  of Stacks 0AEQ on module fibres.** For an `𝒪_Y`-module `M` supported on `|f^{-1}Z|`, the
  comparison `θ : (f_*M)_x̄ ⟶ M_ȳ` of geometric module fibres is invertible. The map `θ`
  (`AlgebraicGeometry.Space.directImageFiberMap`) is defined through the counit `f^*f_*M ⟶ M`:
  its transpose along extension of scalars is the identification `(f^*N)_ȳ ≅ 𝒪_{Y,ȳ} ⊗ N_x̄` of
  Stacks 05V5 followed by the fibre of the counit
  (`AlgebraicGeometry.Space.directImageFiberMapTranspose_eq`), which is the compatibility with
  the counit that the proof of Stacks 0AEU uses.
* `AlgebraicGeometry.Space.bijective_quotientMap_closedSubspaceStalkIdeal`: if `ȳ` lies on
  `f^{-1}Z`, then `𝒪_{X,x̄}/I_x̄ ⟶ 𝒪_{Y,ȳ}/I_x̄𝒪_{Y,ȳ}` is bijective, `I_x̄` the stalk of the ideal
  of `Z`.

## Main definitions

* `AlgebraicGeometry.Space.DerivedPullbackGeometricStalkIsoType`: the type of the isomorphism
  `K_x̄ ⊗ᴸ_{𝒪_{X,x̄}} 𝒪_{Y,ȳ} ≅ (Lf^*K)_ȳ`, natural in `K ∈ D(𝒪_X)`, of which
  `AlgebraicGeometry.Space.derivedPullbackGeometricStalkIso` is a term.

The third input, that the geometric stalk of a cohomology sheaf is the cohomology of the derived
geometric stalk, holds because `AlgebraicGeometry.Space.geometricDerivedStalk` is
`Stacks.derivedModuleFiber`, the functor induced on derived categories by the exact stalk functor
`Stacks.sheafModuleFiberOfCommRing`, so that `CategoryTheory.Functor.mapDerivedCategoryHomologyIso`
and `CategoryTheory.Functor.isIso_mapDerivedCategory_map_iff` apply to it.

## Implementation notes

The degree-zero comparison is proved for abelian sheaves at universe `u + 1` in
`AlgebraicGeometry.Space.isIso_app_smallEtaleAbelianDirectImageStalkMap_of_support_of_isPullback`;
it is carried to module fibres by the dictionary
`AlgebraicGeometry.Space.directImageFiberMap_compat_ulift`, and the support of the lifted
abelian sheaf is the support of the module (`AlgebraicGeometry.Space.supportOfSheaf_uliftSheaf`).

The quotient statement is the argument of
`AlgebraicGeometry.Space.FormalGlueingSituation.bijective_quotientMap_etaleLocalRingMap` stopped
at the ideal `I_x̄` instead of an ideal of germs of chosen equations, and with only the hypotheses
it uses: no quasi-compactness, quasi-separatedness or finite presentation.

## References

* [Stacks Project, Tag 0AEU](https://stacks.math.columbia.edu/tag/0AEU)
* [Stacks Project, Tag 0AEQ](https://stacks.math.columbia.edu/tag/0AEQ)
* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
* [Stacks Project, Tag 05E9](https://stacks.math.columbia.edu/tag/05E9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Support is unchanged by a universe lift -/

section Support

universe c d m t

/-- An objectwise equivalence of two type-valued functors compatible with the maps induces an
equivalence of their colimit types. -/
def colimitTypeEquivOfObjEquiv {C : Type c} [Category.{d} C] (F : C ⥤ Type m) (G : C ⥤ Type t)
    (e : ∀ X, F.obj X ≃ G.obj X)
    (he : ∀ {X Y} (f : X ⟶ Y) x, e Y (F.map f x) = G.map f (e X x)) :
    F.ColimitType ≃ G.ColimitType where
  toFun := Quot.map (fun x ↦ ⟨x.1, e x.1 x.2⟩) (by
    rintro ⟨X, x⟩ ⟨Y, y⟩ ⟨f, h⟩
    dsimp at f h ⊢
    exact ⟨f, (congrArg (e Y) h).trans (he f x)⟩)
  invFun := Quot.map (fun x ↦ ⟨x.1, (e x.1).symm x.2⟩) (by
    rintro ⟨X, x⟩ ⟨Y, y⟩ ⟨f, h⟩
    dsimp at f h ⊢
    refine ⟨f, ?_⟩
    apply (e Y).injective
    simpa only [Equiv.apply_symm_apply, he] using h)
  left_inv x := by
    induction x using Quot.inductionOn with
    | _ x => change Quot.mk _ ⟨x.1, (e x.1).symm (e x.1 x.2)⟩ = Quot.mk _ x
             simp only [Equiv.symm_apply_apply]
  right_inv x := by
    induction x using Quot.inductionOn with
    | _ x => change Quot.mk _ ⟨x.1, e x.1 ((e x.1).symm x.2)⟩ = Quot.mk _ x
             simp only [Equiv.apply_symm_apply]

/-- **The support of an abelian sheaf on the small étale site does not change when its values
are lifted to a higher universe.** -/
theorem supportOfSheaf_uliftSheaf (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{m}) :
    supportOfSheaf B S hS X ((sheafCompose _ AddCommGrpCat.uliftFunctor.{t, m}).obj F) =
      supportOfSheaf B S hS X F := by
  ext x
  simp only [mem_supportOfSheaf_iff_exists]
  refine exists_congr fun p ↦ and_congr_right fun _ ↦ not_congr ?_
  exact (colimitTypeEquivOfObjEquiv _ _ (fun _ ↦ Equiv.ulift.symm)
    (fun _ _ ↦ rfl)).subsingleton_congr.symm

end Support

/-! ### The degree-zero case of Stacks 0AEQ on module fibres -/

section DirectImageFiber

variable {X Y Z W : AlgebraicSpaces B S hS}

/-- **The degree-zero case of Stacks 0AEQ on geometric module fibres.** Let `f : Y ⟶ X` be a
morphism of algebraic spaces, `i : Z ⟶ X` a closed immersion and `W = Y ×_X Z` with `i' : W ⟶ Y`
a closed immersion and `f' : W ⟶ Z` integral and universally injective. For every `𝒪_Y`-module
`M` supported on `|W|` and every geometric point `ȳ` of `Y`, the comparison
`θ : (f_*M)_{f(ȳ)} ⟶ M_ȳ` of geometric module fibres, which is defined through the counit
`f^*f_*M ⟶ M`, is an isomorphism. -/
theorem isIso_directImageFiberMap_of_supportOfSheaf (f : Y ⟶ X)
    (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom) (i' : W ⟶ Y)
    (hi' : IsClosedImmersion B S hS i'.hom) (f' : W ⟶ Z)
    (hf'int : IsIntegralHom B S hS f'.hom) (hf'inj : UniversallyInjective B S hS f'.hom)
    (sq : IsPullback f' i' i f) (y : GeometricPoint B S hS Y.1)
    (M : Modules.{u, u} B S hS Y.1 Y.2)
    (hM : supportOfSheaf B S hS Y.1
        ((SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS Y)).obj M) ⊆
      Set.range (pointsMap B S hS W.1 i'.hom)) :
    IsIso ((directImageFiberMap B S hS f y).app M) := by
  have h₀ := isIso_app_smallEtaleAbelianDirectImageStalkMap_of_support_of_isPullback B S hS f i
    hi i' hi' f' hf'int hf'inj sq y ((moduleUliftAbelianSheaf B S hS Y).obj M)
    ((supportOfSheaf_uliftSheaf B S hS Y.1 _).le.trans hM)
  have hc := directImageFiberMap_compat_ulift B S hS f y M
  have : IsIso ((moduleFiberStalkIso B S hS Y y
      (smallEtaleStalkPullbackRingMap B S hS f y)).hom.app M) :=
    Iso.isIso_hom ((moduleFiberStalkIso B S hS Y y
      (smallEtaleStalkPullbackRingMap B S hS f y)).app M)
  have h₁ : IsIso ((forget₂ _ AddCommGrpCat.{u} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}).map
      ((directImageFiberMap B S hS f y).app M) ≫
      (moduleFiberStalkIso B S hS Y y (smallEtaleStalkPullbackRingMap B S hS f y)).hom.app M) := by
    rw [hc]
    infer_instance
  have h₂ : IsIso ((forget₂ _ AddCommGrpCat.{u} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}).map
      ((directImageFiberMap B S hS f y).app M)) :=
    IsIso.of_isIso_comp_right _
      ((moduleFiberStalkIso B S hS Y y (smallEtaleStalkPullbackRingMap B S hS f y)).hom.app M)
  exact isIso_of_reflects_iso _
    (forget₂ _ AddCommGrpCat.{u} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u})

end DirectImageFiber

/-! ### The closed part is an isomorphism modulo the stalk of its ideal -/

section Quotient

variable {B S hS}

/-- **`𝒪_{X,x̄}/I_x̄ ⟶ 𝒪_{Y,ȳ}/I_x̄𝒪_{Y,ȳ}` is bijective at a point of `f^{-1}Z`.** Let
`f : Y ⟶ X` be a morphism of algebraic spaces and `Z ⊆ X` a closed subspace such that
`f^{-1}Z ⟶ Z` is an isomorphism and `f` is flat at every point of `f^{-1}Z`. At a geometric point
`ȳ` of `Y` lying on `f^{-1}Z`, with image `x̄`, the map of quotients of étale local rings by the
stalk `I_x̄` of the ideal of `Z` is bijective. Together with the flatness of `𝒪_{X,x̄} ⟶ 𝒪_{Y,ȳ}`
these are the hypotheses of Stacks 05E9 at the stalks. -/
theorem bijective_quotientMap_closedSubspaceStalkIdeal {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : Y ⟶ X)
    (Z : Subfunctor X) (hZ : IsClosedSubspace B S hS Z) (hfZ : IsIso (Z.fromPreimage f))
    (hflat : ∀ p : points B S hS (Z.preimage f).toFunctor,
      IsFlatAt B S hS f (pointsMap B S hS (Z.preimage f).toFunctor (Z.preimage f).ι p))
    (y : GeometricPoint B S hS Y)
    (hy : y.image ∈ Set.range (pointsMap B S hS (Z.preimage f).toFunctor (Z.preimage f).ι)) :
    letI := (etaleLocalRingMap hY f y).toAlgebra
    Function.Bijective
      (Ideal.quotientMap
        ((closedSubspaceStalkIdeal B S hS ⟨X, hX⟩ ⟨Z, hZ⟩ (geometricPointMap f y)).map
          (algebraMap ↥(etaleLocalRing B S hS X (geometricPointMap f y))
            ↥(etaleLocalRing B S hS Y y)))
        (algebraMap ↥(etaleLocalRing B S hS X (geometricPointMap f y))
          ↥(etaleLocalRing B S hS Y y)) Ideal.le_comap_map) := by
  have hflaty : let := (etaleLocalRingMap hY f y).toAlgebra
      Module.Flat ↥(etaleLocalRing B S hS X (geometricPointMap f y))
        ↥(etaleLocalRing B S hS Y y) := by
    obtain ⟨p, hp⟩ := hy
    exact (isFlatAt_iff_etaleLocalRingMap_flat hY hX f y).mp (hp ▸ hflat p)
  have hP := isClosedSubspace_preimage B S hS f Z hX hY hZ
  obtain ⟨z, rfl⟩ := exists_geometricPoint_map_eq_of_mem_range B S hS
    (ObjectProperty.homMk (Z.preimage f).ι :
      (⟨(Z.preimage f).toFunctor, hP.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩) hP.2 y hy
  have hpb0 : IsPullback
      (ObjectProperty.homMk (Z.fromPreimage f) :
        (⟨(Z.preimage f).toFunctor, hP.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Z.toFunctor, hZ.1⟩)
      (ObjectProperty.homMk (Z.preimage f).ι :
        (⟨(Z.preimage f).toFunctor, hP.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
      (ObjectProperty.homMk Z.ι :
        (⟨Z.toFunctor, hZ.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩)
      (ObjectProperty.homMk f : (⟨Y, hY⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩) :=
    IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS T)) (Subfunctor.isPullback_preimage f Z)
  have hcart := cartesian_etaleStalk_tensor_flat B S hS _ _ _ _ hpb0.flip z
  dsimp only [IsEtaleStalkTensorFlat] at hcart
  obtain ⟨φ, hφl, hφr, hφflat⟩ := hcart
  have hw : geometricPointMap f (geometricPointMap (Z.preimage f).ι z) =
      geometricPointMap Z.ι (geometricPointMap (Z.fromPreimage f) z) :=
    congrArg (fun k => geometricPointMap k z) (Subfunctor.isPullback_preimage f Z).w.symm
  let : IsLocalRing ↥(etaleLocalRing B S hS (Z.preimage f).toFunctor z) :=
    isLocalRing_etaleLocalRing B S hS _ hP.1 z
  let : Algebra
      ↥(etaleLocalRing B S hS X (geometricPointMap f (geometricPointMap (Z.preimage f).ι z)))
      ↥(etaleLocalRing B S hS Y (geometricPointMap (Z.preimage f).ι z)) :=
    (etaleLocalRingMap hY f (geometricPointMap (Z.preimage f).ι z)).toAlgebra
  let : Algebra
      ↥(etaleLocalRing B S hS X (geometricPointMap f (geometricPointMap (Z.preimage f).ι z)))
      ↥(etaleLocalRing B S hS Z.toFunctor (geometricPointMap (Z.fromPreimage f) z)) :=
    ((eqToHom (congrArg (etaleLocalRing B S hS X) hw) ≫
      CommRingCat.ofHom
        (etaleLocalRingMap hZ.1 Z.ι (geometricPointMap (Z.fromPreimage f) z))).hom).toAlgebra
  have : IsLocalHom (etaleLocalRingMap hP.1 (Z.preimage f).ι z) :=
    isLocalHom_etaleLocalRingMap B S hS hP.1 hY _ z
  have hβsurj : Function.Surjective (algebraMap
      ↥(etaleLocalRing B S hS X (geometricPointMap f (geometricPointMap (Z.preimage f).ι z)))
      ↥(etaleLocalRing B S hS Z.toFunctor (geometricPointMap (Z.fromPreimage f) z))) := by
    have h1 := surjective_etaleLocalRingMap_of_isClosedImmersion B S hS
      (ObjectProperty.homMk Z.ι :
        (⟨Z.toFunctor, hZ.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩) hZ.2
      (geometricPointMap (Z.fromPreimage f) z)
    have h2 := (ConcreteCategory.bijective_of_isIso
      (eqToHom (congrArg (etaleLocalRing B S hS X) hw))).2
    exact h1.comp h2
  have hδ := bijective_etaleLocalRingMap_of_isIso B S hS hP.1 hZ.1 (Z.fromPreimage f) z
  have hK := FormalGlueing.bijective_quotientMap_ker_of_tensor_flat hβsurj
    (etaleLocalRingMap hP.1 (Z.preimage f).ι z)
    (etaleLocalRingMap hP.1 (Z.fromPreimage f) z) hδ φ hφl hφr hφflat
  have hK₀ := ker_etaleLocalRingMap_le_closedSubspaceStalkIdeal_of_eq B S hS ⟨X, hX⟩
    ⟨Z, hZ⟩ (geometricPointMap (Z.fromPreimage f) z) _ hw
  exact FormalGlueing.bijective_quotientMap_of_pow_le (n := 1) (le_trans (pow_one _).le hK₀) hK

end Quotient

/-! ### The shape of the stalk of the derived pullback -/

section DerivedStalk

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : AlgebraicSpaces B S hS}

variable {X' : AlgebraicSpaces B S hS}

/-- **The type of the stalk formula for a derived pullback**,
`K_{g(x̄')} ⊗ᴸ_{𝒪_{X,g(x̄')}} 𝒪_{X',x̄'} ≅ (Lg^*K)_x̄'`, natural in `K ∈ D(𝒪_X)`, for a morphism
`g : X' ⟶ X` of algebraic spaces and a geometric point `x̄'` of `X'`. The derived tensor product is
the total derived extension of scalars along the stalk map `𝒪_{X,g(x̄')} ⟶ 𝒪_{X',x̄'}`.
`AlgebraicGeometry.Space.derivedPullbackGeometricStalkIso` is a term of this type. -/
abbrev DerivedPullbackGeometricStalkIsoType (g : X' ⟶ X) (x' : GeometricPoint B S hS X'.1) :
    Type _ :=
  geometricDerivedStalk B S hS (geometricPointMap g.hom x') ⋙
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (stalkStructureMap B S hS g x').hom).functor ≅
    smallEtaleDerivedModulePullback B S hS g ⋙ geometricDerivedStalk B S hS x'

/-- **The statement that a derived pullback is computed at a stalk by derived base change.** For
a morphism `g : X' ⟶ X` of algebraic spaces, a geometric point `x̄'` of `X'` and a complex `P` of
`𝒪_X`-modules at whose stalk complex `P_{g(x̄')}` the comparison of derived with degreewise
extension of scalars along `𝒪_{X,g(x̄')} ⟶ 𝒪_{X',x̄'}` is invertible, the stalk at `x̄'` of the
comparison `Lg^*P ⟶ g^*P` of Stacks 06YY is invertible.

It follows from the stalk formula for derived pullbacks: by
`AlgebraicGeometry.Space.derivedPullbackGeometricStalkMap_fac`,
`derivedPullbackGeometricStalkMap g x'` (an isomorphism) followed by the stalk of `Lg^*P ⟶ g^*P`
is the comparison of extensions of scalars between two isomorphisms
(`AlgebraicGeometry.Space.derivedPullbackGeometricStalkComplexMap`). -/
def DerivedPullbackStalkComparisonStatement : Prop :=
  ∀ {X' X : AlgebraicSpaces B S hS} (g : X' ⟶ X) (x' : GeometricPoint B S hS X'.1)
    (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ),
    IsIso ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (stalkStructureMap B S hS g x').hom).comparison.app
      (((Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS X.1 (geometricPointMap g.hom x') X.2)
        (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) →
    IsIso ((geometricDerivedStalk B S hS x').map
      ((smallEtaleDerivedModulePullbackComparison B S hS g).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)))

end DerivedStalk

end AlgebraicGeometry.Space

end
