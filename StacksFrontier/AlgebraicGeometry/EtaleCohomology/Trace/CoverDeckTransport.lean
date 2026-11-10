module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoverDeckRegularDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapCohomologyIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportExt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoverDeckWeil

/-!
# The deck transformations of a Galois cover act on `j_!(f_* A)` as multiplication in `A[H]`

For a Galois covering `G : V ⟶ U` with group `H` and a smooth compactification `V̄` of the cover,
the complex `f_* j^{-1} A_{V̄}` in degree zero, with the action of `g ∈ H` of Step 8 of the proof
of [Stacks, Tag 03UG] (`Stacks.EtaleCohomology.openDeck`), is isomorphic to the restriction of
scalars along `A ⟶ A[H]` of the descent sheaf of `A[H]` in degree zero, with the action of
multiplication by `g⁻¹` (`Stacks.EtaleCohomology.etaleModuleRestrictScalarsComplexEndo` of
`Stacks.Trace.groupElementAction`).

## Main results

* `Stacks.EtaleCohomology.coverDescentComplexIso` and
  `Stacks.EtaleCohomology.openDeck_comp_coverDescentComplexIso_hom`.
* `Stacks.EtaleCohomology.twistComp_naturality`: twists of bounded below complexes are natural
  along isomorphisms intertwining endomorphisms.
* `Stacks.EtaleCohomology.perfectDerivedTrace_groupElementAction_regularDescent_eq_zero`: for
  `A = ℤ/ℓⁿ` the twisted Frobenius trace with multiplication by `g⁻¹` on
  `RΓ(Y_k̄, j_!((D(A[H])|_A)[0]))` vanishes, granted perfectness.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Steps 7 and 8.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius CategoryTheory.FilteredDerived

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

namespace Stacks.EtaleCohomology

section Generic

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]

/-- The endomorphism of `F(X)[0]` induced by a natural endomorphism `θ` of `F` is `θ_X[0]`. -/
lemma homMk_mapHomologicalComplex_app_single_comp_mapCochainComplexPlusSinglePlusIso_hom
    (F : A ⥤ B) [F.PreservesZeroMorphisms] (θ : F ⟶ F) (X : A) :
    ObjectProperty.homMk
        (X := F.mapCochainComplexPlus.obj ((Stacks.DerivedIndexing.singlePlusFunctor A 0).obj X))
        (Y := F.mapCochainComplexPlus.obj ((Stacks.DerivedIndexing.singlePlusFunctor A 0).obj X))
        ((NatTrans.mapHomologicalComplex θ (ComplexShape.up ℤ)).app
          ((Stacks.DerivedIndexing.singlePlusFunctor A 0).obj X).obj) ≫
      (mapCochainComplexPlusSinglePlusIso F X).hom =
    (mapCochainComplexPlusSinglePlusIso F X).hom ≫
      (Stacks.DerivedIndexing.singlePlusFunctor B 0).map (θ.app X) := by
  refine ObjectProperty.hom_ext _ (HomologicalComplex.hom_ext _ _ fun n => ?_)
  by_cases hn : n = 0
  · subst hn
    change θ.app _ ≫
        ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app X).f 0 =
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app X).f 0 ≫
        ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).map (θ.app X)).f 0
    rw [HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.single_map_f_self, ← θ.naturality_assoc]
    simp
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn).eq_of_tgt _ _

/-- A twist of bounded below complexes induced by `θ : F ⟶ F ⋙ P`, followed by `P ∘ F` of an
endomorphism, is natural along isomorphisms intertwining the endomorphisms. -/
lemma twistComp_naturality (F : A ⥤ B) (P : B ⥤ B) [F.PreservesZeroMorphisms]
    [P.PreservesZeroMorphisms] (θ : F ⟶ F ⋙ P) {K L : CochainComplex.Plus A} (e : K ≅ L)
    (δK : K ⟶ K) (δL : L ⟶ L) (h : δK ≫ e.hom = e.hom ≫ δL) :
    (ObjectProperty.homMk (X := F.mapCochainComplexPlus.obj K)
        (Y := P.mapCochainComplexPlus.obj (F.mapCochainComplexPlus.obj K))
        ((NatTrans.mapHomologicalComplex θ (ComplexShape.up ℤ)).app K.obj) ≫
      P.mapCochainComplexPlus.map (F.mapCochainComplexPlus.map δK)) ≫
      P.mapCochainComplexPlus.map (F.mapCochainComplexPlus.map e.hom) =
    F.mapCochainComplexPlus.map e.hom ≫
      (ObjectProperty.homMk (X := F.mapCochainComplexPlus.obj L)
        (Y := P.mapCochainComplexPlus.obj (F.mapCochainComplexPlus.obj L))
        ((NatTrans.mapHomologicalComplex θ (ComplexShape.up ℤ)).app L.obj) ≫
      P.mapCochainComplexPlus.map (F.mapCochainComplexPlus.map δL)) := by
  rw [Category.assoc, ← Functor.map_comp, ← Functor.map_comp, h, Functor.map_comp,
    Functor.map_comp, ← Category.assoc, homMk_mapHomologicalComplex_app_naturality, Category.assoc]

end Generic

section Transport

variable {k : Type u} [Field k] [Fintype k] [PerfectField k] {U : Scheme.{u}} {H : Type} [Group H]
  [Fintype H] {pU : U ⟶ Spec (.of k)} [IsCurve k pU] [Smooth pU] (Y : Over (Spec (.of k)))
  [IsProper Y.hom] {jU : U ⟶ Y.left} [IsOpenImmersion jU] (hjU : jU ≫ Y.hom = pU)
  (G : EtaleGaloisCovering U H) [IsFinite (G.cover.hom : G.cover.left ⟶ U)]
  [hconn : ConnectedSpace G.cover.left]
  [ConnectedSpace ((𝟭 Scheme).obj G.cover.left)]
  (C : CoverCompactification k Y.hom jU (G.cover.hom : G.cover.left ⟶ U)) (g : H) (A : Type)
  [CommRing A]

/-- The action of `g ∈ H` on the covering, as an automorphism. -/
@[simps]
def coverActIso : G.cover.left ≅ G.cover.left where
  hom := G.act g
  inv := G.act g⁻¹
  hom_inv_id := by rw [← G.act_mul, inv_mul_cancel, G.act_one]
  inv_hom_id := by rw [← G.act_mul, mul_inv_cancel, G.act_one]

include hjU in
/-- The extension to `V̄` of the action of `g ∈ H` is an integral morphism. -/
instance isIntegralHom_extendOver_actIso :
    IsIntegralHom (C.extendOver hjU (coverActIso G g) (G.act_comp_hom g)).left :=
  haveI : IsIso (C.extendOver hjU (coverActIso G g) (G.act_comp_hom g)).left :=
    inferInstanceAs (IsIso (C.extendIso pU hjU (coverActIso G g) (G.act_comp_hom g)).hom)
  inferInstance

/-- The composite functor `M ↦ f_* j^{-1} M_{V̄}`. -/
abbrev coverConstantFunctor : ModuleCat.{u + 1} A ⥤ EtaleModules.{u, 0} A U :=
  constantSheaf C.toOver.left.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
    etaleModuleRestriction.{u, 0} A (C.j : G.cover.left ⟶ C.toOver.left) ⋙
      etaleModuleDirectImage.{u, 0} A G.cover.hom

/-- **`f_* j^{-1} A_{V̄}[0] ≅ (D(A[H])|_A)[0]`** as bounded below complexes on `U`. -/
def coverDescentComplexIso :
    openComplex A (Z := C.toOver) (C.j : G.cover.left ⟶ C.toOver.left) G.cover.hom
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj (uliftCoefficientModule.{u} A)) ≅
      (etaleModuleRestrictScalars (MonoidAlgebra.singleOneRingHom (R := A) (M := H))
        U).mapCochainComplexPlus.obj
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj G.regularDescentSheaf) :=
  mapCochainComplexPlusSinglePlusIso (coverConstantFunctor Y G C A)
      (uliftCoefficientModule.{u} A) ≪≫
    (Stacks.DerivedIndexing.singlePlusFunctor _ 0).mapIso
      (coverDescentIso A G (Vb := C.toOver.left) C.j) ≪≫
    (mapCochainComplexPlusSinglePlusIso
      (etaleModuleRestrictScalars (MonoidAlgebra.singleOneRingHom (R := A) (M := H)) U)
      G.regularDescentSheaf).symm

/-- If `i₁`, `ψ` and `i₂` intertwine `d₀`, `t`, `s` and `d₂` as in `h₁`, `h₂`, `h₃`, then
`i₁.hom ≫ ψ ≫ i₂.inv` intertwines `d₀` and `d₂`. -/
private lemma transportChase {D : Type*} [Category* D] {P Q R S : D} (i₁ : P ≅ Q) (ψ : Q ⟶ R)
    (i₂ : S ≅ R) (d₀ : P ⟶ P) (t : Q ⟶ Q) (s : R ⟶ R) (d₂ : S ⟶ S)
    (h₁ : d₀ ≫ i₁.hom = i₁.hom ≫ t) (h₂ : t ≫ ψ = ψ ≫ s) (h₃ : d₂ ≫ i₂.hom = i₂.hom ≫ s) :
    d₀ ≫ i₁.hom ≫ ψ ≫ i₂.inv = (i₁.hom ≫ ψ ≫ i₂.inv) ≫ d₂ := by
  have h₄ : s ≫ i₂.inv = i₂.inv ≫ d₂ := by
    rw [Iso.comp_inv_eq, Category.assoc, h₃, Iso.inv_hom_id_assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂, h₄, Category.assoc, Category.assoc]

omit hconn [Fintype k] [PerfectField k] [IsCurve k pU] [Smooth pU] [IsOpenImmersion jU]
  [IsFinite (G.cover.hom : G.cover.left ⟶ U)] in
include hjU in
/-- **The deck transformation `g` on `f_* j^{-1} A_{V̄}[0]` is multiplication by `g⁻¹` on
`(D(A[H])|_A)[0]`**, under `Stacks.EtaleCohomology.coverDescentComplexIso`. -/
theorem openDeck_comp_coverDescentComplexIso_hom :
    openDeck A (C.extendOver hjU (coverActIso G g) (G.act_comp_hom g))
        (C.j : G.cover.left ⟶ C.toOver.left) G.cover.hom (coverActIso G g).hom (G.act_comp_hom g)
        (C.isPullback_extend pU hjU (coverActIso G g) (G.act_comp_hom g))
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj (uliftCoefficientModule.{u} A)) ≫
      (coverDescentComplexIso Y G C A).hom =
    (coverDescentComplexIso Y G C A).hom ≫
      etaleModuleRestrictScalarsComplexEndo (MonoidAlgebra.singleOneRingHom (R := A) (M := H))
        (Stacks.Trace.groupElementAction.{0, 0, u + 1} A H g)
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj G.regularDescentSheaf) := by
  have h₁ := homMk_mapHomologicalComplex_app_single_comp_mapCochainComplexPlusSinglePlusIso_hom
    (coverConstantFunctor Y G C A)
    (openDeckNatTrans A (C.extendOver hjU (coverActIso G g) (G.act_comp_hom g))
      (C.j : G.cover.left ⟶ C.toOver.left) G.cover.hom (coverActIso G g).hom (G.act_comp_hom g)
      (C.isPullback_extend pU hjU (coverActIso G g) (G.act_comp_hom g)))
    (uliftCoefficientModule.{u} A)
  have h₃ := homMk_mapHomologicalComplex_app_single_comp_mapCochainComplexPlusSinglePlusIso_hom
    (etaleModuleRestrictScalars (MonoidAlgebra.singleOneRingHom (R := A) (M := H)) U)
    (etaleModuleRestrictScalarsNatTrans (MonoidAlgebra.singleOneRingHom (R := A) (M := H))
      (Stacks.Trace.groupElementAction.{0, 0, u + 1} A H g) U) G.regularDescentSheaf
  have h₂ : (Stacks.DerivedIndexing.singlePlusFunctor _ 0).map
        ((openDeckNatTrans A (C.extendOver hjU (coverActIso G g) (G.act_comp_hom g))
          (C.j : G.cover.left ⟶ C.toOver.left) G.cover.hom (coverActIso G g).hom (G.act_comp_hom g)
          (C.isPullback_extend pU hjU (coverActIso G g) (G.act_comp_hom g))).app
            (uliftCoefficientModule.{u} A)) ≫
      (Stacks.DerivedIndexing.singlePlusFunctor _ 0).map
        (coverDescentIso A G (Vb := C.toOver.left) C.j).hom =
      (Stacks.DerivedIndexing.singlePlusFunctor _ 0).map
        (coverDescentIso A G (Vb := C.toOver.left) C.j).hom ≫
      (Stacks.DerivedIndexing.singlePlusFunctor _ 0).map
        ((etaleModuleRestrictScalarsNatTrans (MonoidAlgebra.singleOneRingHom (R := A) (M := H))
          (Stacks.Trace.groupElementAction.{0, 0, u + 1} A H g) U).app G.regularDescentSheaf) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    exact directImageTwist_comp_coverDescentIso_hom A G (Vb := C.toOver.left) C.j g
      (C.extendOver hjU (coverActIso G g) (G.act_comp_hom g)).left
      (C.isPullback_extend pU hjU (coverActIso G g) (G.act_comp_hom g))
  exact transportChase _ _ _ _ _ _ _ h₁ h₂ h₃


variable (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ)
  [Fact p.Prime] [CharP k p] [CharP kbar p] (hcard : Fintype.card k = p ^ q)

omit hconn [Fintype H] [IsCurve k pU] [Smooth pU] [IsFinite (G.cover.hom : G.cover.left ⟶ U)] in
include hjU in
/-- For `A = ℤ/ℓⁿ`, granted perfectness, the twisted Frobenius trace with multiplication by
`g⁻¹` on `RΓ(Y_k̄, j_!((D(A[H])|_A)[0]))` vanishes. -/
theorem perfectDerivedTrace_groupElementAction_regularDescent_eq_zero
    [Finite H] [Algebra.IsAlgebraic k kbar] (ℓ n : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0) (hn : 1 ≤ n)
    [IsEmpty (rationalPoints pU)]
    (hY : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      ((etaleModuleGlobalSections.{u, 0} (ZMod (ℓ ^ n))
          (Spec (.of kbar))).rightDerivedFunctorPlus.obj
        ((etaleModuleDirectImage.{u, 0} (ZMod (ℓ ^ n))
            (pullback.snd Y.hom (specAlgebraMap k kbar))).rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Q.obj
            ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ n))
                (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
              ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ n)) jU).mapCochainComplexPlus.obj
                ((etaleModuleRestrictScalars
                    (MonoidAlgebra.singleOneRingHom (R := ZMod (ℓ ^ n)) (M := H))
                    U).mapCochainComplexPlus.obj
                  ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
                    G.regularDescentSheaf)))))))))
    (hZ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      ((etaleModuleGlobalSections.{u, 0} (ZMod (ℓ ^ n))
          (Spec (.of kbar))).rightDerivedFunctorPlus.obj
        ((etaleModuleDirectImage.{u, 0} (ZMod (ℓ ^ n))
          (pullback.snd C.toOver.hom (specAlgebraMap k kbar))).rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Q.obj
            ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ n))
                (fieldBaseChangeProj C.toOver kbar)).mapCochainComplexPlus.obj
              (extensionByZeroConstantComplex (ZMod (ℓ ^ n)) C.toOver C.j
                (zmodSingleComplex.{u} ℓ n))))))))
    (hp₂ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2}
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, 0} (ZMod (ℓ ^ n))
        (pullback.snd C.toOver.hom (specAlgebraMap k kbar))
        (etaleModuleConstantComplex (ZMod (ℓ ^ n)) kbar (zmodSingleComplex.{u} ℓ n)))))
    (hp₃ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2}
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, 0} (ZMod (ℓ ^ n))
        (pullback.snd C.boundaryOver.hom (specAlgebraMap k kbar))
        (etaleModuleConstantComplex (ZMod (ℓ ^ n)) kbar (zmodSingleComplex.{u} ℓ n)))))
    (hΓ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2}
      (DerivedCategory.Q.obj (baseSectionsComplex (ZMod (ℓ ^ n))
        (etaleModuleConstantComplex (ZMod (ℓ ^ n)) kbar (zmodSingleComplex.{u} ℓ n)).obj))) :
    perfectDerivedTrace (ZMod (ℓ ^ n)) ⟨_, hY⟩ (DerivedCategory.Plus.ι.map (Functor.derivedTwistEndo
        (etaleModuleDirectImage.{u, 0} (ZMod (ℓ ^ n))
          (geometricFrobeniusBaseChange Y kbar p q hcard))
        (etaleModuleDirectImage.{u, 0} (ZMod (ℓ ^ n)) (pullback.snd Y.hom (specAlgebraMap k kbar)))
        (etaleModuleGlobalSections.{u, 0} (ZMod (ℓ ^ n)) (Spec (.of kbar)))
        (etaleModuleDirectImageComp.{u, 0} (ZMod (ℓ ^ n))
          (geometricFrobeniusBaseChange Y kbar p q hcard)
          (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Y.hom (specAlgebraMap k kbar))
          (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard).symm)
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ n))
            (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ n)) jU).mapCochainComplexPlus.obj
            ((etaleModuleRestrictScalars
                (MonoidAlgebra.singleOneRingHom (R := ZMod (ℓ ^ n)) (M := H))
                U).mapCochainComplexPlus.obj
              ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj G.regularDescentSheaf))))
        (ObjectProperty.homMk
          (X := (etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ n))
              (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
            ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ n)) jU).mapCochainComplexPlus.obj
              ((etaleModuleRestrictScalars
                  (MonoidAlgebra.singleOneRingHom (R := ZMod (ℓ ^ n)) (M := H))
                  U).mapCochainComplexPlus.obj
                ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj G.regularDescentSheaf))))
          (Y := (etaleModuleDirectImage.{u, 0} (ZMod (ℓ ^ n))
            (geometricFrobeniusBaseChange Y kbar p q hcard)).mapCochainComplexPlus.obj
            ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ n))
                (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
              ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ n)) jU).mapCochainComplexPlus.obj
                ((etaleModuleRestrictScalars
                    (MonoidAlgebra.singleOneRingHom (R := ZMod (ℓ ^ n)) (M := H))
                    U).mapCochainComplexPlus.obj
                  ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj G.regularDescentSheaf)))))
          ((NatTrans.mapHomologicalComplex
            (frobeniusBaseChangeTwist.{u, 0} (ZMod (ℓ ^ n)) Y kbar p q hcard)
            (ComplexShape.up ℤ)).app
              ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ n)) jU).mapCochainComplexPlus.obj
                ((etaleModuleRestrictScalars
                    (MonoidAlgebra.singleOneRingHom (R := ZMod (ℓ ^ n)) (M := H))
                    U).mapCochainComplexPlus.obj
                  ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
                    G.regularDescentSheaf))).obj) ≫
          (etaleModuleDirectImage.{u, 0} (ZMod (ℓ ^ n))
              (geometricFrobeniusBaseChange Y kbar p q hcard)).mapCochainComplexPlus.map
            ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ n))
                (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.map
              ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ n)) jU).mapCochainComplexPlus.map
                (etaleModuleRestrictScalarsComplexEndo
                  (MonoidAlgebra.singleOneRingHom (R := ZMod (ℓ ^ n)) (M := H))
                  (Stacks.Trace.groupElementAction.{0, 0, u + 1} (ZMod (ℓ ^ n)) H g)
                  ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
                    G.regularDescentSheaf))))))) = 0 := by
  have := Fintype.ofFinite H
  have : Etale (G.cover.hom : G.cover.left ⟶ U) := G.cover.prop
  let e := (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ n)) jU).mapCochainComplexPlus.mapIso
    (coverDescentComplexIso Y G C (ZMod (ℓ ^ n)))
  have hδ := congrArg
    (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ n)) jU).mapCochainComplexPlus.map
    (openDeck_comp_coverDescentComplexIso_hom Y hjU G C g (ZMod (ℓ ^ n)))
  simp only [Functor.map_comp] at hδ
  have hτ := twistComp_naturality
    (etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ n)) (fieldBaseChangeProj Y kbar))
    (etaleModuleDirectImage.{u, 0} (ZMod (ℓ ^ n)) (geometricFrobeniusBaseChange Y kbar p q hcard))
    (frobeniusBaseChangeTwist.{u, 0} (ZMod (ℓ ^ n)) Y kbar p q hcard) e _ _ hδ
  have hY₀ := (Functor.isPerfect_iff_of_iso (DerivedCategory.Plus.ι.mapIso
    ((etaleModuleGlobalSections.{u, 0} (ZMod (ℓ ^ n))
        (Spec (.of kbar))).rightDerivedFunctorPlus.mapIso
      ((etaleModuleDirectImage.{u, 0} (ZMod (ℓ ^ n))
        (pullback.snd Y.hom (specAlgebraMap k kbar))).rightDerivedFunctorPlus.mapIso
        (DerivedCategory.Plus.Q.mapIso ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ n))
          (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.mapIso e)))))).2 hY
  rw [← Functor.perfectDerivedTrace_derivedTwistEndo_eq_of_iso.{0, u + 1, u + 2, u + 1} _ _ _ _
    ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ n))
      (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.mapIso e)
    _ _ hτ hY₀ hY]
  exact perfectDerivedTrace_openDeck_coverCompactification_eq_zero_of_zmod Y hjU C (coverActIso G g)
    (G.act_comp_hom g) kbar p q hcard ℓ n hℓ hn hY₀ hZ hp₂ hp₃ hΓ

end Transport

end Stacks.EtaleCohomology
