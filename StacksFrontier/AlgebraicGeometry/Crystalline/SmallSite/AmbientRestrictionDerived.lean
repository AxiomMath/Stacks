module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.DerivedGlobalSections
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Formula07MK

/-!
# Restricting crystalline cohomology classes to an object of `Cris(X/S)`

Fix a global crystalline situation `(p, (S, I, γ), X)` and an object `A = (U, T, δ)` of the small
crystalline site `Cris(X/S)`.  A global section of an abelian sheaf `G` on `Cris(X/S)` has a value
at every restriction `(U ∩ W, W, δ|_W)` of `A` to an open `W` of `T`, compatibly with the
restrictions, so it is a global section of the restriction `G_T` of `G` to the Zariski site of
`T`.  This gives a natural transformation

`Γ(Cris(X/S), G) ⟶ Γ(T, G_T)`

and, deriving it, the natural map of bounded below derived categories

`RΓ(Cris(X/S), K) ⟶ RΓ(T, K_T)`

which restricts global cohomology classes to `T`; here `K ↦ K_T` is the restriction applied
termwise to a complex, which computes its own derived functor because restriction to `T` is exact.
This is the middle step of the construction of [Stacks, Equation 07LP]: "we can restrict global
cohomology classes to `T`".

## Main definitions

Everything below lives in the namespace
`Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening`.

* `ambientGlobalSections` and `derivedAmbientGlobalSectionsFunctor` — `Γ(T, -)` and
  `RΓ(T, -) : D⁺(Ab(T_Zar)) ⥤ D⁺(Ab)` for the ambient scheme `T` of an object.
* `derivedAmbientRestriction` — `K ↦ K_T : D⁺(Ab(Cris(X/S))) ⥤ D⁺(Ab(T_Zar))`, the action of the
  exact restriction functor `G ↦ G_T` on bounded below derived categories.
* `globalSectionsToAmbient` — the natural transformation `Γ(Cris(X/S), G) ⟶ Γ(T, G_T)`.
* `derivedGlobalSectionsToAmbient` — its derived form `RΓ(Cris(X/S), K) ⟶ RΓ(T, K_T)`.

## Main results

* `globalSectionsToAmbient_app_comp` — the restriction of a global section to `T`, followed by
  the identification of `Γ(T, G_T)` with the sections of `G` over `A`, is the value of the global
  section at `A`.
* `derivedGlobalSectionsToAmbient_fac` — on a bounded below complex `K` of abelian sheaves, the
  derived map composed with the canonical map `Γ(Cris(X/S), K) ⟶ RΓ(Cris(X/S), K)` is the
  termwise restriction `Γ(Cris(X/S), K) ⟶ Γ(T, K_T)` followed by `Γ(T, K_T) ⟶ RΓ(T, K_T)`; this
  characterises the derived map uniquely, `RΓ(Cris(X/S), -)` being a right derived functor.
* `derivedGlobalSectionsToAmbient_naturality` — the derived map is natural in `K`.

## References

* [Stacks Project, Tag 07LP](https://stacks.math.columbia.edu/tag/07LP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe w w' w'' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

namespace CrystallineThickening

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {S : GlobalCrystallineSituation.{u}} (A : CrystallineThickening S)

/-! ### Global sections on the ambient scheme -/

/-- **The global sections `Γ(T, -)` of abelian sheaves on the Zariski site of the ambient scheme
`T` of an object of `Cris(X/S)`**, at the coefficient universe of the crystalline side. -/
abbrev ambientGlobalSections :
    Sheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme) AddCommGrpCat.{u + 1} ⥤
      AddCommGrpCat.{u + 1} :=
  Sheaf.Γ (Opens.grothendieckTopology A.obj.thickening.target.scheme) AddCommGrpCat.{u + 1}

/-- Global sections on the ambient scheme are additive, being a right adjoint. -/
instance additive_ambientGlobalSections : (ambientGlobalSections A).Additive :=
  Stacks.Cohomology.GlobalSections.additive_Γ.{u + 1, u, u}
    (Opens.grothendieckTopology A.obj.thickening.target.scheme)

/-- The comparison of limits underlying `globalSectionsToAmbient`: the limit of the presheaf of
an abelian sheaf `G` on `Cris(X/S)` maps, by `limit.pre`, to the limit of its precomposition with
the restrictions of `A` to the opens of `T`, which is the presheaf of `G_T`. -/
def limitToAmbient :
    sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1} ⋙ lim ⟶
      abelianAmbientRestriction A ⋙
        sheafToPresheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme)
          AddCommGrpCat.{u + 1} ⋙ lim where
  app G := limit.pre G.obj (restrictOpenFunctor A).op
  naturality _ _ φ := limit.map_pre φ.hom (restrictOpenFunctor A).op

/-- **The natural transformation `Γ(Cris(X/S), G) ⟶ Γ(T, G_T)`.**  Both global sections functors
are limits of the underlying presheaves, and the presheaf of `G_T` is `G` precomposed with the
restrictions of `A` to the opens of `T`; the map is the comparison `limit.pre` of the two limits,
which sends a compatible family of sections of `G` to its values at the restrictions of `A`. -/
def globalSectionsToAmbient :
    globalSections S ⟶ abelianAmbientRestriction A ⋙ ambientGlobalSections A :=
  (Sheaf.ΓNatIsoLim (smallTopology S) AddCommGrpCat.{u + 1}).hom ≫ limitToAmbient A ≫
    Functor.whiskerLeft (abelianAmbientRestriction A)
      (Sheaf.ΓNatIsoLim (Opens.grothendieckTopology A.obj.thickening.target.scheme)
        AddCommGrpCat.{u + 1}).inv

/-- **The restriction of a global section to `T` is its value at `A`.**  Reading `Γ(T, G_T)` as a
limit, its projection to the open `T` itself is the sections of `G_T` over `T`, which are the
sections of `G` over the restriction `A|_T`; the composite with `globalSectionsToAmbient` is the
projection of `Γ(Cris(X/S), G)` to `A|_T`. -/
theorem globalSectionsToAmbient_app_comp (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (W : A.obj.thickening.target.scheme.Opens) :
    (globalSectionsToAmbient A).app G ≫
        (Sheaf.ΓNatIsoLim (Opens.grothendieckTopology A.obj.thickening.target.scheme)
          AddCommGrpCat.{u + 1}).hom.app ((abelianAmbientRestriction A).obj G) ≫
        limit.π _ (op W) =
      (Sheaf.ΓNatIsoLim (smallTopology S) AddCommGrpCat.{u + 1}).hom.app G ≫
        limit.π G.obj (op (A.restrictOpen W)) := by
  simp only [globalSectionsToAmbient, NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  exact congrArg (_ ≫ ·) (limit.pre_π G.obj (restrictOpenFunctor A).op (op W))

/-! ### The derived restriction -/

section Derived

variable [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'}
    (Sheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]

/-- **`K ↦ K_T` on bounded below derived categories.**  Restriction to the ambient scheme `T` of
an object is exact, so it acts on derived categories termwise,
`CategoryTheory.Functor.mapDerivedCategoryPlus`. -/
def derivedAmbientRestriction :
    DerivedCategory.Plus (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus
        (Sheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme)
          AddCommGrpCat.{u + 1}) :=
  (abelianAmbientRestriction A).mapDerivedCategoryPlus

/-- `K ↦ K_T` on derived categories is induced by the termwise restriction of complexes. -/
def derivedAmbientRestrictionFactorsh :
    DerivedCategory.Plus.Qh ⋙ derivedAmbientRestriction A ≅
      (abelianAmbientRestriction A).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh :=
  (abelianAmbientRestriction A).mapDerivedCategoryPlusFactorsh

/-- **The derived global sections `RΓ(T, -) : D⁺(Ab(T_Zar)) ⥤ D⁺(Ab)`** on the Zariski site of the
ambient scheme `T` of an object of `Cris(X/S)`. -/
def derivedAmbientGlobalSectionsFunctor :
    DerivedCategory.Plus
        (Sheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme)
          AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus AddCommGrpCat.{u + 1} :=
  (ambientGlobalSections A).rightDerivedFunctorPlus

/-- The termwise comparison out of which `derivedGlobalSectionsToAmbient` is derived: on the
image of a bounded below complex `K`, it is the termwise restriction
`Γ(Cris(X/S), K) ⟶ Γ(T, K_T)`, then the canonical map `Γ(T, K_T) ⟶ RΓ(T, K_T)`, then the
identification of `K_T` with the restriction of `K` in the derived category. -/
def globalSectionsToAmbientComparison :
    (globalSections S).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ derivedAmbientRestriction A ⋙
        derivedAmbientGlobalSectionsFunctor A :=
  Functor.whiskerRight
      (Functor.mapHomotopyCategoryPlusNatTrans (globalSectionsToAmbient A))
      DerivedCategory.Plus.Qh ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl _)).inv DerivedCategory.Plus.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (abelianAmbientRestriction A).mapHomotopyCategoryPlus
      (ambientGlobalSections A).rightDerivedFunctorPlusUnith ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (derivedAmbientRestrictionFactorsh A).inv
      (derivedAmbientGlobalSectionsFunctor A) ≫
    (Functor.associator _ _ _).hom

/-- **The restriction of global cohomology classes to `T`, `RΓ(Cris(X/S), K) ⟶ RΓ(T, K_T)`**,
natural in the bounded below complex `K` of abelian sheaves on `Cris(X/S)`.  It is the derived
functor of the natural transformation `Γ(Cris(X/S), G) ⟶ Γ(T, G_T)` of `globalSectionsToAmbient`:
the unique natural transformation out of the right derived functor `RΓ(Cris(X/S), -)` restricting
to `globalSectionsToAmbientComparison` on complexes, by `derivedGlobalSectionsToAmbient_fac`. -/
def derivedGlobalSectionsToAmbient :
    derivedGlobalSectionsFunctor S ⟶
      derivedAmbientRestriction A ⋙ derivedAmbientGlobalSectionsFunctor A :=
  (globalSections S).rightDerivedFunctorPlus.rightDerivedDesc
    (globalSections S).rightDerivedFunctorPlusUnith (HomotopyCategory.Plus.quasiIso _) _
    (globalSectionsToAmbientComparison A)

/-- **The derived restriction to `T` is the derived functor of the termwise restriction**: its
composite with the canonical map `Γ(Cris(X/S), K) ⟶ RΓ(Cris(X/S), K)` is
`globalSectionsToAmbientComparison`. -/
@[reassoc]
theorem derivedGlobalSectionsToAmbient_fac :
    (globalSections S).rightDerivedFunctorPlusUnith ≫
        Functor.whiskerLeft DerivedCategory.Plus.Qh (derivedGlobalSectionsToAmbient A) =
      globalSectionsToAmbientComparison A :=
  Functor.rightDerived_fac _ _ _ _ _

/-- `derivedGlobalSectionsToAmbient_fac` at a single bounded below complex. -/
@[reassoc]
theorem derivedGlobalSectionsToAmbient_fac_app (K : HomotopyCategory.Plus
    (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})) :
    (globalSections S).rightDerivedFunctorPlusUnith.app K ≫
        (derivedGlobalSectionsToAmbient A).app (DerivedCategory.Plus.Qh.obj K) =
      (globalSectionsToAmbientComparison A).app K :=
  NatTrans.congr_app (derivedGlobalSectionsToAmbient_fac A) K

/-- **The derived restriction to `T` is unique**: a natural transformation out of
`RΓ(Cris(X/S), -)` which restricts to `globalSectionsToAmbientComparison` on complexes is
`derivedGlobalSectionsToAmbient`. -/
theorem derivedGlobalSectionsToAmbient_unique
    (τ : derivedGlobalSectionsFunctor S ⟶
      derivedAmbientRestriction A ⋙ derivedAmbientGlobalSectionsFunctor A)
    (hτ : (globalSections S).rightDerivedFunctorPlusUnith ≫
        Functor.whiskerLeft DerivedCategory.Plus.Qh τ = globalSectionsToAmbientComparison A) :
    τ = derivedGlobalSectionsToAmbient A :=
  Functor.rightDerived_ext _ (globalSections S).rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso _) _ _ _
    (hτ.trans (derivedGlobalSectionsToAmbient_fac A).symm)

/-- **The derived restriction to `T` is natural in the complex.** -/
@[reassoc]
theorem derivedGlobalSectionsToAmbient_naturality
    {K L : DerivedCategory.Plus (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})} (φ : K ⟶ L) :
    (derivedGlobalSectionsFunctor S).map φ ≫ (derivedGlobalSectionsToAmbient A).app L =
      (derivedGlobalSectionsToAmbient A).app K ≫
        (derivedAmbientGlobalSectionsFunctor A).map ((derivedAmbientRestriction A).map φ) :=
  (derivedGlobalSectionsToAmbient A).naturality φ

end Derived

end CrystallineThickening

end Crystalline.GlobalCrystallineSituation.SmallSite

end
