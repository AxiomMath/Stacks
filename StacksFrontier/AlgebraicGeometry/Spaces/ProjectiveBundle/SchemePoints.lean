module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.SectionsEquivBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.RelativeProjBaseChangeTwist.BaseChangeCongr
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.RelativeProjCongrFunctorial
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.FunctorOfPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.InvertibleQuotientBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SymmetricAlgebraPointPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.PointComparisonModule
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.ZariskiReadingSymmetricAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiReadingInvertibleQuotients
public import StacksFrontier.AlgebraicGeometry.SymAlgebraQcohPieces.Basic

/-!
# The points of the projective bundle of an algebraic space over a scheme point

Let `X` be an algebraic space over a scheme `S`, `ℰ` a quasi-coherent `𝒪_X`-module and
`π : 𝐏(ℰ) ⟶ X` its projective bundle.  For a scheme point `g : T ⟶ X`, the points of `𝐏(ℰ)` over
`g` are in bijection with the isomorphism classes of invertible quotients of `g^*ℰ`, naturally in
`T`.  This is the universal property of the projective bundle (Stacks 01O4) at scheme points.

The bijection is the composite of: the identification of the points over `g` with the sections
of `Proj_T(g^*Sym ℰ) ⟶ T` (Stacks 084B); the isomorphism of that relative Proj with the projective
bundle of the Zariski reading of `g^*ℰ`, through `g^*Sym(ℰ) ≅ Sym(g^*ℰ)`; the bijection of
Stacks 0B3V on the scheme `T`; and the dictionary between invertible quotients of a
quasi-coherent module on the scheme of `T` and on the small étale site of `T`.

## Main definitions

* `AlgebraicGeometry.Space.pointProjIso`: `Proj_T(g^*Sym ℰ) ≅ 𝐏((g^*ℰ)_Zar)` over `T`.
* `AlgebraicGeometry.Space.pointsEquivInvertibleQuotientClass`: the bijection.

## Main results

* `AlgebraicGeometry.Space.pointsEquivInvertibleQuotientClass_natural`: its naturality in `T`.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 0B4I](https://stacks.math.columbia.edu/tag/0B4I)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (X : AlgebraicSpaces B S hS)
  (E : SheafOfModules.{u} (structureRingSheaf B S hS X)) (hE : E.IsQuasicoherentOnSite)
  (hb : SymmetricAlgebraBounded X E)

/-- The Zariski reading `(g^*ℰ)_Zar` of the pullback of `ℰ` to a scheme point `g`. -/
abbrev pointZariskiModule (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ X.1) :
    ((BigFppfOver.toScheme B S hS).obj T).Modules :=
  (zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom g)).obj E)

include hE in
/-- The pullback `g^*ℰ` of a quasi-coherent module to a scheme point is quasi-coherent. -/
theorem isQuasicoherentOnSite_pointPullback (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ X.1) :
    ((modulePullback B S hS (pointHom g)).obj E).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom g) _ hE

include hE in
/-- The Zariski reading `(g^*ℰ)_Zar` is a quasi-coherent module on the scheme of the point. -/
theorem isQuasicoherent_pointZariskiModule (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ X.1) :
    (pointZariskiModule X E T g).IsQuasicoherent :=
  isQuasicoherent_zariskiReading_piece T _ (isQuasicoherentOnSite_pointPullback X E hE T g)

/-- `Sym((g^*ℰ)_Zar)`, as graded algebra data on the scheme of a point. -/
abbrev pointSymmetricAlgebra (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ X.1) :
    SheafGradedAlgebra ((BigFppfOver.toScheme B S hS).obj T) :=
  haveI := isQuasicoherent_pointZariskiModule X E hE T g
  Stacks.SymGraded.schemeSheafGradedAlgebra (pointZariskiModule X E T g)
    (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent _)

/-- The relative Proj situation of `Sym(ℱ)` read as a `SheafGradedAlgebra` is the projective
bundle situation of `ℱ`. -/
theorem situation_schemeSheafGradedAlgebra {Y : Scheme.{u}} (F : Y.Modules) [F.IsQuasicoherent] :
    Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.situation
      (Stacks.SymGraded.schemeSheafGradedAlgebra F
        (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F)) =
      Stacks.RelativeProj.symmetricSituationOfQuasicoherent Y F := rfl

/-- `Sym(ℱ)` read as the graded algebra of its `SheafGradedAlgebra` is `Sym(ℱ)`. -/
def situationAlgebraSymmetricHom {Y : Scheme.{u}} (F : Y.Modules) [F.IsQuasicoherent] :
    SheafOfModules.GradedAlgebra.UnitalHom
      (situationAlgebra (Stacks.SymGraded.schemeSheafGradedAlgebra F
        (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F)))
      (Scheme.Modules.symmetricAlgebra Y F) where
  app _ := 𝟙 _
  map_mul _ _ _ _ _ := rfl
  map_one _ := rfl

/-- The identification `situationAlgebraSymmetricHom` is an isomorphism in every degree. -/
instance isIso_situationAlgebraSymmetricHom_app {Y : Scheme.{u}} (F : Y.Modules)
    [F.IsQuasicoherent] (n : ℤ) : IsIso ((situationAlgebraSymmetricHom F).app n) :=
  inferInstanceAs (IsIso (𝟙 _))

/-- An isomorphism of sheaves of graded algebras is an isomorphism in every degree. -/
instance _root_.SheafOfModules.GradedAlgebra.isIso_hom_app_of_iso {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat} {A₁ A₂ : SheafOfModules.GradedAlgebra R}
    (e : A₁ ≅ A₂) (n : ℤ) : IsIso (e.hom.app n) :=
  ⟨e.inv.app n, congrArg (fun f => SheafOfModules.GradedAlgebra.Hom.app f n) e.hom_inv_id,
    congrArg (fun f => SheafOfModules.GradedAlgebra.Hom.app f n) e.inv_hom_id⟩

/-- A composite of unital homomorphisms is invertible in a degree where both factors are. -/
theorem _root_.SheafOfModules.GradedAlgebra.UnitalHom.isIso_comp_app_of_isIso {C : Type*}
    [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat}
    {A₁ A₂ A₃ : SheafOfModules.GradedAlgebra R} (f : SheafOfModules.GradedAlgebra.UnitalHom A₁ A₂)
    (g : SheafOfModules.GradedAlgebra.UnitalHom A₂ A₃) (n : ℤ) (hf : IsIso (f.app n))
    (hg : IsIso (g.app n)) : IsIso ((f.comp g).app n) := by
  rw [SheafOfModules.GradedAlgebra.UnitalHom.comp_app]
  exact IsIso.comp_isIso

/-- An isomorphism of sheaves of graded algebras, as a unital homomorphism. -/
def _root_.SheafOfModules.GradedAlgebra.UnitalHom.ofIso {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat} {A₁ A₂ : SheafOfModules.GradedAlgebra R}
    (e : A₁ ≅ A₂) : SheafOfModules.GradedAlgebra.UnitalHom A₁ A₂ :=
  @SheafOfModules.GradedAlgebra.UnitalHom.ofHomOfIsIso _ _ _ _ _ _ e.hom
    (SheafOfModules.GradedAlgebra.isIso_hom_app_of_iso e 0)

/-- The components of `UnitalHom.ofIso e` are those of `e`. -/
@[simp] theorem _root_.SheafOfModules.GradedAlgebra.UnitalHom.ofIso_app {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat} {A₁ A₂ : SheafOfModules.GradedAlgebra R}
    (e : A₁ ≅ A₂) (n : ℤ) : (SheafOfModules.GradedAlgebra.UnitalHom.ofIso e).app n = e.hom.app n :=
  rfl

/-- The unital homomorphism of an isomorphism is an isomorphism in every degree. -/
instance _root_.SheafOfModules.GradedAlgebra.UnitalHom.isIso_ofIso_app {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat} {A₁ A₂ : SheafOfModules.GradedAlgebra R}
    (e : A₁ ≅ A₂) (n : ℤ) : IsIso ((SheafOfModules.GradedAlgebra.UnitalHom.ofIso e).app n) :=
  SheafOfModules.GradedAlgebra.isIso_hom_app_of_iso e n

/-- The restricted algebra of Situation 0849 at a point, read as the graded algebra of its
`SheafGradedAlgebra`, is the Zariski reading of the pullback. -/
def pointAlgebraSituationHom (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ X.1) :
    SheafOfModules.GradedAlgebra.UnitalHom (R := ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf)
      (zariskiReading T (etalePointAlgebra (symmetricAlgebra B S hS X E) T g))
      (situationAlgebra ((projectiveBundleSituation X E hE hb).pointAlgebra T g)) :=
  SheafOfModules.GradedAlgebra.UnitalHom.ofIso
    (eqToIso (RelativeProjSituation.situationAlgebra_pointAlgebra
      (t := projectiveBundleSituation X E hE hb) T g).symm)

/-- `pointAlgebraSituationHom` is an isomorphism in every degree. -/
theorem isIso_pointAlgebraSituationHom_app (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ X.1)
    (n : ℤ) : IsIso ((pointAlgebraSituationHom X E hE hb T g).app n) :=
  SheafOfModules.GradedAlgebra.UnitalHom.isIso_ofIso_app _ n

/-- The Zariski reading of the comparison `Sym(g^*ℰ) ⟶ g^*Sym(ℰ)`, as a homomorphism. -/
def pointPullbackSymmetricZariskiHomBase (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ X.1) :
    SheafOfModules.GradedAlgebra.Hom (R := ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf)
      (zariskiReading T (symmetricAlgebra B S hS (yonedaSpace B S hS T)
        ((modulePullback B S hS (pointHom g)).obj E)))
      (zariskiReading T (etalePointAlgebra (symmetricAlgebra B S hS X E) T g)) :=
  haveI := isContinuous_selfOpensFunctor B S hS T
  (symmetricAlgebraPointPullbackHom E T g).toHom.pushforward (selfOpensStructureMap B S hS T)

/-- The Zariski reading of `Sym(g^*ℰ) ⟶ g^*Sym(ℰ)` is an isomorphism in every degree. -/
theorem isIso_pointPullbackSymmetricZariskiHomBase_app (T : BigFppfOver B S hS)
    (g : yoneda.obj T ⟶ X.1) (n : ℤ) :
    IsIso ((pointPullbackSymmetricZariskiHomBase X E T g).app n) :=
  Functor.map_isIso (SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T))
    ((symmetricAlgebraPointPullbackHom E T g).app n)

/-- The Zariski reading of the comparison `Sym(g^*ℰ) ⟶ g^*Sym(ℰ)`, as a unital homomorphism. -/
def pointPullbackSymmetricZariskiHom (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ X.1) :
    SheafOfModules.GradedAlgebra.UnitalHom (R := ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf)
      (zariskiReading T (symmetricAlgebra B S hS (yonedaSpace B S hS T)
        ((modulePullback B S hS (pointHom g)).obj E)))
      (zariskiReading T (etalePointAlgebra (symmetricAlgebra B S hS X E) T g)) :=
  @SheafOfModules.GradedAlgebra.UnitalHom.ofHomOfIsIso _ _ _ _ _ _
    (pointPullbackSymmetricZariskiHomBase X E T g)
    (isIso_pointPullbackSymmetricZariskiHomBase_app X E T g 0)

/-- `pointPullbackSymmetricZariskiHom` is an isomorphism in every degree. -/
theorem isIso_pointPullbackSymmetricZariskiHom_app (T : BigFppfOver B S hS)
    (g : yoneda.obj T ⟶ X.1) (n : ℤ) : IsIso ((pointPullbackSymmetricZariskiHom X E T g).app n) :=
  isIso_pointPullbackSymmetricZariskiHomBase_app X E T g n

/-- **The comparison `Sym((g^*ℰ)_Zar) ⟶ (g^*Sym ℰ)_Zar`** of graded algebras on the scheme of a
point: the Zariski reading commutes with `Sym` on quasi-coherent modules, and so does `g^*`. -/
def symmetricAlgebraPointComparison (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ X.1) :
    SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra (pointSymmetricAlgebra X E hE T g))
      (situationAlgebra ((projectiveBundleSituation X E hE hb).pointAlgebra T g)) :=
  haveI := isQuasicoherent_pointZariskiModule X E hE T g
  (situationAlgebraSymmetricHom (pointZariskiModule X E T g)).comp
    ((zariskiReadingSymmetricAlgebraHom T ((modulePullback B S hS (pointHom g)).obj E)).comp
      ((pointPullbackSymmetricZariskiHom X E T g).comp (pointAlgebraSituationHom X E hE hb T g)))

/-- The comparison `Sym((g^*ℰ)_Zar) ⟶ (g^*Sym ℰ)_Zar` is an isomorphism in every degree. -/
theorem isIso_symmetricAlgebraPointComparison_app (T : BigFppfOver B S hS)
    (g : yoneda.obj T ⟶ X.1) (n : ℤ) :
    IsIso ((symmetricAlgebraPointComparison X E hE hb T g).app n) := by
  have := isQuasicoherent_pointZariskiModule X E hE T g
  have h2 := isIso_zariskiReadingSymmetricAlgebraHom_app T
    ((modulePullback B S hS (pointHom g)).obj E) (isQuasicoherentOnSite_pointPullback X E hE T g) n
  exact SheafOfModules.GradedAlgebra.UnitalHom.isIso_comp_app_of_isIso
    (situationAlgebraSymmetricHom (pointZariskiModule X E T g)) _ n
    (isIso_situationAlgebraSymmetricHom_app _ n)
    (SheafOfModules.GradedAlgebra.UnitalHom.isIso_comp_app_of_isIso
      (zariskiReadingSymmetricAlgebraHom T ((modulePullback B S hS (pointHom g)).obj E)) _ n h2
      (SheafOfModules.GradedAlgebra.UnitalHom.isIso_comp_app_of_isIso
        (pointPullbackSymmetricZariskiHom X E T g) (pointAlgebraSituationHom X E hE hb T g) n
        (isIso_pointPullbackSymmetricZariskiHom_app X E T g n)
        (isIso_pointAlgebraSituationHom_app X E hE hb T g n)))

/-- The comparison of the restriction of the re-presented algebra with that of the algebra, as a
unital homomorphism. -/
def shrinkPointAlgebraUnitalHom (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ X.1) :
    SheafOfModules.GradedAlgebra.UnitalHom
      (situationAlgebra ((projectiveBundleSituation X E hE hb).shrink.pointAlgebra T g))
      (situationAlgebra ((projectiveBundleSituation X E hE hb).pointAlgebra T g)) :=
  SheafOfModules.GradedAlgebra.UnitalHom.ofIso
    ((projectiveBundleSituation X E hE hb).shrinkPointAlgebraIso T g)

/-- `shrinkPointAlgebraUnitalHom` is an isomorphism in every degree. -/
instance isIso_shrinkPointAlgebraUnitalHom_app (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ X.1)
    (n : ℤ) : IsIso ((shrinkPointAlgebraUnitalHom X E hE hb T g).app n) :=
  SheafOfModules.GradedAlgebra.UnitalHom.isIso_ofIso_app _ n

/-- The identification of the restricted algebra of Stacks 084B at a scheme point with
`Sym((g^*ℰ)_Zar)`. -/
def pointAlgebraSymmetricHom (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ X.1) :
    SheafOfModules.GradedAlgebra.UnitalHom
      (situationAlgebra ((projectiveBundleSituation X E hE hb).relativeProjPoints.algebra T g))
      (situationAlgebra (pointSymmetricAlgebra X E hE T g)) :=
  (shrinkPointAlgebraUnitalHom X E hE hb T g).comp
    (unitalHomInverse (symmetricAlgebraPointComparison X E hE hb T g)
      (isIso_symmetricAlgebraPointComparison_app X E hE hb T g))

/-- `pointAlgebraSymmetricHom` is an isomorphism in every degree. -/
instance isIso_pointAlgebraSymmetricHom_app (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ X.1)
    (n : ℤ) : IsIso ((pointAlgebraSymmetricHom X E hE hb T g).app n) :=
  SheafOfModules.GradedAlgebra.UnitalHom.isIso_comp_app_of_isIso _ _ n
    (isIso_shrinkPointAlgebraUnitalHom_app X E hE hb T g n)
    (isIso_unitalHomInverse_app (symmetricAlgebraPointComparison X E hE hb T g)
      (isIso_symmetricAlgebraPointComparison_app X E hE hb T g) n)

/-- **Tag 0B3V for the relative Proj of `Sym(ℱ)` read as a `SheafGradedAlgebra`**: its sections
are the isomorphism classes of invertible quotients of `ℱ`. -/
def symmetricSectionsEquivInvertibleQuotientClass {Y : Scheme.{u}} (F : Y.Modules)
    [F.IsQuasicoherent] :
    {σ : Y ⟶ Stacks.RelativeProj.Situation.relativeProj
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.situation
          (Stacks.SymGraded.schemeSheafGradedAlgebra F
            (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F))) //
      σ ≫ Stacks.RelativeProj.Situation.relativeProjToBase
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.situation
          (Stacks.SymGraded.schemeSheafGradedAlgebra F
            (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F))) = 𝟙 Y} ≃
      Stacks.Divisors.InvertibleQuotientClass Y F :=
  Stacks.RelativeProj.projectiveBundleSectionsEquiv

/-- **The fibre of `𝐏(ℰ)` over a scheme point `g` is the projective bundle of `(g^*ℰ)_Zar`**:
`Proj_T(g^*Sym ℰ) ≅ 𝐏((g^*ℰ)_Zar)`, the target being the relative Proj of the projective bundle
situation of `(g^*ℰ)_Zar` (`situation_schemeSheafGradedAlgebra`). -/
def pointProjIso (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ X.1) :
    (relativeProj ((projectiveBundleSituation X E hE hb).relativeProjPoints.algebra T g)).scheme ≅
      Stacks.RelativeProj.Situation.relativeProj
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.situation
          (pointSymmetricAlgebra X E hE T g)) :=
  relativeProjCongr (pointAlgebraSymmetricHom X E hE hb T g)
      (isIso_pointAlgebraSymmetricHom_app X E hE hb T g) ≪≫
    Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.presentationIso
      (pointSymmetricAlgebra X E hE T g)

/-- The identification lies over the scheme of the point. -/
theorem pointProjIso_hom_toBase (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ X.1) :
    (pointProjIso X E hE hb T g).hom ≫ Stacks.RelativeProj.Situation.relativeProjToBase
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.situation
          (pointSymmetricAlgebra X E hE T g)) =
      (relativeProj
        ((projectiveBundleSituation X E hE hb).relativeProjPoints.algebra T g)).toBase :=
  (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.presentationIso_hom_toBase _)).trans
      (relativeProjCongr_hom_comp_toBase _ _))

/-- Precomposition with the image under `yoneda` of the identity of `T` is the identity. -/
theorem yoneda_map_id_comp_eq {T : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : yoneda.obj T ⟶ F) : yoneda.map (𝟙 T) ≫ g = g :=
  (congrArg (· ≫ g) (yoneda.map_id T)).trans (Category.id_comp g)

/-- Restricting along `yoneda.map h` preserves the equation `u ≫ p = g`. -/
private theorem yoneda_map_comp_comp_eq {T T' : BigFppfOver B S hS}
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (h : T' ⟶ T) (u : yoneda.obj T ⟶ F) (p : F ⟶ G)
    {g : yoneda.obj T ⟶ G} (hu : u ≫ p = g) : (yoneda.map h ≫ u) ≫ p = yoneda.map h ≫ g :=
  (Category.assoc _ _ _).trans (congrArg (yoneda.map h ≫ ·) hu)

/-- The points of `𝐏(ℰ)` over a scheme point `g` are the sections of `𝐏((g^*ℰ)_Zar) ⟶ T`. -/
def pointsEquivSections (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ X.1) :
    {u : yoneda.obj T ⟶ (relativeProjSymmetricAlgebra X E hE hb).1 //
        u ≫ (projectiveBundleπ X E hE hb).hom = g} ≃
      {σ : (BigFppfOver.toScheme B S hS).obj T ⟶ Stacks.RelativeProj.Situation.relativeProj
          (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.situation
            (pointSymmetricAlgebra X E hE T g)) //
        σ ≫ Stacks.RelativeProj.Situation.relativeProjToBase
          (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.situation
            (pointSymmetricAlgebra X E hE T g)) = 𝟙 _} :=
  (Equiv.subtypeEquivRight fun u =>
      Iff.of_eq (congrArg (fun w => u ≫ (projectiveBundleπ X E hE hb).hom = w)
        (yoneda_map_id_comp_eq g).symm)).trans <|
    ((projectiveBundleSituation X E hE hb).relativeProjPoints.pointEquivProjOver T g (𝟙 T)).trans <|
      (Equiv.subtypeEquivRight fun k =>
        Iff.of_eq (congrArg (fun w => k ≫ _ = w) ((BigFppfOver.toScheme B S hS).map_id T))).trans
        (Space.overEquivOfIso (pointProjIso X E hE hb T g)
            (pointProjIso_hom_toBase X E hE hb T g).symm (𝟙 _))

/-- **The points of `𝐏(ℰ)` over a scheme point `g` are the isomorphism classes of invertible
quotients of `g^*ℰ`** (Stacks 01O4 at scheme points; Stacks 0B4I). -/
def pointsEquivInvertibleQuotientClass (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ X.1) :
    {u : yoneda.obj T ⟶ (relativeProjSymmetricAlgebra X E hE hb).1 //
        u ≫ (projectiveBundleπ X E hE hb).hom = g} ≃
      InvertibleQuotientClass (yonedaSpace B S hS T) ((modulePullback B S hS (pointHom g)).obj E) :=
  haveI := isQuasicoherent_pointZariskiModule X E hE T g
  (pointsEquivSections X E hE hb T g).trans <|
    (symmetricSectionsEquivInvertibleQuotientClass (pointZariskiModule X E T g)).trans
      (invertibleQuotientClassZariskiEquiv T _
        (isQuasicoherentOnSite_pointPullback X E hE T g)).symm

/-! ### Base change on the scheme side -/

section SchemeBaseChange

variable {Y Y' : Scheme.{u}} (r : Y' ⟶ Y) (F : Y.Modules) [F.IsQuasicoherent] (F' : Y'.Modules)
  [F'.IsQuasicoherent] (e : F' ≅ (Scheme.Modules.pullback r).obj F)

/-- The identification `r^*Sym(ℱ) ≅ Sym(ℱ')` along `ℱ' ≅ r^*ℱ`, between the graded algebras of
the relative Proj situations of the two `SheafGradedAlgebra`s. -/
abbrev symmetricPullbackSituationHom :
    SheafOfModules.GradedAlgebra.UnitalHom
      (Stacks.Conormal.gradedPullback r
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.situation
          (Stacks.SymGraded.schemeSheafGradedAlgebra F
            (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F))).algebra)
      (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.situation
        (Stacks.SymGraded.schemeSheafGradedAlgebra F'
          (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F'))).algebra :=
  Stacks.RelativeProj.symmetricSituationPullbackHom r F F' e

/-- The identification `r^*Sym(ℱ) ≅ Sym(ℱ')` is an isomorphism in every degree. -/
theorem isIso_symmetricPullbackSituationHom_app (n : ℤ) :
    IsIso ((symmetricPullbackSituationHom r F F' e).app n) :=
  Stacks.RelativeProj.isIso_symmetricSituationPullbackHom_app r F F' e n

/-- **Tag 0B3V and base change, in the presentation through `SheafGradedAlgebra`s.** -/
theorem symmetricSectionsEquivInvertibleQuotientClass_baseChange
    (σ : Y ⟶ Stacks.RelativeProj.Situation.relativeProj
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.situation
          (Stacks.SymGraded.schemeSheafGradedAlgebra F
            (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F))))
    (hσ : σ ≫ Stacks.RelativeProj.Situation.relativeProjToBase
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.situation
          (Stacks.SymGraded.schemeSheafGradedAlgebra F
            (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F))) = 𝟙 Y)
    (σ' : Y' ⟶ Stacks.RelativeProj.Situation.relativeProj
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.situation
          (Stacks.SymGraded.schemeSheafGradedAlgebra F'
            (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F'))))
    (hσ' : σ' ≫ Stacks.RelativeProj.Situation.relativeProjToBase
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.situation
          (Stacks.SymGraded.schemeSheafGradedAlgebra F'
            (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F'))) = 𝟙 Y')
    (comm : σ' ≫ Stacks.RelativeProj.Situation.relativeProjBaseChange
        (s := Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.situation
          (Stacks.SymGraded.schemeSheafGradedAlgebra F
            (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F)))
        (s' := Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.situation
          (Stacks.SymGraded.schemeSheafGradedAlgebra F'
            (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F')))
        r (symmetricPullbackSituationHom r F F' e)
        (fun m => isIso_symmetricPullbackSituationHom_app r F F' e m) = r ≫ σ) :
    symmetricSectionsEquivInvertibleQuotientClass F' ⟨σ', hσ'⟩ =
      Stacks.ProjectiveBundleQuotients.baseChangeClass r e
        (symmetricSectionsEquivInvertibleQuotientClass F ⟨σ, hσ⟩) :=
  Stacks.RelativeProj.projectiveBundleSectionsEquiv_baseChange_of_iso r F F' e σ hσ σ' hσ' comm

/-- A degree-one generator stays pairwise commuting after a unital homomorphism. -/
theorem _root_.SheafOfModules.GradedAlgebra.PairwiseCommutes.comp_unitalHom {C : Type*}
    [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat}
    {A₁ A₂ : SheafOfModules.GradedAlgebra R} {M : SheafOfModules R} {ι : M ⟶ A₁.piece 1}
    (hι : SheafOfModules.GradedAlgebra.PairwiseCommutes ι)
    (Φ : SheafOfModules.GradedAlgebra.UnitalHom A₁ A₂) :
    SheafOfModules.GradedAlgebra.PairwiseCommutes (ι ≫ Φ.app 1) := fun U a b =>
  ((Φ.map_mul 1 1 U (ι.val.app U a) (ι.val.app U b)).symm.trans
    (congrArg (fun z => (Φ.app (1 + 1)).val.app U z) (hι U a b))).trans
      (Φ.map_mul 1 1 U (ι.val.app U b) (ι.val.app U a))

/-- In degree one, the identification `Sym(ℱ') ≅ r^*Sym(ℱ)` sends the generator to the pullback
of the generator, read along `ℱ' ≅ r^*ℱ`. -/
theorem symmetricAlgebraGen_comp_baseChangeCongrHom_app_one :
    Scheme.Modules.symmetricAlgebraGen Y' F' ≫
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeCongrHom
          (Stacks.SymGraded.schemeSheafGradedAlgebra F
            (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F))
          (Stacks.SymGraded.schemeSheafGradedAlgebra F'
            (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F'))
          r (symmetricPullbackSituationHom r F F' e)
          (isIso_symmetricPullbackSituationHom_app r F F' e)).app 1 =
      e.hom ≫ (Stacks.RingedSpace.pullbackFunctor
        (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ringedSpaceHom r)).map
          (Scheme.Modules.symmetricAlgebraGen Y F) := by
  have hgen := Stacks.SymmetricAlgebra.pullbackSheafifiedPieceIsoOfIso_generator r F F' e
  have hI := isIso_symmetricPullbackSituationHom_app r F F' e 1
  change Scheme.Modules.symmetricAlgebraGen Y' F' ≫
      (@inv _ _ _ _ ((symmetricPullbackSituationHom r F F' e).app 1) hI ≫ 𝟙 _) = _
  refine (congrArg (_ ≫ ·) (Category.comp_id _)).trans ?_
  exact @Stacks.RelativeSpecFunctorOfPoints.comp_inv_eq_of_comp_eq _ _ _ _ _ _ _ hI _
    ((Category.assoc _ _ _).trans ((congrArg (e.hom ≫ ·) hgen).trans (e.hom_inv_id_assoc _)))

/-- **A square of identifications of graded algebras with symmetric algebras commutes as soon as
it commutes on the generators.** For `ρ : B' ≅ r^*B`, `Ψ : B ≅ Sym(ℱ)` and `Ψ' : B' ≅ Sym(ℱ')`,
if `ρ` carries the generator of `Sym(ℱ')`, read in `B'` through `Ψ'`, to the pullback of the
generator of `Sym(ℱ)` read in `B` through `Ψ`, along `ℱ' ≅ r^*ℱ`, then `ρ` followed by `r^*Ψ` is
`Ψ'` followed by the identification `Sym(ℱ') ≅ r^*Sym(ℱ)`. -/
theorem comp_baseAlgebraMapHom_eq_of_generator
    {A : SheafGradedAlgebra Y} {A' : SheafGradedAlgebra Y'}
    (ρ : SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra A')
      (situationAlgebra (A.pullback r)))
    (Ψ : SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra A)
      (situationAlgebra (Stacks.SymGraded.schemeSheafGradedAlgebra F
        (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F))))
    (hΨ : ∀ n : ℤ, IsIso (Ψ.app n))
    (Ψ' : SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra A')
      (situationAlgebra (Stacks.SymGraded.schemeSheafGradedAlgebra F'
        (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F'))))
    (hΨ' : ∀ n : ℤ, IsIso (Ψ'.app n))
    (h1 : Scheme.Modules.symmetricAlgebraGen Y' F' ≫ (unitalHomInverse Ψ' hΨ').app 1 ≫ ρ.app 1 =
      e.hom ≫ (Stacks.RingedSpace.pullbackFunctor
        (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ringedSpaceHom r)).map
          (Scheme.Modules.symmetricAlgebraGen Y F ≫ (unitalHomInverse Ψ hΨ).app 1)) :
    ρ.comp (baseAlgebraMapHom r Ψ) =
      Ψ'.comp (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeCongrHom
        (Stacks.SymGraded.schemeSheafGradedAlgebra F
          (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F))
        (Stacks.SymGraded.schemeSheafGradedAlgebra F'
          (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F'))
        r (symmetricPullbackSituationHom r F F' e)
        (isIso_symmetricPullbackSituationHom_app r F F' e)) := by
  set Θ := Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeCongrHom
    (Stacks.SymGraded.schemeSheafGradedAlgebra F
      (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F))
    (Stacks.SymGraded.schemeSheafGradedAlgebra F'
      (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F'))
    r (symmetricPullbackSituationHom r F F' e)
    (isIso_symmetricPullbackSituationHom_app r F F' e)
  have hU := (Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra Y' F').isUniversal
  have hκ := hU.1.comp_unitalHom Θ
  have key : (unitalHomInverse Ψ' hΨ').comp (ρ.comp (baseAlgebraMapHom r Ψ)) = Θ := by
    refine hU.hom_ext hκ ?_ rfl
    have h3 : (unitalHomInverse Ψ hΨ).app 1 ≫ Ψ.app 1 = 𝟙 _ := by
      have := hΨ 1
      exact IsIso.inv_hom_id (Ψ.app 1)
    refine ((congrArg (Scheme.Modules.symmetricAlgebraGen Y' F' ≫ ·)
      (Category.assoc _ _ _).symm).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (baseAlgebraMapHom r Ψ).app 1) ((Category.assoc _ _ _).trans h1)).trans
          ?_))).trans (symmetricAlgebraGen_comp_baseChangeCongrHom_app_one r F F' e).symm
    refine (Category.assoc _ _ _).trans (congrArg (e.hom ≫ ·) ?_)
    refine ((Stacks.RingedSpace.pullbackFunctor
      (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ringedSpaceHom r)).map_comp _ _).symm.trans ?_
    refine congrArg (Stacks.RingedSpace.pullbackFunctor
      (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ringedSpaceHom r)).map ?_
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h3).trans (Category.comp_id _))
  refine SheafOfModules.GradedAlgebra.UnitalHom.ext fun n => ?_
  have hk := congrArg (fun φ => SheafOfModules.GradedAlgebra.UnitalHom.app φ n) key
  simp only [SheafOfModules.GradedAlgebra.UnitalHom.comp_app] at hk ⊢
  rw [← hk]
  have := hΨ' n
  change _ = Ψ'.app n ≫ inv (Ψ'.app n) ≫ _
  rw [IsIso.hom_inv_id_assoc]

end SchemeBaseChange



/-- **The sections attached to a point and to its restriction** are related by the comparison
morphism of the third assertion of Stacks 084B. -/
theorem toScheme_map_comp_sectionOfPoint {T T' : BigFppfOver B S hS} (g : yoneda.obj T ⟶ X.1)
    (h : T' ⟶ T) (u : yoneda.obj T ⟶ (relativeProjSymmetricAlgebra X E hE hb).1)
    (hu : u ≫ (projectiveBundleSituation X E hE hb).relativeProjπ = yoneda.map (𝟙 T) ≫ g)
    (hu' : (yoneda.map h ≫ u) ≫ (projectiveBundleSituation X E hE hb).relativeProjπ =
      yoneda.map (𝟙 T') ≫ (yoneda.map h ≫ g)) :
    (BigFppfOver.toScheme B S hS).map h ≫
        (projectiveBundleSituation X E hE hb).relativeProjPoints.sectionOfPoint T g (𝟙 T) u hu =
      (projectiveBundleSituation X E hE hb).relativeProjPoints.sectionOfPoint T'
          (yoneda.map h ≫ g) (𝟙 T') (yoneda.map h ≫ u) hu' ≫
        (BigFppfOver.toScheme B S hS).map
          ((projectiveBundleSituation X E hE hb).quadrupleRestriction.projComparison
            (projectiveBundleSituation X E hE hb).shrink.contains_relativeProj_pointAlgebra
              g h) := by
  have hu'' : (yoneda.map h ≫ u) ≫ (projectiveBundleSituation X E hE hb).relativeProjπ =
      yoneda.map h ≫ g :=
    yoneda_map_comp_comp_eq h u _ (hu.trans (yoneda_map_id_comp_eq g))
  exact ((projectiveBundleSituation X E hE hb).relativeProjPoints.sectionOfPoint_restrict' T g
    (𝟙 T) h h (Category.comp_id h).symm u hu hu'').symm.trans
    (GradedAlgebraRestriction.sectionOfPoint_eq_comp_projComparison _ _
      (projectiveBundleSituation X E hE hb).space.property.isSheaf T g h (yoneda.map h ≫ u)
        hu'' hu')

/-! ### The comparison of Stacks 084B against identifications with symmetric algebras -/

section RestrictionSquare

namespace GradedAlgebraRestriction

variable {X₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Â : ∀ T : BigFppfOver B S hS, (yoneda.obj T ⟶ X₀) →
      SheafGradedAlgebra ((BigFppfOver.toScheme B S hS).obj T)}
  (ρ : GradedAlgebraRestriction (GradedAlgebraPoints.ofQuasicoherentFamily Â))
  (hc : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X₀),
    B.Contains (relativeProj (Â T f)).scheme)

/-- **The comparison morphism of Stacks 084B, read through identifications of the restricted
algebras with symmetric algebras, is the base change of projective bundles**, as soon as the
restriction datum carries the generators to the pulled-back generators. -/
theorem toScheme_map_projComparison_comp_symmetric {T T' : BigFppfOver B S hS}
    (g : yoneda.obj T ⟶ X₀) (h : T' ⟶ T)
    (F : ((BigFppfOver.toScheme B S hS).obj T).Modules) [F.IsQuasicoherent]
    (F' : ((BigFppfOver.toScheme B S hS).obj T').Modules) [F'.IsQuasicoherent]
    (e : F' ≅ (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).obj F)
    (Ψ : SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra (Â T g))
      (situationAlgebra (Stacks.SymGraded.schemeSheafGradedAlgebra F
        (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F))))
    (hΨ : ∀ n : ℤ, IsIso (Ψ.app n))
    (Ψ' : SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra (Â T' (yoneda.map h ≫ g)))
      (situationAlgebra (Stacks.SymGraded.schemeSheafGradedAlgebra F'
        (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F'))))
    (hΨ' : ∀ n : ℤ, IsIso (Ψ'.app n))
    (h1 : Scheme.Modules.symmetricAlgebraGen _ F' ≫ (unitalHomInverse Ψ' hΨ').app 1 ≫
        (ρ.restrict h g (yoneda.map h ≫ g) rfl).app 1 =
      e.hom ≫ (Stacks.RingedSpace.pullbackFunctor
        (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ringedSpaceHom
          ((BigFppfOver.toScheme B S hS).map h))).map
        (Scheme.Modules.symmetricAlgebraGen _ F ≫ (unitalHomInverse Ψ hΨ).app 1)) :
    (BigFppfOver.toScheme B S hS).map (ρ.projComparison hc g h) ≫
        (relativeProjCongr Ψ hΨ).hom ≫
          (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.presentationIso
            (Stacks.SymGraded.schemeSheafGradedAlgebra F
              (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F))).hom =
      (relativeProjCongr Ψ' hΨ').hom ≫
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.presentationIso
          (Stacks.SymGraded.schemeSheafGradedAlgebra F'
            (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F'))).hom ≫
        Stacks.RelativeProj.Situation.relativeProjBaseChange
          (s := Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.situation
            (Stacks.SymGraded.schemeSheafGradedAlgebra F
              (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F)))
          (s' := Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.situation
            (Stacks.SymGraded.schemeSheafGradedAlgebra F'
              (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F')))
          ((BigFppfOver.toScheme B S hS).map h) (symmetricPullbackSituationHom _ F F' e)
          (fun m => isIso_symmetricPullbackSituationHom_app _ F F' e m) := by
  refine ((congrArg (· ≫ _) (ρ.toScheme_map_projComparison hc g h)).trans
    (Category.assoc _ _ _)).trans ?_
  exact Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.relativeProjCongr_baseChange_square
    _ _ _ _ (isIso_symmetricPullbackSituationHom_app _ F F' e)
    (ρ.restrict h g (yoneda.map h ≫ g) rfl) (ρ.isIso_restrict_app h g _ rfl) Ψ hΨ Ψ' hΨ'
    (comp_baseAlgebraMapHom_eq_of_generator _ F F' e (ρ.restrict h g (yoneda.map h ≫ g) rfl)
      Ψ hΨ Ψ' hΨ' h1)

end GradedAlgebraRestriction

end RestrictionSquare

/-! ### Naturality in the test object -/

/-- The identification of the Zariski readings of the two pullbacks of `ℰ` along a morphism of test
objects: `(g'^*ℰ)_Zar ≅ τ^*(g^*ℰ)_Zar`, through the composition comparison of Stacks 03LU and the
base change of the Zariski reading. -/
def pointZariskiModuleBaseChangeIso {T T' : BigFppfOver B S hS} (g : yoneda.obj T ⟶ X.1)
    (h : T' ⟶ T) :
    pointZariskiModule X E T' (yoneda.map h ≫ g) ≅
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).obj
        (pointZariskiModule X E T g) :=
  (zariskiReadingFunctor T').mapIso ((modulePullbackCompIso B S hS
      (representedSpaceMap B S hS h : yonedaSpace B S hS T' ⟶ yonedaSpace B S hS T)
      (pointHom g)).app E).symm ≪≫
    (zariskiReadingPullbackIso h _ (isQuasicoherentOnSite_pointPullback X E hE T g)).symm

section GeneratorRestrict

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (ringedSpaceHom)


/-- If `I ≫ U = Φ`, with `U` the image of an isomorphism `φ` under a functor `H` up to the
spellings of its source and target, then a morphism `gen` with `gen ≫ Φ` the image of `gE`
satisfies `gen ≫ I = H(gE ≫ φ⁻¹)`, up to transport. -/
theorem comp_eq_map_comp_inv_of_comp_eq {C D : Type*} [Category C] [Category D] (H : D ⥤ C)
    {E' Na Nb : D} {G P Bg W : C} (gen : H.obj E' ⟶ G) (Φ : G ⟶ Bg) (U : P ⟶ Bg) (I : G ⟶ P)
    (hI : I ≫ U = Φ) (ph : Na ≅ Nb) (gE : E' ⟶ Nb) (hP : P = H.obj Na) (hB : Bg = H.obj Nb)
    (hUf : HEq U (H.map ph.hom)) (hW : H.obj Nb = W) (k : W ⟶ Bg) (e₃ : W = Bg)
    (hk : k = eqToHom e₃) (b : H.obj E' ⟶ W) (hΦ : gen ≫ Φ = b ≫ k) (hb : HEq b (H.map gE)) :
    gen ≫ I = H.map (gE ≫ ph.inv) ≫ eqToHom hP.symm := by
  subst hP hB
  obtain rfl := eq_of_heq hUf
  subst hW hk hI
  obtain rfl := eq_of_heq hb
  simp only [eqToHom_refl, Category.comp_id] at hΦ ⊢
  rw [Functor.map_comp, ← hΦ]
  simp

/-- The components of a transported isomorphism of graded algebras are those of the
isomorphism. -/
theorem _root_.SheafOfModules.GradedAlgebra.heq_eqToIso_trans_trans_eqToIso_hom_app {C : Type*}
    [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat}
    {A₁ A₂ A₃ A₄ : SheafOfModules.GradedAlgebra R} (p : A₁ = A₂) (φ : A₂ ≅ A₃) (q : A₃ = A₄)
    (n : ℤ) :
    HEq (SheafOfModules.GradedAlgebra.Hom.app (eqToIso p ≪≫ φ ≪≫ eqToIso q).hom n)
      (SheafOfModules.GradedAlgebra.Hom.app φ.hom n) := by
  subst p q
  simp



/-- The inverse of `U ≫ Φ⁻¹`, followed by `U`, is `Φ`. -/
theorem inv_comp_inv_comp_eq_of_isIso {C : Type*} [Category C] {P B G : C} (U : P ⟶ B)
    (Φ : G ⟶ B) [IsIso Φ] [IsIso (U ≫ inv Φ)] : inv (U ≫ inv Φ) ≫ U = Φ := by
  rw [IsIso.inv_comp_eq]
  simp


/-- **The comparison of Stacks 084B against a base change square**: if the comparison `pc`
agrees with `c` up to the spellings of its source and target, and `x = e ≫ F(y) ≫ c`, then `x`
followed by the inverse of `pc` is `e` followed by `F(y)`, up to transport. -/
theorem comp_eqToHom_comp_inv_eq_of_heq {C D : Type*} [Category C] [Category D] (F : D ⥤ C)
    {Z : C} {Y Q P : D} {Q' P' : C} (e : Z ⟶ F.obj Y) (y : Y ⟶ Q) (x : Z ⟶ Q') (hQ : Q = P)
    (hQ' : Q' = P') (pc : F.obj P ⟶ P') (hpc : IsIso pc) (c : F.obj Q ⟶ Q') (hc : HEq pc c)
    (hx : x = e ≫ F.map y ≫ c) :
    (x ≫ eqToHom hQ') ≫ @inv _ _ _ _ pc hpc = e ≫ F.map (y ≫ eqToHom hQ) := by
  subst hQ hQ'
  obtain rfl := eq_of_heq hc
  simp [hx]

/-- The Zariski reading of the pullback of a homogeneous piece to a scheme point is the
homogeneous piece of the restricted algebra. -/
theorem zariskiReadingFunctor_obj_pointPullback_piece
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    {T : BigFppfOver B S hS} (g : yoneda.obj T ⟶ X.1) (n : ℤ) :
    (modulePullback B S hS (pointHom g) ⋙ zariskiReadingFunctor T).obj (A.piece n) =
      (zariskiReading T (etalePointAlgebra A T g)).piece n :=
  rfl


/-- The comparison of restricted algebras of Stacks 084B, degree by degree, in the spelling of the
module pullbacks. -/
theorem heq_pointComparison_app_zariskiReadingPullbackHom
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    {T T' : BigFppfOver B S hS} (g : yoneda.obj T ⟶ X.1) (h : T' ⟶ T) (n : ℤ) :
    HEq ((pointComparison A h g (yoneda.map h ≫ g) rfl).app n)
      ((zariskiReadingPullbackHom h).app ((modulePullback B S hS (pointHom g)).obj (A.piece n)) ≫
        (zariskiReadingFunctor T').map
          ((modulePullbackCompIso B S hS (representedSpaceMap B S hS h) (pointHom g)).hom.app
            (A.piece n))) :=
  heq_of_eq (pointComparison_app_eq_zariskiReadingPullbackHom_modulePullback A h g n)


/-- **A base change square through a composition comparison.** For `κ : F ⋙ G ≅ H` and a
natural transformation `β : R ⋙ P ⟶ G ⋙ R'` invertible at `F E`, the image under `R' ∘ H` of
`m : E ⟶ N` is read off from `P(R(F m))` through `κ` and `β`. -/
theorem map_map_eq_comp_inv_comp_map_map {𝒜 ℬ 𝒞 𝒟 ℰ : Type*} [Category 𝒜] [Category ℬ]
    [Category 𝒞] [Category 𝒟] [Category ℰ] (F : 𝒜 ⥤ ℬ) (G : ℬ ⥤ 𝒞) (H : 𝒜 ⥤ 𝒞)
    (κ : F ⋙ G ≅ H) (R : ℬ ⥤ 𝒟) (R' : 𝒞 ⥤ ℰ) (P : 𝒟 ⥤ ℰ) (β : R ⋙ P ⟶ G ⋙ R') {E N : 𝒜}
    (m : E ⟶ N) (hβ : IsIso (β.app (F.obj E))) :
    (H ⋙ R').map m = (R'.map (κ.inv.app E) ≫ @inv _ _ _ _ (β.app (F.obj E)) hβ) ≫
      P.map ((F ⋙ R).map m) ≫ β.app (F.obj N) ≫ R'.map (κ.hom.app N) := by
  simp only [Functor.comp_map]
  have h1 := β.naturality (F.map m)
  simp only [Functor.comp_map] at h1
  rw [Category.assoc, reassoc_of% h1, IsIso.inv_hom_id_assoc, ← R'.map_comp, ← R'.map_comp]
  congr 1
  have h2 := κ.hom.naturality m
  simp only [Functor.comp_map] at h2
  rw [h2, Iso.inv_hom_id_app_assoc]

/-- The Zariski reading of the pullback of `m : ℰ ⟶ 𝒜₁` along `g ∘ h` is the base change of the
Zariski reading of its pullback along `g`, read through `pointZariskiModuleBaseChangeIso`, the
base-change map of the Zariski reading and the composition comparison of Stacks 03LU. -/
theorem zariskiReadingFunctor_map_pointPullback_comp_eq
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X)) (m : E ⟶ A.piece 1)
    {T T' : BigFppfOver B S hS} (g : yoneda.obj T ⟶ X.1) (h : T' ⟶ T) :
    (modulePullback B S hS (pointHom (yoneda.map h ≫ g)) ⋙ zariskiReadingFunctor T').map m =
      (pointZariskiModuleBaseChangeIso X E hE g h).hom ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map
          ((modulePullback B S hS (pointHom g) ⋙ zariskiReadingFunctor T).map m) ≫
        (zariskiReadingPullbackHom h).app ((modulePullback B S hS (pointHom g)).obj (A.piece 1)) ≫
          (zariskiReadingFunctor T').map
            ((modulePullbackCompIso B S hS (representedSpaceMap B S hS h) (pointHom g)).hom.app
              (A.piece 1)) := by
  have he : (pointZariskiModuleBaseChangeIso X E hE g h).hom =
      (zariskiReadingFunctor T').map
          ((modulePullbackCompIso B S hS (representedSpaceMap B S hS h) (pointHom g)).inv.app E) ≫
        @inv _ _ _ _
          ((zariskiReadingPullbackHom h).app ((modulePullback B S hS (pointHom g)).obj E))
          (isIso_zariskiReadingPullbackHom_app h _
            (isQuasicoherentOnSite_pointPullback X E hE T g)) :=
    rfl
  rw [he]
  exact map_map_eq_comp_inv_comp_map_map _ _ _ _ _ _ _ _ m
    (isIso_zariskiReadingPullbackHom_app h _ (isQuasicoherentOnSite_pointPullback X E hE T g))

end GeneratorRestrict

section GeneratorRestrictPoint

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (ringedSpaceHom)

/-- The direct image to the Zariski site of the pullback of the comparison of the re-presented
algebra with the algebra is, degreewise, the Zariski reading of the pullback of its component. -/
theorem
    _root_.AlgebraicGeometry.Space.RelativeProjSituation.heq_zariskiReadingSmallAlgebraIso_hom_app
    (s : RelativeProjSituation.{u, u}) (T : BigFppfOver s.site s.base s.containsBase)
    (f : yoneda.obj T ⟶ s.space.1) (n : ℤ) :
    HEq ((s.zariskiReadingSmallAlgebraIso T f).hom.app n)
      ((modulePullback s.site s.base s.containsBase (pointHom f) ⋙ zariskiReadingFunctor T).map
        (s.smallAlgebraPieceIso n).hom) :=
  HEq.rfl

/-- Equal functors send a morphism to the same morphism. -/
theorem heq_functor_map_of_eq {C D : Type*} [Category C] [Category D]
    (K₁ K₂ : C ⥤ D) (hK : K₁ = K₂) {X Y : C} (f : X ⟶ Y) : HEq (K₁.map f) (K₂.map f) := by
  subst hK
  rfl

/-- The components of the unital homomorphism of a transport are transports. -/
theorem _root_.SheafOfModules.GradedAlgebra.UnitalHom.ofIso_eqToIso_app {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat} {A₁ A₂ : SheafOfModules.GradedAlgebra R}
    (p : A₁ = A₂) (n : ℤ) :
    (SheafOfModules.GradedAlgebra.UnitalHom.ofIso (eqToIso p)).app n =
      eqToHom (congrArg (fun A => SheafOfModules.GradedAlgebra.piece A n) p) := by
  subst p
  rfl


/-- The generator of `Sym(ℱ)`, read through `Sym(ℱ)` presented as a `SheafGradedAlgebra` and a
composite of three unital homomorphisms. -/
theorem symmetricAlgebraGen_comp_situationAlgebraSymmetricHom_comp_app_one {Y : Scheme.{u}}
    (F : Y.Modules) [F.IsQuasicoherent]
    {A₂ A₃ A₄ : SheafOfModules.GradedAlgebra.{u, u} Y.ringCatSheaf}
    (zr : SheafOfModules.GradedAlgebra.UnitalHom (Scheme.Modules.symmetricAlgebra Y F) A₂)
    (pp : SheafOfModules.GradedAlgebra.UnitalHom A₂ A₃)
    (pa : SheafOfModules.GradedAlgebra.UnitalHom A₃ A₄) (a : F ⟶ A₂.piece 1) (b : F ⟶ A₃.piece 1)
    (hz : Scheme.Modules.symmetricAlgebraGen Y F ≫ zr.app 1 = a) (hq : a ≫ pp.app 1 = b) :
    Scheme.Modules.symmetricAlgebraGen Y F ≫
        ((situationAlgebraSymmetricHom F).comp (zr.comp (pp.comp pa))).app 1 =
      @CategoryStruct.comp Y.Modules _ _ _ _ b (pa.app 1) :=
  (congrArg (Scheme.Modules.symmetricAlgebraGen Y F ≫ ·) (Category.id_comp _)).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hz).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hq))))

/-- The Zariski reading of a composite functor, on morphisms. -/
theorem comp_zariskiReadingFunctor_map {𝒳 : Type*} [Category 𝒳] {T : BigFppfOver B S hS}
    (G : 𝒳 ⥤ Modules.{u, u} B S hS (yonedaSpace B S hS T).1 (yonedaSpace B S hS T).2)
    {a b : 𝒳} (x : a ⟶ b) :
    (G ⋙ zariskiReadingFunctor T).map x = (zariskiReadingFunctor T).map (G.map x) :=
  rfl


include hE hb in
/-- **The generator of `Sym((g^*ℰ)_Zar)`, read in the restricted algebra of Stacks 084B**, is the
Zariski reading of the pullback of the generator of `Sym(ℰ)`, carried to the re-presented
algebra. -/
theorem symmetricAlgebraGen_comp_unitalHomInverse_pointAlgebraSymmetricHom_app_one
    (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ X.1) :
    haveI := isQuasicoherent_pointZariskiModule X E hE T g
    @CategoryStruct.comp ((BigFppfOver.toScheme B S hS).obj T).Modules _ _ _ _
        (Scheme.Modules.symmetricAlgebraGen _ (pointZariskiModule X E T g))
        ((unitalHomInverse (pointAlgebraSymmetricHom X E hE hb T g)
          (isIso_pointAlgebraSymmetricHom_app X E hE hb T g)).app 1) =
      @CategoryStruct.comp ((BigFppfOver.toScheme B S hS).obj T).Modules _ _ _ _
        ((modulePullback B S hS (pointHom g) ⋙ zariskiReadingFunctor T).map
          (symmetricAlgebraGen B S hS X E ≫
            ((projectiveBundleSituation X E hE hb).smallAlgebraPieceIso 1).inv :
            E ⟶ (projectiveBundleSituation X E hE hb).shrink.algebra.piece 1))
        (eqToHom (zariskiReadingFunctor_obj_pointPullback_piece X
          (projectiveBundleSituation X E hE hb).shrink.algebra g 1)) := by
  have := isQuasicoherent_pointZariskiModule X E hE T g
  have hI : (unitalHomInverse (pointAlgebraSymmetricHom X E hE hb T g)
          (isIso_pointAlgebraSymmetricHom_app X E hE hb T g)).app 1 ≫
        (shrinkPointAlgebraUnitalHom X E hE hb T g).app 1 =
      (symmetricAlgebraPointComparison X E hE hb T g).app 1 :=
    @inv_comp_inv_comp_eq_of_isIso _ _ _ _ _ ((shrinkPointAlgebraUnitalHom X E hE hb T g).app 1)
      ((symmetricAlgebraPointComparison X E hE hb T g).app 1)
      (isIso_symmetricAlgebraPointComparison_app X E hE hb T g 1)
      (isIso_pointAlgebraSymmetricHom_app X E hE hb T g 1)
  have z := symmetricAlgebraGen_comp_zariskiReadingSymmetricAlgebraHom_app_one T
    ((modulePullback B S hS (pointHom g)).obj E)
  have q := ((zariskiReadingFunctor T).map_comp _ _).symm.trans
    (congrArg (zariskiReadingFunctor T).map
      (symmetricAlgebraGen_comp_symmetricAlgebraPointPullbackHom_app_one E T g))
  have a2 : (pointAlgebraSituationHom X E hE hb T g).app 1 = _ :=
    SheafOfModules.GradedAlgebra.UnitalHom.ofIso_eqToIso_app _ 1
  have h0 : HEq ((shrinkPointAlgebraUnitalHom X E hE hb T g).app 1) _ :=
    SheafOfModules.GradedAlgebra.heq_eqToIso_trans_trans_eqToIso_hom_app _ _ _ 1
  have h1 := h0.trans (RelativeProjSituation.heq_zariskiReadingSmallAlgebraIso_hom_app
    (projectiveBundleSituation X E hE hb) T g 1)
  have hUf := h1.trans (heq_functor_map_of_eq _
    (modulePullback B S hS (pointHom g) ⋙ zariskiReadingFunctor T) (by exact rfl) _)
  have pp : (pointPullbackSymmetricZariskiHom X E T g).app 1 =
      (zariskiReadingFunctor T).map ((symmetricAlgebraPointPullbackHom E T g).app 1) := rfl
  have q' : (zariskiReadingFunctor T).map (symmetricAlgebraGen B S hS (yonedaSpace B S hS T)
      ((modulePullback B S hS (pointHom g)).obj E)) ≫
      (pointPullbackSymmetricZariskiHom X E T g).app 1 =
      (zariskiReadingFunctor T).map ((modulePullback B S hS (pointHom g)).map
      (symmetricAlgebraGen B S hS X E)) :=
    (congrArg (_ ≫ ·) pp).trans q
  have z' : Scheme.Modules.symmetricAlgebraGen _ (pointZariskiModule X E T g) ≫
      (zariskiReadingSymmetricAlgebraHom T ((modulePullback B S hS (pointHom g)).obj E)).app 1 =
      (zariskiReadingFunctor T).map (symmetricAlgebraGen B S hS (yonedaSpace B S hS T)
      ((modulePullback B S hS (pointHom g)).obj E)) := z
  have qS : @CategoryStruct.comp ((BigFppfOver.toScheme B S hS).obj T).Modules _ _
      ((zariskiReading T (symmetricAlgebra B S hS (yonedaSpace B S hS T)
      ((modulePullback B S hS (pointHom g)).obj E))).piece 1) _
      ((zariskiReadingFunctor T).map (symmetricAlgebraGen B S hS (yonedaSpace B S hS T)
      ((modulePullback B S hS (pointHom g)).obj E)))
      ((pointPullbackSymmetricZariskiHom X E T g).app 1) =
      (zariskiReadingFunctor T).map ((modulePullback B S hS (pointHom g)).map
      (symmetricAlgebraGen B S hS X E)) := q'
  refine comp_eq_map_comp_inv_of_comp_eq
    (C := ((BigFppfOver.toScheme B S hS).obj T).Modules)
    (modulePullback B S hS (pointHom g) ⋙ zariskiReadingFunctor T)
    (Na := (projectiveBundleSituation X E hE hb).shrink.algebra.piece 1)
    (Nb := (symmetricAlgebra B S hS X E).piece 1) _ _ _ _ hI
    ((projectiveBundleSituation X E hE hb).smallAlgebraPieceIso 1) (symmetricAlgebraGen B S hS X E)
    ?_ ?_ hUf ?_ ((pointAlgebraSituationHom X E hE hb T g).app 1) _ a2 _ ?_
    (heq_of_eq (comp_zariskiReadingFunctor_map _ _).symm)
  · exact (zariskiReadingFunctor_obj_pointPullback_piece X
      (projectiveBundleSituation X E hE hb).shrink.algebra g 1).symm
  · exact (zariskiReadingFunctor_obj_pointPullback_piece X
      (projectiveBundleSituation X E hE hb).algebra g 1).symm
  · exact zariskiReadingFunctor_obj_pointPullback_piece X (symmetricAlgebra B S hS X E) g 1
  · refine (symmetricAlgebraGen_comp_situationAlgebraSymmetricHom_comp_app_one _ _ _ _ _ _
      z' qS).trans ?_
    congr 1

end GeneratorRestrictPoint

/-- **The restriction datum of Stacks 084B and the identifications with symmetric algebras agree
on the generators.** -/
theorem pointGenerator_comp_restrict {T T' : BigFppfOver B S hS} (g : yoneda.obj T ⟶ X.1)
    (h : T' ⟶ T) :
    haveI := isQuasicoherent_pointZariskiModule X E hE T g
    haveI := isQuasicoherent_pointZariskiModule X E hE T' (yoneda.map h ≫ g)
    Scheme.Modules.symmetricAlgebraGen _ (pointZariskiModule X E T' (yoneda.map h ≫ g)) ≫
        (unitalHomInverse (pointAlgebraSymmetricHom X E hE hb T' (yoneda.map h ≫ g))
          (isIso_pointAlgebraSymmetricHom_app X E hE hb T' (yoneda.map h ≫ g))).app 1 ≫
        ((projectiveBundleSituation X E hE hb).quadrupleRestriction.restrict h g
          (yoneda.map h ≫ g) rfl).app 1 =
      (pointZariskiModuleBaseChangeIso X E hE g h).hom ≫
        (Stacks.RingedSpace.pullbackFunctor
          (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ringedSpaceHom
            ((BigFppfOver.toScheme B S hS).map h))).map
          (Scheme.Modules.symmetricAlgebraGen _ (pointZariskiModule X E T g) ≫
            (unitalHomInverse (pointAlgebraSymmetricHom X E hE hb T g)
              (isIso_pointAlgebraSymmetricHom_app X E hE hb T g)).app 1) := by
  have := isQuasicoherent_pointZariskiModule X E hE T g
  have := isQuasicoherent_pointZariskiModule X E hE T' (yoneda.map h ≫ g)
  have hA' :=
    symmetricAlgebraGen_comp_unitalHomInverse_pointAlgebraSymmetricHom_app_one X E hE hb T'
      (yoneda.map h ≫ g)
  have hA :=
    symmetricAlgebraGen_comp_unitalHomInverse_pointAlgebraSymmetricHom_app_one X E hE hb T g
  have as1 : Scheme.Modules.symmetricAlgebraGen _ (pointZariskiModule X E T' (yoneda.map h ≫ g)) ≫
        (unitalHomInverse (pointAlgebraSymmetricHom X E hE hb T' (yoneda.map h ≫ g))
          (isIso_pointAlgebraSymmetricHom_app X E hE hb T' (yoneda.map h ≫ g))).app 1 ≫
        ((projectiveBundleSituation X E hE hb).quadrupleRestriction.restrict h g
          (yoneda.map h ≫ g) rfl).app 1 =
      (@CategoryStruct.comp ((BigFppfOver.toScheme B S hS).obj T').Modules _ _ _ _
        (Scheme.Modules.symmetricAlgebraGen _ (pointZariskiModule X E T' (yoneda.map h ≫ g)))
        ((unitalHomInverse (pointAlgebraSymmetricHom X E hE hb T' (yoneda.map h ≫ g))
          (isIso_pointAlgebraSymmetricHom_app X E hE hb T' (yoneda.map h ≫ g))).app 1)) ≫
        ((projectiveBundleSituation X E hE hb).quadrupleRestriction.restrict h g
          (yoneda.map h ≫ g) rfl).app 1 := (Category.assoc _ _ _).symm
  have as2 : (Stacks.RingedSpace.pullbackFunctor
          (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ringedSpaceHom
            ((BigFppfOver.toScheme B S hS).map h))).map
          (Scheme.Modules.symmetricAlgebraGen _ (pointZariskiModule X E T g) ≫
            (unitalHomInverse (pointAlgebraSymmetricHom X E hE hb T g)
              (isIso_pointAlgebraSymmetricHom_app X E hE hb T g)).app 1) =
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map
          (Scheme.Modules.symmetricAlgebraGen _ (pointZariskiModule X E T g) ≫
            (unitalHomInverse (pointAlgebraSymmetricHom X E hE hb T g)
              (isIso_pointAlgebraSymmetricHom_app X E hE hb T g)).app 1) := rfl
  rw [as1, as2, hA', hA]
  rw [show ((projectiveBundleSituation X E hE hb).quadrupleRestriction.restrict h g
          (yoneda.map h ≫ g) rfl).app 1 =
      @inv ((BigFppfOver.toScheme B S hS).obj T').Modules _ _ _
        ((pointComparison (projectiveBundleSituation X E hE hb).shrink.algebra h g
          (yoneda.map h ≫ g) rfl).app 1)
        (isIso_pointComparison_app (projectiveBundleSituation X E hE hb).shrink.algebra
          (projectiveBundleSituation X E hE hb).shrink.isQuasicoherent h g _ rfl 1) from rfl]
  have hc := heq_pointComparison_app_zariskiReadingPullbackHom X
      (projectiveBundleSituation X E hE hb).shrink.algebra g h 1
  have hx := zariskiReadingFunctor_map_pointPullback_comp_eq X E hE
      (projectiveBundleSituation X E hE hb).shrink.algebra
      (symmetricAlgebraGen B S hS X E ≫
        ((projectiveBundleSituation X E hE hb).smallAlgebraPieceIso 1).inv :
        E ⟶ (projectiveBundleSituation X E hE hb).shrink.algebra.piece 1) g h
  have key := comp_eqToHom_comp_inv_eq_of_heq
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h))
    (pointZariskiModuleBaseChangeIso X E hE g h).hom
    ((modulePullback B S hS (pointHom g) ⋙ zariskiReadingFunctor T).map
      (symmetricAlgebraGen B S hS X E ≫
        ((projectiveBundleSituation X E hE hb).smallAlgebraPieceIso 1).inv :
        E ⟶ (projectiveBundleSituation X E hE hb).shrink.algebra.piece 1))
    ((modulePullback B S hS (pointHom (yoneda.map h ≫ g)) ⋙ zariskiReadingFunctor T').map
      (symmetricAlgebraGen B S hS X E ≫
        ((projectiveBundleSituation X E hE hb).smallAlgebraPieceIso 1).inv :
        E ⟶ (projectiveBundleSituation X E hE hb).shrink.algebra.piece 1))
    (zariskiReadingFunctor_obj_pointPullback_piece X
      (projectiveBundleSituation X E hE hb).shrink.algebra g 1)
    (zariskiReadingFunctor_obj_pointPullback_piece X
      (projectiveBundleSituation X E hE hb).shrink.algebra (yoneda.map h ≫ g) 1)
    ((pointComparison (projectiveBundleSituation X E hE hb).shrink.algebra h g
          (yoneda.map h ≫ g) rfl).app 1)
    (isIso_pointComparison_app (projectiveBundleSituation X E hE hb).shrink.algebra
          (projectiveBundleSituation X E hE hb).shrink.isQuasicoherent h g _ rfl 1)
    _ hc hx
  refine Eq.mpr ?_ key
  congr 1

/-- **The identifications of the fibres with projective bundles commute with the comparison of
Stacks 084B and the base change of projective bundles.** -/
theorem toScheme_map_projComparison_comp_pointProjIso {T T' : BigFppfOver B S hS}
    (g : yoneda.obj T ⟶ X.1) (h : T' ⟶ T) :
    haveI := isQuasicoherent_pointZariskiModule X E hE T g
    haveI := isQuasicoherent_pointZariskiModule X E hE T' (yoneda.map h ≫ g)
    (BigFppfOver.toScheme B S hS).map
        ((projectiveBundleSituation X E hE hb).quadrupleRestriction.projComparison
          (projectiveBundleSituation X E hE hb).shrink.contains_relativeProj_pointAlgebra g h) ≫
        (relativeProjCongr (pointAlgebraSymmetricHom X E hE hb T g)
          (isIso_pointAlgebraSymmetricHom_app X E hE hb T g)).hom ≫
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.presentationIso
          (pointSymmetricAlgebra X E hE T g)).hom =
      (relativeProjCongr (pointAlgebraSymmetricHom X E hE hb T' (yoneda.map h ≫ g))
          (isIso_pointAlgebraSymmetricHom_app X E hE hb T' (yoneda.map h ≫ g))).hom ≫
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.presentationIso
          (pointSymmetricAlgebra X E hE T' (yoneda.map h ≫ g))).hom ≫
        Stacks.RelativeProj.Situation.relativeProjBaseChange
          (s := Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.situation
            (pointSymmetricAlgebra X E hE T g))
          (s' := Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.situation
            (pointSymmetricAlgebra X E hE T' (yoneda.map h ≫ g)))
          ((BigFppfOver.toScheme B S hS).map h)
          (symmetricPullbackSituationHom ((BigFppfOver.toScheme B S hS).map h)
            (pointZariskiModule X E T g) (pointZariskiModule X E T' (yoneda.map h ≫ g))
            (pointZariskiModuleBaseChangeIso X E hE g h))
          (fun m => isIso_symmetricPullbackSituationHom_app ((BigFppfOver.toScheme B S hS).map h)
            (pointZariskiModule X E T g) (pointZariskiModule X E T' (yoneda.map h ≫ g))
            (pointZariskiModuleBaseChangeIso X E hE g h) m) := by
  have := isQuasicoherent_pointZariskiModule X E hE T g
  have := isQuasicoherent_pointZariskiModule X E hE T' (yoneda.map h ≫ g)
  exact GradedAlgebraRestriction.toScheme_map_projComparison_comp_symmetric
    (Â := (projectiveBundleSituation X E hE hb).shrink.pointAlgebra)
    (projectiveBundleSituation X E hE hb).quadrupleRestriction
    (projectiveBundleSituation X E hE hb).shrink.contains_relativeProj_pointAlgebra g h
    (pointZariskiModule X E T g) (pointZariskiModule X E T' (yoneda.map h ≫ g))
    (pointZariskiModuleBaseChangeIso X E hE g h)
    (pointAlgebraSymmetricHom X E hE hb T g) (isIso_pointAlgebraSymmetricHom_app X E hE hb T g)
    (pointAlgebraSymmetricHom X E hE hb T' (yoneda.map h ≫ g))
    (isIso_pointAlgebraSymmetricHom_app X E hE hb T' (yoneda.map h ≫ g))
    (pointGenerator_comp_restrict X E hE hb g h)

/-- **The bijection is natural in the test object** (Stacks 0B4I, through Stacks 01O4): restricting
a point of `𝐏(ℰ)` over `g` along `h : T' ⟶ T` corresponds to pulling the invertible quotient back
along the morphism of represented algebraic spaces, read through the composition comparison of
Stacks 03LU. -/
theorem pointsEquivInvertibleQuotientClass_natural {T T' : BigFppfOver B S hS}
    (g : yoneda.obj T ⟶ X.1) (h : T' ⟶ T)
    (u : {u : yoneda.obj T ⟶ (relativeProjSymmetricAlgebra X E hE hb).1 //
      u ≫ (projectiveBundleπ X E hE hb).hom = g}) :
    pointsEquivInvertibleQuotientClass X E hE hb T' (yoneda.map h ≫ g)
        ⟨yoneda.map h ≫ u.1, (Category.assoc _ _ _).trans (congrArg (yoneda.map h ≫ ·) u.2)⟩ =
      invertibleQuotientBaseChangeClass
        (ObjectProperty.homMk (yoneda.map h) : yonedaSpace B S hS T' ⟶ yonedaSpace B S hS T)
        ((modulePullbackCompIso B S hS
          (ObjectProperty.homMk (yoneda.map h) : yonedaSpace B S hS T' ⟶ yonedaSpace B S hS T)
          (pointHom g)).app E).symm
        (pointsEquivInvertibleQuotientClass X E hE hb T g u) := by
  have := isQuasicoherent_pointZariskiModule X E hE T g
  have := isQuasicoherent_pointZariskiModule X E hE T' (yoneda.map h ≫ g)
  set σ := pointsEquivSections X E hE hb T g u
  set σ' := pointsEquivSections X E hE hb T' (yoneda.map h ≫ g)
    ⟨yoneda.map h ≫ u.1, yoneda_map_comp_comp_eq h _ _ u.2⟩
  have hA := toScheme_map_comp_sectionOfPoint X E hE hb g h u.1
    (u.2.trans (yoneda_map_id_comp_eq g).symm)
    ((yoneda_map_comp_comp_eq h _ _ u.2).trans (yoneda_map_id_comp_eq _).symm)
  have hB := toScheme_map_projComparison_comp_pointProjIso X E hE hb g h
  have comm : σ'.1 ≫ Stacks.RelativeProj.Situation.relativeProjBaseChange
      (s := Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.situation
        (pointSymmetricAlgebra X E hE T g))
      (s' := Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.situation
        (pointSymmetricAlgebra X E hE T' (yoneda.map h ≫ g)))
      ((BigFppfOver.toScheme B S hS).map h)
      (symmetricPullbackSituationHom ((BigFppfOver.toScheme B S hS).map h)
        (pointZariskiModule X E T g) (pointZariskiModule X E T' (yoneda.map h ≫ g))
        (pointZariskiModuleBaseChangeIso X E hE g h))
      (fun m => isIso_symmetricPullbackSituationHom_app ((BigFppfOver.toScheme B S hS).map h)
        (pointZariskiModule X E T g) (pointZariskiModule X E T' (yoneda.map h ≫ g))
        (pointZariskiModuleBaseChangeIso X E hE g h) m) =
      (BigFppfOver.toScheme B S hS).map h ≫ σ.1 :=
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans hB.symm)).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hA.symm)))).trans (Category.assoc _ _ _)
  have hC := symmetricSectionsEquivInvertibleQuotientClass_baseChange
    ((BigFppfOver.toScheme B S hS).map h) (pointZariskiModule X E T g)
    (pointZariskiModule X E T' (yoneda.map h ≫ g)) (pointZariskiModuleBaseChangeIso X E hE g h)
    σ.1 σ.2 σ'.1 σ'.2 comm
  have hD := invertibleQuotientClassZariskiEquiv_baseChange h
    ((modulePullback B S hS (pointHom g)).obj E) (isQuasicoherentOnSite_pointPullback X E hE T g)
    ((modulePullback B S hS (pointHom (yoneda.map h ≫ g))).obj E)
    (isQuasicoherentOnSite_pointPullback X E hE T' (yoneda.map h ≫ g))
    ((modulePullbackCompIso B S hS
      (ObjectProperty.homMk (yoneda.map h) : yonedaSpace B S hS T' ⟶ yonedaSpace B S hS T)
      (pointHom g)).app E).symm
    ((invertibleQuotientClassZariskiEquiv T _ (isQuasicoherentOnSite_pointPullback X E hE T g)).symm
      (symmetricSectionsEquivInvertibleQuotientClass (pointZariskiModule X E T g) σ))
  rw [Equiv.apply_symm_apply] at hD
  simp only [pointsEquivInvertibleQuotientClass, Equiv.trans_apply]
  exact (Equiv.symm_apply_eq _).2 (hC.trans hD.symm)

end AlgebraicGeometry.Space

end
