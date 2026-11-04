module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAbelianInverseImageSquare
public import
  StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringBySimplicialObjectComponentCohomology
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringObjectCohomologyDescent
public import StacksFrontier.Topology.Simplicial.ProperHypercovering.QcHypercovering
public import StacksFrontier.Topology.Simplicial.ProperHypercovering.QcSmallCohomology
import StacksCore.Tactic.StacksAttribute

/-!
# The spectral sequence of a proper hypercovering

Let `U` be a simplicial object of the category `LC` of Hausdorff, locally quasi-compact spaces,
let `a : U → X` be an augmentation which is a proper hypercovering of `X`, let `F` be an abelian
sheaf on `X` and let `F_n` be its pullback to `U_n`. Stacks 09XB asserts that there is a
canonical spectral sequence

`E_1^{p,q} = H^q(U_p, F_p) ⇒ H^{p+q}(X, F)`.

The spectral sequence is that of Stacks 09WJ of the total site `(LC_qc/K)_total` of the
hypercovering `K` of `X` by `U` in a quasi-compact site `LC_qc` of Stacks 09X2 containing `X` and
every `U_n`, applied to the pullback of `F` to `(LC_qc/K)_total`.

## Main definitions

* `Stacks.Topology.Simplicial.ProperHypercoveringSpectralSequence`: the data of Stacks 09XB, a
  spectral sequence functorial in `F` with first page `H^q(U_p, F_p)` abutting to `H^{p+q}(X, F)`.
* `Stacks.Topology.Simplicial.properHypercoveringSpectralSequence`: the spectral sequence of
  Stacks 09XB of a proper hypercovering.
* `Stacks.Topology.Simplicial.opensMapTopoi`: the morphism of topoi of a continuous map, for
  sheaves of sets in the universe of the spaces.
* `Stacks.Topology.Simplicial.qcSmallComparisonSquareAbIso`: Stacks 0D92 for abelian sheaves on
  the small model of `LC_qc`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Simplicial
open Stacks.Topos.AbelianPushforward

universe u w

namespace Stacks.Topology.Simplicial

open Stacks.Topology Stacks.Topology.LocallyQuasiCompactZariskiSituation

/-! ### Cohomology of a space, indexed by the integers -/

open ZeroObject in
/-- The cohomology `H^n(A, F)` of an abelian sheaf on a space, indexed by the integers: the
`n`-th right derived functor of the sections over the whole space in degrees `n ≥ 0`, and zero
in negative degrees. -/
def cohomologyZ {A : TopCat.{u}} (F : Sheaf (Opens.grothendieckTopology A) AddCommGrpCat.{u})
    (n : ℤ) : AddCommGrpCat.{u} :=
  match n with
  | Int.ofNat k =>
    (((sheafSections (Opens.grothendieckTopology A) AddCommGrpCat.{u}).obj (op ⊤)).rightDerived
      k).obj F
  | Int.negSucc _ => 0

/-- In degree `n ≥ 0`, `cohomologyZ` is the `n`-th right derived functor of the sections over the
whole space. -/
theorem cohomologyZ_natCast {A : TopCat.{u}}
    (F : Sheaf (Opens.grothendieckTopology A) AddCommGrpCat.{u}) (n : ℕ) :
    cohomologyZ F n =
      (((sheafSections (Opens.grothendieckTopology A) AddCommGrpCat.{u}).obj (op ⊤)).rightDerived
        n).obj F :=
  rfl

/-! ### Two morphisms of topoi -/

/-- The morphism of topoi `Sh(A) ⟶ Sh(B)` of a continuous map `g : A ⟶ B`, for sheaves of sets in
the universe of the spaces: its direct image is the topological `g_*` and its inverse image the
topological `g⁻¹`. -/
def opensMapTopoi {A B : TopCat.{u}} (g : A ⟶ B) :
    MorphismOfTopoi (Sheaf (Opens.grothendieckTopology A) (Type u))
      (Sheaf (Opens.grothendieckTopology B) (Type u)) :=
  haveI : PreservesFiniteLimits ((Opens.map g).op.lan :
      ((Opens B)ᵒᵖ ⥤ Type u) ⥤ (Opens A)ᵒᵖ ⥤ Type u) :=
    lan_preservesFiniteLimits_of_representablyFlat.{u, u, u, u, u} (Opens.map g)
  { pushforward := (Opens.map g).sheafPushforwardContinuous (Type u)
      (Opens.grothendieckTopology B) (Opens.grothendieckTopology A)
    inverseImage := (Opens.map g).sheafPullback (Type u)
      (Opens.grothendieckTopology B) (Opens.grothendieckTopology A)
    adj := (Opens.map g).sheafAdjunctionContinuous (Type u)
      (Opens.grothendieckTopology B) (Opens.grothendieckTopology A)
    preservesFiniteLimits := Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _ }

/-- The abelian inverse image of the morphism of topoi of a continuous map is the topological
pullback of abelian sheaves. -/
def abelianInverseImageOpensMapTopoiIso {A B : TopCat.{u}} (g : A ⟶ B) :
    Sites.abelianInverseImage (opensMapTopoi g) ≅ TopCat.Sheaf.pullback AddCommGrpCat.{u} g :=
  haveI : ((Opens.map g).sheafPushforwardContinuous (Type u)
      (Opens.grothendieckTopology B) (Opens.grothendieckTopology A)).IsRightAdjoint :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map g) (Type u)
      (Opens.grothendieckTopology B) (Opens.grothendieckTopology A)).isRightAdjoint
  (abelianInverseImageAdjRestriction (Opens.map g) (Opens.grothendieckTopology B)
      (Opens.grothendieckTopology A) (opensMapTopoi g) (Iso.refl _)).leftAdjointUniq
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g)

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)

/-- The morphism of topoi of the localization `LC_qc/Y ⥤ LC_qc/X` along a morphism `f : Y ⟶ X`,
read on the small model: its inverse image is restriction along `Over.map f`. -/
def smallLocalizationTopoi {X Y : S.category} (f : Y ⟶ X) :
    MorphismOfTopoi (Sheaf (S.qcSite.smallOverTopology Y) (Type u))
      (Sheaf (S.qcSite.smallOverTopology X) (Type u)) where
  pushforward := (Over.map (S.qcSite.smallEquivalence.functor.map f)).sheafPushforwardCocontinuous
    (Type u) (S.qcSite.smallOverTopology Y) (S.qcSite.smallOverTopology X)
  inverseImage := (Over.map (S.qcSite.smallEquivalence.functor.map f)).sheafPushforwardContinuous
    (Type u) (S.qcSite.smallOverTopology Y) (S.qcSite.smallOverTopology X)
  adj := (Over.map (S.qcSite.smallEquivalence.functor.map f)).sheafAdjunctionCocontinuous (Type u)
    (S.qcSite.smallOverTopology Y) (S.qcSite.smallOverTopology X)
  preservesFiniteLimits := Functor.preservesFiniteLimits_sheafPushforwardContinuous _ _ _ (Type u)

/-- The abelian inverse image of the localization is restriction of abelian sheaves along
`Over.map f`. -/
def abelianInverseImageSmallLocalizationTopoiIso {X Y : S.category} (f : Y ⟶ X) :
    Sites.abelianInverseImage (smallLocalizationTopoi S f) ≅
      (Over.map (S.qcSite.smallEquivalence.functor.map f)).sheafPushforwardContinuous
        AddCommGrpCat.{u} (S.qcSite.smallOverTopology Y) (S.qcSite.smallOverTopology X) :=
  letI : ((Over.map (S.qcSite.smallEquivalence.functor.map f)).sheafPushforwardContinuous (Type u)
      (S.qcSite.smallOverTopology Y) (S.qcSite.smallOverTopology X)).IsRightAdjoint :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Over.map (S.qcSite.smallEquivalence.functor.map f)) (Type u)
      (S.qcSite.smallOverTopology Y) (S.qcSite.smallOverTopology X)).isRightAdjoint
  Sites.abelianInverseImageIsoSheafPushforwardContinuous _ _ _ _ (Iso.refl _)

/-! ### Stacks 0D92 on the small model -/

section ComparisonSquare

variable {X Y : S.category} (f : Y ⟶ X)

/-- Localizing along `f` and then passing to the small model is passing to the small model and
then localizing along the image of `f`. -/
def overMapCompPostIso :
    Over.map f ⋙ Over.post (X := X) S.qcSite.smallEquivalence.functor ≅
      Over.post (X := Y) S.qcSite.smallEquivalence.functor ⋙
        Over.map (S.qcSite.smallEquivalence.functor.map f) :=
  NatIso.ofComponents
    (fun _ ↦ Over.isoMk (Iso.refl _) ((Category.id_comp _).trans (Functor.map_comp _ _ _).symm))
    (fun g ↦ Over.OverMorphism.ext
      ((Category.comp_id (S.qcSite.smallEquivalence.functor.map g.left)).trans
        (Category.id_comp _).symm))

/-- The identifications of `Sh(LC_qc/X)` and `Sh(LC_qc/Y)` with the topoi of the small model
commute with localization along `f`, on the side of the inverse functors. -/
def smallOverSheafEquivInverseLocalizationIso :
    (S.qcSite.smallOverSheafEquiv X (Type u)).inverse ⋙ qcSliceInverseImage.{u, w, u} S f ≅
      (smallLocalizationTopoi S f).inverseImage ⋙
        (S.qcSite.smallOverSheafEquiv Y (Type u)).inverse :=
  letI := Functor.isContinuous_comp (Over.map f)
    (Over.post (X := X) S.qcSite.smallEquivalence.functor)
    (S.qcSite.grothendieckTopology.over Y) (S.qcSite.grothendieckTopology.over X)
    (S.qcSite.smallOverTopology X)
  letI := Functor.isContinuous_comp (Over.post (X := Y) S.qcSite.smallEquivalence.functor)
    (Over.map (S.qcSite.smallEquivalence.functor.map f))
    (S.qcSite.grothendieckTopology.over Y) (S.qcSite.smallOverTopology Y)
    (S.qcSite.smallOverTopology X)
  Functor.isoWhiskerRight (S.qcSite.smallOverSheafEquivInverseIso X (Type u)) _ ≪≫
    Functor.sheafPushforwardContinuousComp' (Iso.refl _) _ _ _ _ ≪≫
    Functor.sheafPushforwardContinuousIso (overMapCompPostIso S f) _ _ _ ≪≫
    (Functor.sheafPushforwardContinuousComp' (Iso.refl _) _ _ _ _).symm ≪≫
    Functor.isoWhiskerLeft _ (S.qcSite.smallOverSheafEquivInverseIso Y (Type u)).symm

/-- The identifications of `Sh(LC_qc/X)` and `Sh(LC_qc/Y)` with the topoi of the small model
commute with localization along `f`. -/
def smallOverSheafEquivLocalizationIso :
    qcSliceInverseImage.{u, w, u} S f ⋙ (S.qcSite.smallOverSheafEquiv Y (Type u)).functor ≅
      (S.qcSite.smallOverSheafEquiv X (Type u)).functor ⋙
        (smallLocalizationTopoi S f).inverseImage :=
  let EX := S.qcSite.smallOverSheafEquiv X (Type u)
  let EY := S.qcSite.smallOverSheafEquiv Y (Type u)
  (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight EX.unitIso _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft EX.functor ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (smallOverSheafEquivInverseLocalizationIso S f) EY.functor ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ EY.counitIso ≪≫ Functor.rightUnitor _)

/-- **Stacks 0D92 on the small model, for sheaves of sets.** The comparison morphisms
`a_X : Sh(LC_qc/X) → Sh(X)` commute with the morphisms induced by `f : Y ⟶ X`. -/
def qcSmallComparisonSquareIso :
    (opensMapTopoi ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).inverseImage ⋙
        (qcSmallBottomMorphism S Y).inverseImage ≅
      (qcSmallBottomMorphism S X).inverseImage ⋙ (smallLocalizationTopoi S f).inverseImage :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (qcTopologicalComparisonSquareIso.{u, w, u} S f) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (smallOverSheafEquivLocalizationIso S f) ≪≫
    (Functor.associator _ _ _).symm

/-- **Stacks 0D92 on the small model, for abelian sheaves.** For a morphism `f : Y ⟶ X` of
`LC_qc` with underlying continuous map `g`, restricting `a_X^{-1}F` along `Over.map f` is
`a_Y^{-1}(g^{-1}F)`, naturally in the abelian sheaf `F`. -/
def qcSmallComparisonSquareAbIso :
    TopCat.Sheaf.pullback AddCommGrpCat.{u}
        ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) ⋙
        Sites.abelianInverseImage (qcSmallBottomMorphism S Y) ≅
      Sites.abelianInverseImage (qcSmallBottomMorphism S X) ⋙
        (Over.map (S.qcSite.smallEquivalence.functor.map f)).sheafPushforwardContinuous
          AddCommGrpCat.{u} (S.qcSite.smallOverTopology Y) (S.qcSite.smallOverTopology X) :=
  Functor.isoWhiskerRight (abelianInverseImageOpensMapTopoiIso _).symm _ ≪≫
    StacksTag03LR.abelianInverseImageSquareIso _ _ _ _ (qcSmallComparisonSquareIso S f) ≪≫
    Functor.isoWhiskerLeft _ (abelianInverseImageSmallLocalizationTopoiIso S f)

end ComparisonSquare

/-! ### The spectral sequence of a hypercovering of `LC_qc` -/

section Qc

open CategoryTheory.SimplicialSemiRepresentable Stacks.CategoryTheory.Hypercovering

variable {X : S.category} (U : SimplicialObject S.category)
  (a : U ⟶ (SimplicialObject.const S.category).obj X)

/-- The total site `(LC_qc/K)_total` of the hypercovering `K_n = {U_n → X}`, formed in the small
model of `LC_qc`. -/
abbrev qcHypercoverTotal : SimplicialSiteSituation.{u} :=
  totalSituation S.qcSite.smallPretopology (U ⋙ S.qcSite.smallEquivalence.functor)
    (S.qcSite.smallAugmentation U a)

/-- The inverse image `a_K^{-1} a_X^{-1}` from abelian sheaves on `X` to abelian sheaves on the
total site `(LC_qc/K)_total`. -/
abbrev qcHypercoverTotalInverseImage :
    Sheaf (Opens.grothendieckTopology X.obj.obj) AddCommGrpCat.{u} ⥤
      Sheaf (qcHypercoverTotal S U a).totalTopology AddCommGrpCat.{u} :=
  Sites.abelianInverseImage (qcSmallBottomMorphism S X) ⋙
    SimplicialSiteSituation.Augmentation.totalInverseImageAb (qcHypercoverTotal S U a)
      (Cat.of (Over (S.qcSite.smallEquivalence.functor.obj X)))
      (S.qcSite.smallPretopology.toGrothendieck.over (S.qcSite.smallEquivalence.functor.obj X))
      (augmentationAugmented S.qcSite.smallPretopology (U ⋙ S.qcSite.smallEquivalence.functor)
        (S.qcSite.smallAugmentation U a))

/-- The spectral sequence of Stacks 09WJ of the total site `(LC_qc/K)_total`, applied to
`a_K^{-1}a_X^{-1}F`, as a functor of the abelian sheaf `F` on `X`. -/
def qcHypercoverSpectralSequence :
    Sheaf (Opens.grothendieckTopology X.obj.obj) AddCommGrpCat.{u} ⥤
      CohomologicalSpectralSequence AddCommGrpCat.{u} 1 :=
  qcHypercoverTotalInverseImage S U a ⋙ (qcHypercoverTotal S U a).cohomologySpectralSequence

/-- **The first page.** `E_1^{p,q} = H^q(U_p, F_p)`, naturally in `F`, where `F_p` is the pullback
of `F` along `a_p : U_p → X`. -/
def qcHypercoverSpectralSequencePageOneIso (p q : ℕ) :
    qcHypercoverSpectralSequence S U a ⋙
        SpectralSequence.pageFunctor AddCommGrpCat.{u} _ 1 1 le_rfl ⋙
        HomologicalComplex.eval _ _ ((p : ℤ), (q : ℤ)) ≅
      TopCat.Sheaf.pullback AddCommGrpCat.{u}
          ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map (a.app (op ⦋p⦌))) ⋙
        ((sheafSections (Opens.grothendieckTopology (U.obj (op ⦋p⦌)).obj.obj)
          AddCommGrpCat.{u}).obj (op ⊤)).rightDerived q :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      ((qcHypercoverTotal S U a).cohomologySpectralSequence_pageOneIso p q) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (componentCohomologyInverseImageIso _ _ _ p q) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (qcSmallComparisonSquareAbIso S (X := X) (Y := U.obj (op ⦋p⦌)) (a.app (op ⦋p⦌))).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (smallQcCohomologyComparisonIso S (U.obj (op ⦋p⦌)) q)

variable {U a} in
/-- **The abutment.** The spectral sequence abuts to `H^{p+q}(X, F)`, when the augmentation is a
hypercovering of `X` in `LC_qc`. -/
theorem qcHypercoverSpectralSequence_abutsTo
    (h : IsHypercoveringAugmentation S.qcSite.pretopology U a)
    (F : Sheaf (Opens.grothendieckTopology X.obj.obj) AddCommGrpCat.{u}) :
    SpectralSequence.AbutsTo ((qcHypercoverSpectralSequence S U a).obj F) (cohomologyZ F) := by
  have hK := (S.qcSite.isHypercoveringAugmentation_smallAugmentation U a h).isHypercovering
    S.qcSite.smallPretopology (U ⋙ S.qcSite.smallEquivalence.functor)
      (S.qcSite.smallAugmentation U a)
  refine ((qcHypercoverTotal S U a).cohomologySpectralSequence_abutsTo _).of_iso fun n ↦ ?_
  rcases n with k | k
  · exact (qcHypercoverTotal S U a).totalCohomologyZ_iso_rightDerived _ k ≪≫
      ((rightDerivedGlobalSectionsIsoOfHypercovering _ _ hK k).app _).symm ≪≫
      (smallQcCohomologyComparisonIso S X k).app F
  · exact IsZero.iso ((qcHypercoverTotal S U a).isZero_totalCohomologyZ_of_neg _ _
      (Int.negSucc_lt_zero k)) (isZero_zero AddCommGrpCat.{u})

end Qc

/-! ### Stacks 09XB -/

section ProperHypercovering

variable (Y : SimplicialObject LocallyQuasiCompactHausdorff.{u})
  (T : LocallyQuasiCompactHausdorff.{u})
  (b : Y ⟶ (SimplicialObject.const LocallyQuasiCompactHausdorff).obj T)

/-- A site `LC_qc` of Stacks 09X2 containing `T` and every `Y_n`, chosen once and for all. -/
def chosenQcSite :
    LocallyQuasiCompactZariskiSituation.{u, u + 1} (Set.range Y.obj ∪ {T}) Cardinal.stacksBound :=
  ⟨Classical.choose (exists_locallyQuasiCompactQcSite _
    (exists_boundedLCSubcategory (Set.range Y.obj ∪ {T})).some)⟩

/-- The chosen site contains `T` and every `Y_n`. -/
theorem chosenQcSite_contains (Z : LocallyQuasiCompactHausdorff.{u})
    (hZ : Z ∈ Set.range Y.obj ∪ {T}) : (chosenQcSite Y T).qcSite.Contains Z := by
  have h := (exists_boundedLCSubcategory (Set.range Y.obj ∪ {T})).some.contains_initial Z hZ
  rwa [← Classical.choose_spec (exists_locallyQuasiCompactQcSite _
    (exists_boundedLCSubcategory (Set.range Y.obj ∪ {T})).some)] at h

/-- **The data of Stacks 09XB.** A spectral sequence, functorial in the abelian sheaf `F` on `T`,
whose first page is `E_1^{p,q} = H^q(Y_p, F_p)`, naturally in `F`, with `F_p` the pullback of `F`
along `b_p : Y_p → T`, and which abuts to `H^{p+q}(T, F)`. -/
structure ProperHypercoveringSpectralSequence where
  /-- The spectral sequence, as a functor of the abelian sheaf on `T`. -/
  sequence : Sheaf (Opens.grothendieckTopology T.obj) AddCommGrpCat.{u} ⥤
    CohomologicalSpectralSequence AddCommGrpCat.{u} 1
  /-- The first page: `E_1^{p,q} = H^q(Y_p, F_p)`, naturally in `F`. -/
  pageOneIso (p q : ℕ) :
    sequence ⋙ SpectralSequence.pageFunctor AddCommGrpCat.{u} _ 1 1 le_rfl ⋙
        HomologicalComplex.eval _ _ ((p : ℤ), (q : ℤ)) ≅
      TopCat.Sheaf.pullback AddCommGrpCat.{u}
          (locallyQuasiCompactHausdorffToTop.map (b.app (op ⦋p⦌))) ⋙
        ((sheafSections (Opens.grothendieckTopology (Y.obj (op ⦋p⦌)).obj)
          AddCommGrpCat.{u}).obj (op ⊤)).rightDerived q
  /-- The convergence: the spectral sequence abuts to `H^{p+q}(T, F)`. -/
  abutsTo (F : Sheaf (Opens.grothendieckTopology T.obj) AddCommGrpCat.{u}) :
    SpectralSequence.AbutsTo (sequence.obj F) (cohomologyZ F)

variable {Y T b} in
/-- Let `U` be a simplicial object of the category `LC` of Hausdorff, locally quasi-compact spaces
and let `a : U → X` be an augmentation. Let `F` be an abelian sheaf on `X` and let `F_n` be its
pullback to `U_n`. If `U` is a proper hypercovering of `X`, there is a canonical spectral sequence

`E_1^{p,q} = H^q(U_p, F_p)`

converging to `H^{p+q}(X, F)`.

Here `U = Y`, `X = T` and `a = b`; the proper hypercovering condition of Stacks Section 09XA is
`MorphismProperty.IsHypercovering properSurjective`. The spectral sequence is a functor of `F`,
its first page is identified with `H^q(U_p, F_p)` naturally in `F`, and it abuts to `H^n(X, F)`
(`SpectralSequence.AbutsTo`, the convergence of Stacks 01F2). -/
@[stacks 09XB]
def properHypercoveringSpectralSequence
    (hyp : MorphismProperty.IsHypercovering ProperHypercovering.properSurjective ⟨Y, T, b⟩) :
    ProperHypercoveringSpectralSequence Y T b :=
  let S := chosenQcSite Y T
  have hY : ∀ n, S.qcSite.Contains (Y.obj n) := fun n ↦
    chosenQcSite_contains Y T _ (Or.inl ⟨n, rfl⟩)
  have hT : S.qcSite.Contains T := chosenQcSite_contains Y T _ (Or.inr rfl)
  { sequence := qcHypercoverSpectralSequence S (qcLift S Y hY) (qcLiftAugmentation S b hY hT)
    pageOneIso p q := qcHypercoverSpectralSequencePageOneIso S _ _ p q
    abutsTo F := qcHypercoverSpectralSequence_abutsTo S
      (ProperHypercovering.isHypercoveringAugmentation_qcLift S b hyp hY hT) F }

end ProperHypercovering

end Stacks.Topology.Simplicial

end
