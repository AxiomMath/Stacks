module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.EtaleUnramified
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Diagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ElementaryDistinguishedSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FppfCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Unramified

/-!
# Separatedness detected by an elementary distinguished square

Let `g : X ⟶ Y` be a morphism of algebraic spaces over `S` and let `(U ⊆ X, f : V ⟶ X)` be an
elementary distinguished square. Then `g` is separated as soon as `U ⟶ Y` and `V ⟶ Y` are
separated and the two comparison maps `U ×_X V ⟶ U ×_Y V` and `V ×_X V ⟶ V ×_Y V` are closed.

The condition on `V ×_X V ⟶ V ×_Y V` cannot be dropped: for the affine line with doubled
origin over a field, mapping to a point, take `U` the common punctured line and `V` the
disjoint union of the two affine charts. This is an elementary distinguished square whose
`U ⟶ Y`, `V ⟶ Y` are separated and whose `U ×_X V ⟶ U ×_Y V` is a closed immersion, yet `X`
is not separated; the cross component of `V ×_X V ⟶ V ×_Y V` is the non-closed punctured
diagonal.

## Main results

* `AlgebraicGeometry.Space.isSeparated_of_elementaryDistinguishedSquare`: the criterion
  above.

## References

* [Stacks Project, Tag 0F45](https://stacks.math.columbia.edu/tag/0F45)
-/
@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe v' u' w u

namespace AlgebraicGeometry.Space

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_separatedFromElementarySquare
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_separatedFromElementarySquare
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_separatedFromElementarySquare (hS := hS)).has_limit _

local instance (priority := high) hasLimitsOfShape_discrete_presheaf_separatedFromElementarySquare
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (J : Type) :
    HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

section PullbackMap

variable {C : Type u'} [Category.{v'} C]

/-- The first projection of the map induced on fibre products by a morphism of bases. -/
private theorem mapDesc_comp_fst {X Y R T : C} (f : X ⟶ R) (g : Y ⟶ R) (i : R ⟶ T)
    [HasPullback f g] [HasPullback (f ≫ i) (g ≫ i)] :
    pullback.mapDesc f g i ≫ pullback.fst (f ≫ i) (g ≫ i) = pullback.fst f g := by
  rw [pullback.mapDesc, pullback.lift_fst, Category.comp_id]

/-- The second projection of the map induced on fibre products by a morphism of bases. -/
private theorem mapDesc_comp_snd {X Y R T : C} (f : X ⟶ R) (g : Y ⟶ R) (i : R ⟶ T)
    [HasPullback f g] [HasPullback (f ≫ i) (g ≫ i)] :
    pullback.mapDesc f g i ≫ pullback.snd (f ≫ i) (g ≫ i) = pullback.snd f g := by
  rw [pullback.mapDesc, pullback.lift_snd, Category.comp_id]

end PullbackMap

private theorem immersion_of_closedImmersion
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (m : F ⟶ G) (hm : IsClosedImmersion B S hS m) :
    IsImmersion B S hS m := by
  apply MorphismProperty.relative_monotone (P := MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsClosedImmersion.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)) _ m hm
  intro A C f hf
  let : AlgebraicGeometry.IsClosedImmersion
    ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f) := hf
  exact (inferInstance : AlgebraicGeometry.IsImmersion
    ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f))

private theorem immersion_comp_openImmersion
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G H : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (m : F ⟶ G) (n : G ⟶ H) (hm : IsImmersion B S hS m)
    (hn : IsOpenImmersion B S hS n) :
    IsImmersion B S hS (m ≫ n) := by
  have hn' : IsImmersion B S hS n := by
    apply MorphismProperty.relative_monotone (P := MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)) _ n hn
    intro A C f hf
    let : AlgebraicGeometry.IsOpenImmersion
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f) := hf
    exact (inferInstance : AlgebraicGeometry.IsImmersion
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f))
  let : MorphismProperty.IsStableUnderComposition
      (@AlgebraicGeometry.IsImmersion.{u}) := ⟨fun f g hf hg => by
        let := hf; let := hg; infer_instance⟩
  let : MorphismProperty.IsStableUnderComposition
      (MorphismProperty.inverseImage (@AlgebraicGeometry.IsImmersion.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  exact MorphismProperty.comp_mem (@IsImmersion B S hS) m n hm hn'

private theorem overlap_isImmersion
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X V Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hV : AlgebraicGeometry.IsAlgebraicSpace B S hS V)
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (U : Subfunctor X) (f : V ⟶ X) (g : X ⟶ Y)
    (hOpen : IsOpenSubspace B S hS U)
    (hSepU : AlgebraicGeometry.Space.IsSeparated B S hS (U.ι ≫ g)) :
    IsImmersion B S hS (pullback.mapDesc U.ι f g) := by
  let UObj : AlgebraicSpaces B S hS := ⟨U.toFunctor, hOpen.1⟩
  let VObj : AlgebraicSpaces B S hS := ⟨V, hV⟩
  let XObj : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let YObj : AlgebraicSpaces B S hS := ⟨Y, hY⟩
  let fObj : VObj ⟶ XObj := ObjectProperty.homMk f
  let iObj : UObj ⟶ XObj := ObjectProperty.homMk U.ι
  let PObj := AlgebraicSpaces.fiberProduct B S hS iObj fObj
  let P := pullback U.ι f
  let p : P ⟶ U.toFunctor := pullback.fst U.ι f
  let q : P ⟶ V := pullback.snd U.ι f
  let pObj : PObj ⟶ UObj := ObjectProperty.homMk (pullback.fst U.ι f)
  let qObj : PObj ⟶ VObj := ObjectProperty.homMk (pullback.snd U.ι f)
  have hP : IsPullback pObj qObj iObj fObj :=
    AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct B S hS iObj fObj
  let hObj : UObj ⟶ YObj := ObjectProperty.homMk (U.ι ≫ g)
  let gVObj : VObj ⟶ YObj := ObjectProperty.homMk (f ≫ g)
  let QObj := AlgebraicSpaces.fiberProduct B S hS hObj gVObj
  let h := U.ι ≫ g
  let hV := f ≫ g
  let T := pullback h (p ≫ h)
  let TObj : AlgebraicSpaces B S hS :=
    ⟨T, AlgebraicGeometry.isAlgebraicSpace_pullback B S hS h (p ≫ h)
      hOpen.1 PObj.property hY⟩
  let Q := pullback h hV
  let r : T ⟶ P := pullback.snd h (p ≫ h)
  let k : T ⟶ Q := pullback.map h (p ≫ h) h hV (𝟙 U.toFunctor) q (𝟙 Y)
    (by simp) (by
      dsimp [h, hV]
      simp only [Category.comp_id]
      calc
        p ≫ U.ι ≫ g = (p ≫ U.ι) ≫ g := by simp [Category.assoc]
        _ = (q ≫ f) ≫ g := by rw [show p ≫ U.ι = q ≫ f from pullback.condition]
        _ = q ≫ f ≫ g := by simp [Category.assoc])
  let rObj : TObj ⟶ PObj := ObjectProperty.homMk r
  let kObj : TObj ⟶ QObj := ObjectProperty.homMk k
  have hqOpen : IsOpenImmersion B S hS qObj.hom :=
    AlgebraicGeometry.Space.isOpenImmersion_of_isPullback B S hS hP hOpen.2
  have hkOpen : IsOpenImmersion B S hS kObj.hom := by
    have hsquareRaw : IsPullback r k q (pullback.snd h hV) := by
      apply IsPullback.mk'
      · exact (pullback.lift_snd _ _ _).symm
      · intro A a b ha hb
        apply pullback.hom_ext
        · have hkfst : k ≫ pullback.fst h hV = pullback.fst h (p ≫ h) :=
            (pullback.lift_fst _ _ _).trans (Category.comp_id _)
          simpa only [Category.assoc, hkfst] using
            congrArg (fun t => t ≫ pullback.fst h hV) hb
        · exact ha
      · intro A a b hrel
        have hbcond : b ≫ pullback.fst h hV ≫ h =
            b ≫ pullback.snd h hV ≫ hV := by
          calc
            b ≫ pullback.fst h hV ≫ h = (b ≫ pullback.fst h hV) ≫ h := by simp [Category.assoc]
            _ = (b ≫ pullback.snd h hV) ≫ hV := by
              simpa only [Category.assoc] using
                congrArg (fun t => b ≫ t) (pullback.condition (f := h) (g := hV))
            _ = b ≫ pullback.snd h hV ≫ hV := by simp [Category.assoc]
        have hEq : (b ≫ pullback.fst h hV) ≫ h = a ≫ p ≫ h := by
          calc
            b ≫ pullback.fst h hV ≫ h = b ≫ pullback.snd h hV ≫ hV := hbcond
            _ = a ≫ q ≫ hV := by
              simpa only [Category.assoc] using
                congrArg (fun t => t ≫ hV) hrel.symm
            _ = a ≫ p ≫ h := by
              dsimp [h, hV]
              calc
                a ≫ q ≫ f ≫ g = a ≫ (q ≫ f) ≫ g := by simp [Category.assoc]
                _ = a ≫ (p ≫ U.ι) ≫ g := by
                  simpa only [Category.assoc] using
                    congrArg (fun t => a ≫ t ≫ g)
                      (pullback.condition (f := U.ι) (g := f)).symm
                _ = a ≫ p ≫ U.ι ≫ g := by simp [Category.assoc]
        let l : A ⟶ T := pullback.lift (b ≫ pullback.fst h hV) a hEq
        have hl : l ≫ r = a := by
          simpa [l, r] using
            (pullback.lift_snd (b ≫ pullback.fst h hV) a hEq)
        have hl' : l ≫ pullback.snd h (p ≫ h) = a := by
          simpa [r] using hl
        refine ⟨l, ?_, ?_⟩
        · change l ≫ pullback.snd h (p ≫ h) = a
          exact hl
        · apply pullback.hom_ext
          · change l ≫ pullback.lift (pullback.fst h (p ≫ h))
              (pullback.snd h (p ≫ h) ≫ q) _ ≫ pullback.fst h hV =
                b ≫ pullback.fst h hV
            rw [pullback.lift_fst, pullback.lift_fst]
          · calc
              l ≫ k ≫ pullback.snd h hV = a ≫ q := by
                change l ≫ pullback.lift (pullback.fst h (p ≫ h))
                  (pullback.snd h (p ≫ h) ≫ q) _ ≫ pullback.snd h hV = a ≫ q
                calc
                  l ≫ pullback.lift (pullback.fst h (p ≫ h))
                      (pullback.snd h (p ≫ h) ≫ q) _ ≫ pullback.snd h hV =
                      l ≫ pullback.snd h (p ≫ h) ≫ q := by
                        rw [pullback.lift_snd]
                  _ = a ≫ q := by
                    rw [← Category.assoc, hl']
              _ = b ≫ pullback.snd h hV := hrel
    have hsquare : IsPullback rObj kObj qObj
        (ObjectProperty.homMk (pullback.snd h hV)) := by
      apply IsPullback.of_map (ObjectProperty.ι _)
      · exact ObjectProperty.hom_ext _ hsquareRaw.w
      · exact hsquareRaw
    exact AlgebraicGeometry.Space.isOpenImmersion_of_isPullback B S hS hsquare hqOpen
  let R := pullback (𝟙 U.toFunctor) p
  let eHom : P ⟶ R := pullback.lift p (𝟙 P) (by simp)
  let eInv : R ⟶ P := pullback.snd (𝟙 U.toFunctor) p
  have hefst : eHom ≫ pullback.fst (𝟙 U.toFunctor) p = p :=
    pullback.lift_fst p (𝟙 P) (by simp)
  have hesnd : eHom ≫ pullback.snd (𝟙 U.toFunctor) p = 𝟙 P :=
    pullback.lift_snd p (𝟙 P) (by simp)
  have he : eHom ≫ eInv = 𝟙 P ∧ eInv ≫ eHom = 𝟙 R := by
    refine ⟨hesnd, pullback.hom_ext ?_ ?_⟩
    · rw [Category.assoc, hefst, Category.id_comp]
      exact (pullback.condition (f := 𝟙 U.toFunctor) (g := p)).symm.trans (Category.comp_id _)
    · rw [Category.assoc, hesnd, Category.comp_id, Category.id_comp]
  let d : R ⟶ T := pullback.mapDesc (𝟙 U.toFunctor) p h
  have hdClosed : IsClosedImmersion B S hS d :=
    AlgebraicGeometry.Space.isClosedImmersion_mapDesc B S hS (𝟙 U.toFunctor) p h hSepU
  have hfactor : pullback.mapDesc U.ι f g = eHom ≫ d ≫ k := by
    have hmfst : pullback.mapDesc U.ι f g ≫ pullback.fst h hV = p :=
      mapDesc_comp_fst U.ι f g
    have hmsnd : pullback.mapDesc U.ι f g ≫ pullback.snd h hV = q :=
      mapDesc_comp_snd U.ι f g
    have hdfst : d ≫ pullback.fst h (p ≫ h) = pullback.fst (𝟙 U.toFunctor) p :=
      mapDesc_comp_fst (𝟙 U.toFunctor) p h
    have hdsnd : d ≫ pullback.snd h (p ≫ h) = pullback.snd (𝟙 U.toFunctor) p :=
      mapDesc_comp_snd (𝟙 U.toFunctor) p h
    have hkfst : k ≫ pullback.fst h hV = pullback.fst h (p ≫ h) :=
      (pullback.lift_fst _ _ _).trans (Category.comp_id _)
    have hksnd : k ≫ pullback.snd h hV = pullback.snd h (p ≫ h) ≫ q :=
      pullback.lift_snd _ _ _
    apply pullback.hom_ext
    · calc
        pullback.mapDesc U.ι f g ≫ pullback.fst h hV = p := hmfst
        _ = eHom ≫ d ≫ k ≫ pullback.fst h hV := by
          calc
            p = eHom ≫ pullback.fst (𝟙 U.toFunctor) p := hefst.symm
            _ = eHom ≫ (d ≫ pullback.fst h (p ≫ h)) :=
              congrArg (fun t => eHom ≫ t) hdfst.symm
            _ = eHom ≫ d ≫ (k ≫ pullback.fst h hV) :=
              congrArg (fun t => eHom ≫ d ≫ t) hkfst.symm
            _ = eHom ≫ d ≫ k ≫ pullback.fst h hV := by simp []
    · calc
        pullback.mapDesc U.ι f g ≫ pullback.snd h hV = q := hmsnd
        _ = eHom ≫ d ≫ k ≫ pullback.snd h hV := by
          calc
            q = 𝟙 P ≫ q := by simp
            _ = (eHom ≫ pullback.snd (𝟙 U.toFunctor) p) ≫ q := by rw [hesnd]
            _ = (eHom ≫ (d ≫ pullback.snd h (p ≫ h))) ≫ q :=
              congrArg (fun t => eHom ≫ t ≫ q) hdsnd.symm
            _ = eHom ≫ d ≫ (pullback.snd h (p ≫ h) ≫ q) := by simp [Category.assoc]
            _ = eHom ≫ d ≫ (k ≫ pullback.snd h hV) :=
              congrArg (fun t => eHom ≫ d ≫ t) hksnd.symm
            _ = eHom ≫ d ≫ k ≫ pullback.snd h hV := by simp []
  rw [hfactor]
  have hdk : IsImmersion B S hS (d ≫ k) :=
    immersion_comp_openImmersion B S hS d k (immersion_of_closedImmersion B S hS d hdClosed) hkOpen
  have hSepIso : IsImmersion B S hS (eHom ≫ (d ≫ k)) := by
    have : IsIso eHom := ⟨eInv, he.1, he.2⟩
    exact (MorphismProperty.cancel_left_of_respectsIso
      (@IsImmersion B S hS) eHom (d ≫ k)).2 hdk
  simpa [Category.assoc] using hSepIso

private theorem closedImmersion_of_isImmersion_and_isClosed
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (_hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G)
    (m : F ⟶ G) (hm : IsImmersion B S hS m)
    (hclosed : IsClosedMorphism B S hS m) :
    IsClosedImmersion B S hS m := by
  apply (AlgebraicGeometry.Space.isClosedImmersion_iff_isClosed_range_pointsMap
    B S hS hG m hm).2
  let : TopologicalSpace (AlgebraicGeometry.Space.points B S hS F) :=
    pointTopology B S hS F
  let : TopologicalSpace (AlgebraicGeometry.Space.points B S hS G) :=
    pointTopology B S hS G
  change IsClosedMap (pointsMap B S hS F m) at hclosed
  simpa using hclosed Set.univ isClosed_univ

private theorem mapDesc_isClosedImmersion_of_mono
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U X Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (i : U ⟶ X) [Mono i] (g : X ⟶ Y)
    (hsep : AlgebraicGeometry.Space.IsSeparated B S hS (i ≫ g)) :
    IsClosedImmersion B S hS (pullback.mapDesc i i g) := by
  let δ := pullback.diagonal i
  have : IsIso δ := (pullback.isIso_diagonal_iff i).2 inferInstance
  have hdiag : δ ≫ pullback.mapDesc i i g = pullback.diagonal (i ≫ g) := by
    apply pullback.hom_ext
    · simp [δ, Category.assoc,
        pullback.lift_fst, pullback.diagonal_fst]
    · simp [δ, Category.assoc,
        pullback.lift_snd, pullback.diagonal_snd]
  have hcomp : IsClosedImmersion B S hS
      (δ ≫ pullback.mapDesc i i g) := by
    rw [hdiag]
    exact hsep
  exact (MorphismProperty.cancel_left_of_respectsIso
    (P := @IsClosedImmersion B S hS) δ (pullback.mapDesc i i g)).1 hcomp

private theorem pointsMap_comp_eq
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G H : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (α : F ⟶ G) (β : G ⟶ H) (x : AlgebraicGeometry.Space.points B S hS F) :
    pointsMap B S hS G β (pointsMap B S hS F α x) =
      pointsMap B S hS F (α ≫ β) x :=
  (congrFun (pointsMap_comp B S hS F α β) x).symm

private theorem pointsMap_id_eq
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (x : AlgebraicGeometry.Space.points B S hS F) :
    pointsMap B S hS F (𝟙 F) x = x :=
  congrFun (pointsMap_id B S hS F) x

private theorem etalePresheaf_comp
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : (MorphismProperty.presheaf
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS))) f)
    (hg : (MorphismProperty.presheaf
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS))) g) :
    (MorphismProperty.presheaf
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS))) (f ≫ g) := by
  let Q := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let Qp := Q.presheaf
  let : MorphismProperty.IsStableUnderComposition
      (@Etale.{u} : MorphismProperty Scheme.{u}) := by
    constructor
    intro A C D m n hm hn
    let : Etale m := hm
    let : Etale n := hn
    exact Etale.etale_comp m n
  let : Q.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let : Qp.IsStableUnderComposition := MorphismProperty.relative_isStableUnderComposition Q
  exact MorphismProperty.comp_mem Qp f g hf hg

private theorem etalePresheaf_of_iso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : X ≅ Y) :
    (MorphismProperty.presheaf
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS))) e.inv := by
  let Tsch := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let Q := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) Tsch
  let Qp := Q.presheaf
  let : MorphismProperty.IsStableUnderComposition
      (@Etale.{u} : MorphismProperty Scheme.{u}) := by
    constructor
    intro A C D m n hm hn
    let : Etale m := hm
    let : Etale n := hn
    exact Etale.etale_comp m n
  let : MorphismProperty.IsMultiplicative (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    inferInstance
  let : Q.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage Tsch
  let : MorphismProperty.RespectsIso (@Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let : Q.RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  let : Qp.IsStableUnderComposition := MorphismProperty.relative_isStableUnderComposition Q
  let : Q.ContainsIdentities := by
    refine ⟨?_⟩
    intro A
    show Etale (Tsch.map (𝟙 A))
    simpa using (show Etale (𝟙 (Tsch.obj A)) from inferInstance)
  let : Q.IsMultiplicative := ⟨⟩
  let : Qp.IsMultiplicative := MorphismProperty.relative_isMultiplicative Q
  let : Qp.RespectsIso := inferInstance
  exact MorphismProperty.RespectsIso.postcomp Qp e.inv (𝟙 Y) (Qp.id_mem _)

private theorem point_lift_of_isIso_preimage
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W V : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (D : Subfunctor W) (f : V ⟶ W)
    (x : AlgebraicGeometry.Space.points B S hS W)
    (hx : x ∈ Set.range (pointsMap B S hS D.toFunctor D.ι))
    (his : IsIso (D.fromPreimage f)) :
    ∃ y : AlgebraicGeometry.Space.points B S hS V,
      pointsMap B S hS V f y = x := by
  obtain ⟨z, rfl⟩ := hx
  have := his
  obtain ⟨p, hp⟩ :=
    pointsMap_surjective_of_isIso B S hS (D.fromPreimage f) z
  refine ⟨pointsMap B S hS (D.preimage f).toFunctor
    (D.preimage f).ι p, ?_⟩
  calc
    pointsMap B S hS V f
        (pointsMap B S hS (D.preimage f).toFunctor
          (D.preimage f).ι p) =
        pointsMap B S hS (D.preimage f).toFunctor
          ((D.preimage f).ι ≫ f) p :=
      pointsMap_comp_eq B S hS (D.preimage f).ι f p
    _ = pointsMap B S hS (D.preimage f).toFunctor
          (D.fromPreimage f ≫ D.ι) p := by rw [Subfunctor.fromPreimage_ι]
    _ = pointsMap B S hS D.toFunctor D.ι
          (pointsMap B S hS (D.preimage f).toFunctor
            (D.fromPreimage f) p) :=
      (pointsMap_comp_eq B S hS (D.fromPreimage f) D.ι p).symm
    _ = pointsMap B S hS D.toFunctor D.ι z := by rw [hp]

private theorem points_covered_by_open_or_etale
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W V : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : AlgebraicGeometry.IsAlgebraicSpace B S hS W)
    (U : Subfunctor W) (f : V ⟶ W)
    (h : AlgebraicGeometry.Space.IsElementaryDistinguishedSquare B S hS hW U f)
    (x : AlgebraicGeometry.Space.points B S hS W) :
    x ∈ Set.range (pointsMap B S hS U.toFunctor U.ι) ∨
      ∃ y : AlgebraicGeometry.Space.points B S hS V,
        pointsMap B S hS V f y = x := by
  classical
  by_cases hx : x ∈ Set.range (pointsMap B S hS U.toFunctor U.ι)
  · exact Or.inl hx
  · right
    let D := reducedClosedSubspace B S hS W hW
      (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ
      h.isClosedComplement
    have hxD : x ∈ Set.range (pointsMap B S hS D.toFunctor D.ι) := by
      rw [range_pointsMap_ι_reducedClosedSubspace B S hS W hW _ h.isClosedComplement]
      exact hx
    exact point_lift_of_isIso_preimage B S hS D f x hxD h.isIsoOverComplement


private theorem elementarySquare_etaleCovering
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X V : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (U : Subfunctor X) (f : V ⟶ X)
    (h : AlgebraicGeometry.Space.IsElementaryDistinguishedSquare B S hS hX U f) :
    AlgebraicGeometry.Space.IsEtaleCovering B S hS
      (fun | false => U.toFunctor | true => V)
      (fun | false => U.ι | true => f) := by
  classical
  refine ⟨hX, ?_, ?_, ?_⟩
  · intro i
    cases i <;> simp only []
    · exact h.isOpenSubspace.1
    · exact h.isAlgebraicSpace
  · intro i
    cases i <;> simp only []
    · exact isEtale_of_isOpenImmersion B S hS h.isOpenSubspace.2
    · exact h.isEtale
  · apply Set.eq_univ_iff_forall.mpr
    intro x
    obtain hx | ⟨y, hy⟩ := points_covered_by_open_or_etale B S hS hX U f h x
    · obtain ⟨z, hz⟩ := hx
      exact Set.mem_iUnion.mpr ⟨false, ⟨z, hz⟩⟩
    · exact Set.mem_iUnion.mpr ⟨true, ⟨y, by simpa using hy⟩⟩

private theorem overlap_swap_closedImmersion
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y U V : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (iU : U ⟶ X) (iV : V ⟶ X) (g : X ⟶ Y)
    (hUV : IsClosedImmersion B S hS
      (pullback.mapDesc iU iV g)) :
    IsClosedImmersion B S hS (pullback.mapDesc iV iU g) := by
  let P := MorphismProperty.presheaf
    (MorphismProperty.inverseImage (@AlgebraicGeometry.IsClosedImmersion)
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS))
  let e : Arrow.mk (pullback.mapDesc iV iU g) ≅
      Arrow.mk (pullback.mapDesc iU iV g) := by
    refine Arrow.isoMk (pullbackSymmetry iV iU)
      (pullbackSymmetry (iV ≫ g) (iU ≫ g)) ?_
    show (pullbackSymmetry iV iU).hom ≫ pullback.mapDesc iU iV g =
      pullback.mapDesc iV iU g ≫
        (pullbackSymmetry (iV ≫ g) (iU ≫ g)).hom
    apply pullback.hom_ext <;>
      simp [pullback.lift_fst, pullback.lift_snd,
        pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd]
  show P (pullback.mapDesc iV iU g)
  exact (MorphismProperty.arrow_mk_iso_iff (P := P) e).mpr hUV

private theorem point_lift_of_equal_points
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G H : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ H) (g : G ⟶ H)
    (x : AlgebraicGeometry.Space.points B S hS F) (y : AlgebraicGeometry.Space.points B S hS G)
    (hxy : pointsMap B S hS F f x =
      pointsMap B S hS G g y) :
    ∃ z : AlgebraicGeometry.Space.points B S hS (pullback f g),
      pointsMap B S hS (pullback f g) (pullback.fst f g) z = x ∧
      pointsMap B S hS (pullback f g) (pullback.snd f g) z = y := by
  revert x y hxy
  intro x
  refine Quot.inductionOn x ?_
  intro p y
  refine Quot.inductionOn y ?_
  intro q hxy
  have hclasses :
      (FieldValuedPoint.map B S hS F f p).class B S hS H =
        (FieldValuedPoint.map B S hS G g q).class B S hS H := by
    simpa only [pointsMap_class] using hxy
  obtain ⟨r, ⟨eF, heF⟩, ⟨eG, heG⟩⟩ :=
    (AlgebraicGeometry.Space.FieldValuedPoint.class_eq_class_iff B S hS H _ _).mp hclasses
  let p' : FieldValuedPoint B S hS F :=
    { carrier := r.carrier, field := r.field, contained := r.contained,
      toBase := r.toBase, value := F.map eF.op p.value }
  let q' : FieldValuedPoint B S hS G :=
    { carrier := r.carrier, field := r.field, contained := r.contained,
      toBase := r.toBase, value := G.map eG.op q.value }
  have hval : f.app (Opposite.op r.siteObject) p'.value =
      g.app (Opposite.op r.siteObject) q'.value := by
    show f.app _ (F.map eF.op p.value) = g.app _ (G.map eG.op q.value)
    calc
      f.app _ (F.map eF.op p.value) = H.map eF.op (f.app _ p.value) :=
        congrArg (fun k => k p.value) (f.naturality eF.op)
      _ = r.value := heF
      _ = H.map eG.op (g.app _ q.value) := heG.symm
      _ = g.app _ (G.map eG.op q.value) :=
        (congrArg (fun k => k q.value) (g.naturality eG.op)).symm
  have hpb : IsPullback (pullback.fst f g) (pullback.snd f g) f g :=
    IsPullback.of_hasPullback f g
  let c : yoneda.obj r.siteObject ⟶ pullback f g :=
    hpb.lift (yonedaEquiv.symm p'.value) (yonedaEquiv.symm q'.value) (by
      apply yonedaEquiv.injective
      simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply] using hval)
  let z : FieldValuedPoint B S hS (pullback f g) :=
    { carrier := r.carrier, field := r.field, contained := r.contained,
      toBase := r.toBase, value := yonedaEquiv c }
  refine ⟨z.class B S hS (pullback f g), ?_, ?_⟩
  · rw [pointsMap_class]
    have hv : (FieldValuedPoint.map B S hS (pullback f g)
        (pullback.fst f g) z).value = p'.value := by
      show (pullback.fst f g).app _ (yonedaEquiv c) = p'.value
      rw [← yonedaEquiv_comp]
      rw [← Equiv.apply_symm_apply yonedaEquiv p'.value]
      apply congrArg yonedaEquiv
      simp only [c, IsPullback.lift_fst]
    apply Quot.sound
    refine ⟨FieldValuedPoint.map B S hS (pullback f g)
      (pullback.fst f g) z,
      FieldValuedPoint.dominates_refl B S hS F _, ?_⟩
    have hsite : FieldValuedPoint.siteObject B S hS F
        (FieldValuedPoint.map B S hS (pullback f g)
          (pullback.fst f g) z) = FieldValuedPoint.siteObject B S hS H r := rfl
    cases hsite
    refine ⟨eF, ?_⟩
    rw [hv]
    rfl
  · rw [pointsMap_class]
    have hv : (FieldValuedPoint.map B S hS (pullback f g)
        (pullback.snd f g) z).value = q'.value := by
      show (pullback.snd f g).app _ (yonedaEquiv c) = q'.value
      rw [← yonedaEquiv_comp]
      rw [← Equiv.apply_symm_apply yonedaEquiv q'.value]
      apply congrArg yonedaEquiv
      simp only [c, IsPullback.lift_snd]
    apply Quot.sound
    refine ⟨FieldValuedPoint.map B S hS (pullback f g)
      (pullback.snd f g) z,
      FieldValuedPoint.dominates_refl B S hS G _, ?_⟩
    have hsite : FieldValuedPoint.siteObject B S hS G
        (FieldValuedPoint.map B S hS (pullback f g)
          (pullback.snd f g) z) = FieldValuedPoint.siteObject B S hS H r := rfl
    cases hsite
    refine ⟨eG, ?_⟩
    rw [hv]
    rfl

private theorem overlap_points_covered_by_diagonal_or_open
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W V : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : AlgebraicGeometry.IsAlgebraicSpace B S hS W)
    (U : Subfunctor W) (f : V ⟶ W)
    (h : AlgebraicGeometry.Space.IsElementaryDistinguishedSquare B S hS hW U f)
    (x : AlgebraicGeometry.Space.points B S hS (pullback f f)) :
    x ∈ Set.range (pointsMap B S hS V (pullback.diagonal f)) ∨
      x ∈ Set.range (pointsMap B S hS (pullback U.ι (pullback.fst f f ≫ f))
        (pullback.snd U.ι (pullback.fst f f ≫ f))) := by
  classical
  let q := pullback.fst f f ≫ f
  let y := pointsMap B S hS (pullback f f) q x
  by_cases hy : y ∈ Set.range (pointsMap B S hS U.toFunctor U.ι)
  · obtain ⟨z, hz⟩ := hy
    obtain ⟨t, _, ht⟩ := point_lift_of_equal_points B S hS U.ι q z x hz
    exact Or.inr ⟨t, ht⟩
  · let D := reducedClosedSubspace B S hS W hW
      (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ
      h.isClosedComplement
    have hyD : y ∈ Set.range (pointsMap B S hS D.toFunctor D.ι) := by
      rw [range_pointsMap_ι_reducedClosedSubspace B S hS W hW _ h.isClosedComplement]
      exact hy
    obtain ⟨d, hd⟩ := hyD
    obtain ⟨t, _, ht⟩ := point_lift_of_equal_points B S hS D.ι q d x hd
    let sD := pullback.fst D.ι q
    let sR := pullback.snd D.ι q
    let a₁ := sR ≫ pullback.fst f f
    let a₂ := sR ≫ pullback.snd f f
    have h₁ : sD ≫ D.ι = a₁ ≫ f := by
      dsimp [a₁, sD, sR]
      simpa [q, Category.assoc] using
        (pullback.condition (f := D.ι) (g := q))
    have h₂ : sD ≫ D.ι = a₂ ≫ f := by
      dsimp [a₂, sD, sR, q]
      simp only [Category.assoc, pullback.condition]
    let E := D.preimage f
    have hE := CategoryTheory.Subfunctor.isPullback_preimage f D
    let l₁ := hE.lift sD a₁ h₁
    let l₂ := hE.lift sD a₂ h₂
    let : IsIso (D.fromPreimage f) := h.isIsoOverComplement
    have hl₁ : l₁ ≫ D.fromPreimage f = sD := by simp [l₁]
    have hl₂ : l₂ ≫ D.fromPreimage f = sD := by simp [l₂]
    have hs₁ : l₁ ≫ E.ι = a₁ := hE.lift_snd sD a₁ h₁
    have hs₂ : l₂ ≫ E.ι = a₂ := hE.lift_snd sD a₂ h₂
    have hl : l₁ = l₂ := by
      apply (cancel_mono (D.fromPreimage f)).1
      rw [hl₁, hl₂]
    have ha : a₁ = a₂ := by
      calc
        a₁ = l₁ ≫ E.ι := hs₁.symm
        _ = l₂ ≫ E.ι := by rw [hl]
        _ = a₂ := hs₂
    have hsR : sR = a₁ ≫ pullback.diagonal f := by
      apply pullback.hom_ext
      · simp [a₁, Category.assoc]
      · simpa [a₁, a₂, Category.assoc] using ha.symm
    have hx :
        pointsMap B S hS V (pullback.diagonal f)
          (pointsMap B S hS _ a₁ t) = x := by
      calc
        pointsMap B S hS V (pullback.diagonal f)
            (pointsMap B S hS _ a₁ t) =
            pointsMap B S hS _ (a₁ ≫ pullback.diagonal f) t :=
          pointsMap_comp_eq B S hS a₁ (pullback.diagonal f) t
        _ = pointsMap B S hS _ sR t := by rw [hsR]
        _ = x := ht
    exact Or.inl ⟨pointsMap B S hS _ a₁ t, hx⟩


private theorem closedImmersion_of_etaleCovering
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G) (m : F ⟶ G)
    {I : Type u} (T : I → (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (t : ∀ i, T i ⟶ G) (hc : AlgebraicGeometry.Space.IsEtaleCovering B S hS T t)
    (hm : ∀ i, IsClosedImmersion B S hS (pullback.snd m (t i))) :
    IsClosedImmersion B S hS m := by
  let C := AlgebraicSpaces B S hS
  let F₀ : C := ⟨F, hF⟩
  let G₀ : C := ⟨G, hG⟩
  let m₀ : F₀ ⟶ G₀ := ObjectProperty.homMk m
  let T₀ (i : I) : C := ⟨T i, hc.source_isAlgebraicSpace i⟩
  let t₀ (i : I) : T₀ i ⟶ G₀ := ObjectProperty.homMk (t i)
  let K := AlgebraicGeometry.Space.Topology.precoverage.{u, u} .fpqc B S hS
  let P : MorphismProperty C := fun _ _ f => IsClosedImmersion B S hS f.hom
  have hmem : Presieve.ofArrows T₀ t₀ ∈ K G₀ :=
    ⟨I, T₀, t₀, rfl, hG, hc.source_isAlgebraicSpace,
      AlgebraicGeometry.Space.isFpqcCovering_of_isEtaleCovering B S hS T t hc⟩
  let E : Precoverage.ZeroHypercover.{u} K G₀ :=
    ⟨{ I₀ := I, X := T₀, f := t₀ }, hmem⟩
  let : P.IsLocalAtTarget K := isClosedImmersion_isLocalAtTarget_fpqc B S hS
  show P m₀
  rw [MorphismProperty.IsLocalAtTarget.iff_of_zeroHypercover (P := P) E]
  intro i
  have sq := AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct B S hS m₀ (t₀ i)
  let : P.RespectsIso := MorphismProperty.RespectsIso.inverseImage
    (@IsClosedImmersion B S hS) (ObjectProperty.ι _)
  rw [← P.cancel_left_of_respectsIso sq.isoPullback.hom, sq.isoPullback_hom_snd]
  exact hm i

private theorem mono_of_openImmersion
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (m : F ⟶ G) (hm : IsOpenImmersion B S hS m) : Mono m := by
  apply MorphismProperty.presheaf_monomorphisms_le_monomorphisms _
  apply MorphismProperty.relative_monotone (P := MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsOpenImmersion.{u}) (AlgebraicGeometry.BigFppfOver.toScheme B S hS)) _ m hm
  intro A C f hf
  exact Functor.mono_of_mono_map (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
    (AlgebraicGeometry.IsOpenImmersion.le_monomorphisms _ hf)

private theorem lift_of_openImmersion_of_range_subset
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G H : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G)
    (hH : AlgebraicGeometry.IsAlgebraicSpace B S hS H)
    (r : F ⟶ G) (hr : IsOpenImmersion B S hS r) (m : H ⟶ G)
    (hm : Set.range (pointsMap B S hS H m) ⊆
      Set.range (pointsMap B S hS F r)) :
    ∃ l : H ⟶ F, l ≫ r = m := by
  let : Mono r := mono_of_openImmersion B S hS r hr
  let D := Subfunctor.range r
  let e : F ≅ D.toFunctor := asIso (Subfunctor.toRange r)
  have he : e.hom ≫ D.ι = r := Subfunctor.toRange_ι r
  have hD : IsOpenSubspace B S hS D := by
    refine ⟨isAlgebraicSpace_of_iso B S hS e hF, ?_⟩
    rw [← MorphismProperty.cancel_left_of_respectsIso
      (@IsOpenImmersion B S hS) e.hom D.ι, he]
    exact hr
  have hmD : Set.range (pointsMap B S hS H m) ⊆
      Set.range (pointsMap B S hS D.toFunctor D.ι) := by
    intro x hx
    obtain ⟨y, rfl⟩ := hm hx
    refine ⟨pointsMap B S hS F e.hom y, ?_⟩
    rw [pointsMap_comp_eq, he]
  obtain ⟨l, hl⟩ := (AlgebraicGeometry.Space.factorsThrough_openSubspace_iff_points
    B S hS hG hH D hD m).2 hmD
  refine ⟨l ≫ e.inv, ?_⟩
  rw [Category.assoc, ← he, e.inv_hom_id_assoc, hl]

attribute [local instance] MorphismProperty.relative_isStableUnderBaseChange

private theorem closedImmersion_of_closed_of_openCover
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G) (m : F ⟶ G) [Mono m]
    (hm : IsClosedMorphism B S hS m)
    {I : Type u} [Nonempty I]
    (A : I → (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hA : ∀ i, AlgebraicGeometry.IsAlgebraicSpace B S hS (A i))
    (r : ∀ i, A i ⟶ F) (hr : ∀ i, IsOpenImmersion B S hS (r i))
    (hc : ∀ x : AlgebraicGeometry.Space.points B S hS F,
      ∃ i, x ∈ Set.range (pointsMap B S hS (A i) (r i)))
    (hi : ∀ i, IsImmersion B S hS (r i ≫ m)) :
    IsClosedImmersion B S hS m := by
  classical
  let : TopologicalSpace (AlgebraicGeometry.Space.points B S hS F) :=
    pointTopology B S hS F
  let : TopologicalSpace (AlgebraicGeometry.Space.points B S hS G) :=
    pointTopology B S hS G
  let q := pointsMap B S hS F m
  let a (i : I) := Set.range (pointsMap B S hS (A i) (r i))
  have ha (i : I) : IsOpen (a i) := by
    let : TopologicalSpace (AlgebraicGeometry.Space.points B S hS (A i)) :=
      pointTopology B S hS (A i)
    have h := AlgebraicGeometry.Space.isOpenMap_pointsMap_of_isEtale B S hS (r i) (hA i) hF
      (isEtale_of_isOpenImmersion B S hS (hr i))
    simpa [a] using h Set.univ isOpen_univ
  have hq : IsClosedMap q := hm
  have hqi : Function.Injective q := pointsMap_injective_of_mono B S hS m
  let O (i : I) : TopologicalSpace.Opens (AlgebraicGeometry.Space.points B S hS G) :=
    ⟨(q '' (a i)ᶜ)ᶜ, (hq _ (ha i).isClosed_compl).isOpen_compl⟩
  let D (i : I) := (openSubspacesOrderIso B S hS G hG).symm (O i)
  have hD (i : I) : Set.range
      (pointsMap B S hS (D i).1.toFunctor (D i).1.ι) = (O i).1 := by
    rw [← AlgebraicGeometry.Space.openSubspacesOrderIso_apply]
    exact congrArg (fun T => T.1)
      ((openSubspacesOrderIso B S hS G hG).apply_symm_apply (O i))
  have hcover : AlgebraicGeometry.Space.IsEtaleCovering B S hS
      (fun i => (D i).1.toFunctor) (fun i => (D i).1.ι) := by
    refine ⟨hG, fun i => (D i).2.1, fun i =>
      isEtale_of_isOpenImmersion B S hS (D i).2.2, ?_⟩
    apply Set.eq_univ_iff_forall.mpr
    intro y
    by_cases hy : y ∈ Set.range q
    · obtain ⟨x, rfl⟩ := hy
      obtain ⟨i, hx⟩ := hc x
      apply Set.mem_iUnion.mpr
      refine ⟨i, (hD i).symm ▸ ?_⟩
      show q x ∉ q '' (a i)ᶜ
      rintro ⟨z, hz, he⟩
      exact hz (hqi he ▸ hx)
    · obtain ⟨i⟩ := ‹Nonempty I›
      apply Set.mem_iUnion.mpr
      refine ⟨i, (hD i).symm ▸ ?_⟩
      exact fun ⟨x, _, hx⟩ => hy ⟨x, hx⟩
  apply closedImmersion_of_etaleCovering B S hS hF hG m _ _ hcover
  intro i
  let t := (D i).1.ι
  let P := pullback m t
  have hP := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS m t hF (D i).2.1 hG
  let p : P ⟶ F := pullback.fst m t
  let s : P ⟶ (D i).1.toFunctor := pullback.snd m t
  have hpm : p ≫ m = s ≫ t := pullback.condition
  have hsubset : Set.range (pointsMap B S hS P p) ⊆ a i := by
    rintro _ ⟨x, rfl⟩
    have hx : q (pointsMap B S hS P p x) ∈ (O i).1 := by
      rw [show q (pointsMap B S hS P p x) =
        pointsMap B S hS (D i).1.toFunctor t
          (pointsMap B S hS P s x) from by
            dsimp [q]; rw [pointsMap_comp_eq, hpm, ← pointsMap_comp_eq]]
      rw [← hD]
      exact Set.mem_range_self _
    by_contra hn
    exact hx ⟨_, hn, rfl⟩
  obtain ⟨l, hl⟩ := lift_of_openImmersion_of_range_subset B S hS
    (hA i) hF hP (r i) (hr i) p hsubset
  have : Mono (r i) := mono_of_openImmersion B S hS (r i) (hr i)
  have sq : IsPullback l s (r i ≫ m) t := by
    apply IsPullback.mk'
    · rw [← Category.assoc, hl, hpm]
    · intro Z x y hx hy
      apply pullback.hom_ext
      · show x ≫ p = y ≫ p
        rw [← hl, ← Category.assoc, ← Category.assoc, hx]
      · exact hy
    · intro Z x y hxy
      let z := pullback.lift (x ≫ r i) y (by simpa [Category.assoc] using hxy)
      refine ⟨z, ?_, ?_⟩
      · apply (cancel_mono (r i)).1
        rw [Category.assoc, hl]
        exact pullback.lift_fst _ _ _
      · exact pullback.lift_snd _ _ _
  have hs : IsImmersion B S hS s :=
    MorphismProperty.of_isPullback sq (hi i)
  apply (AlgebraicGeometry.Space.isClosedImmersion_iff_isClosed_range_pointsMap
    B S hS (D i).2.1 s hs).2
  let : TopologicalSpace (AlgebraicGeometry.Space.points B S hS (D i).1.toFunctor) :=
    pointTopology B S hS _
  have hrange : Set.range (pointsMap B S hS P s) =
      pointsMap B S hS (D i).1.toFunctor t ⁻¹' Set.range q := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨pointsMap B S hS P p x, ?_⟩
      dsimp [q]
      rw [pointsMap_comp_eq, hpm, ← pointsMap_comp_eq]
    · rintro ⟨x, hx⟩
      obtain ⟨z, _, hz⟩ := point_lift_of_equal_points B S hS m t x y hx
      exact ⟨z, hz⟩
  rw [hrange]
  exact hq.isClosed_range.preimage
    ((pointTopologyFamily B S hS).continuous (D i).2.1 hG t)

attribute [local simp] pullback.lift_fst pullback.lift_snd
  pullback.lift_fst_assoc pullback.lift_snd_assoc

private theorem selfOverlap_openPart_isImmersion
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U X V Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (i : U ⟶ X) (f : V ⟶ X) (g : X ⟶ Y)
    (hi : IsOpenImmersion B S hS i)
    (hc : IsClosedImmersion B S hS (pullback.mapDesc i f g)) :
    IsImmersion B S hS
      (pullback.snd i (pullback.fst f f ≫ f) ≫ pullback.mapDesc f f g) := by
  let m := pullback.mapDesc f f g
  let q := pullback.fst f f ≫ f
  let q' := pullback.fst (f ≫ g) (f ≫ g) ≫ f
  let T := pullback i q
  let N := pullback i q'
  have hm : m ≫ q' = q := by simp only [m, q, q', Category.comp_id, pullback.lift_fst_assoc,
      pullback.condition]
  let j : T ⟶ N := pullback.lift (pullback.fst i q)
    (pullback.snd i q ≫ m) (by
      rw [Category.assoc, hm]; exact pullback.condition)
  let c : T ⟶ pullback i f := pullback.lift (pullback.fst i q)
    (pullback.snd i q ≫ pullback.snd f f) (by
      rw [Category.assoc, ← pullback.condition]
      exact pullback.condition)
  let d : N ⟶ pullback (i ≫ g) (f ≫ g) :=
    pullback.lift (pullback.fst i q')
      (pullback.snd i q' ≫ pullback.snd (f ≫ g) (f ≫ g)) (by
        calc
          pullback.fst i q' ≫ i ≫ g = pullback.snd i q' ≫ q' ≫ g := by
            rw [← Category.assoc, pullback.condition, Category.assoc]
          _ = _ := by dsimp [q']; simp only [Category.assoc, pullback.condition])
  have sq : IsPullback c j (pullback.mapDesc i f g) d := by
    apply IsPullback.mk'
    · apply pullback.hom_ext <;>
        simp only [c, j, d, m, Category.assoc, Category.comp_id, pullback.lift_fst,
            pullback.lift_snd, pullback.lift_snd_assoc]
    · intro Z x y hx hy
      apply pullback.hom_ext
      · have h := congrArg (fun a => a ≫ pullback.fst i q') hy
        simpa only [j, Category.assoc, Category.comp_id, Category.id_comp, pullback.lift_fst,
            pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc,
            pullback.condition] using h
      · apply (cancel_mono m).1
        have h := congrArg (fun a => a ≫ pullback.snd i q') hy
        simpa only [j, Category.assoc, Category.comp_id, Category.id_comp, pullback.lift_fst,
            pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc,
            pullback.condition] using h
    · intro Z x y hxy
      have hfst : x ≫ pullback.fst i f = y ≫ pullback.fst i q' := by
        have h := congrArg (fun a => a ≫ pullback.fst (i ≫ g) (f ≫ g)) hxy
        simpa only [d, mapDesc_comp_fst, mapDesc_comp_snd, Category.assoc, Category.comp_id,
            Category.id_comp, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
            pullback.lift_snd_assoc, pullback.condition] using h
      have hsnd : x ≫ pullback.snd i f =
          y ≫ pullback.snd i q' ≫ pullback.snd (f ≫ g) (f ≫ g) := by
        have h := congrArg (fun a => a ≫ pullback.snd (i ≫ g) (f ≫ g)) hxy
        simpa only [d, mapDesc_comp_fst, mapDesc_comp_snd, Category.assoc, Category.comp_id,
            Category.id_comp, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
            pullback.lift_snd_assoc, pullback.condition] using h
      have heq : (y ≫ pullback.snd i q' ≫ pullback.fst (f ≫ g) (f ≫ g)) ≫ f =
          (x ≫ pullback.snd i f) ≫ f := by
        calc
          _ = y ≫ pullback.fst i q' ≫ i := by
            simpa only [Category.assoc] using
              congrArg (fun a => y ≫ a) (pullback.condition (f := i) (g := q')).symm
          _ = x ≫ pullback.fst i f ≫ i := by
            simpa only [Category.assoc] using congrArg (fun a => a ≫ i) hfst.symm
          _ = _ := by rw [pullback.condition]; simp
      let zR := pullback.lift
        (y ≫ pullback.snd i q' ≫ pullback.fst (f ≫ g) (f ≫ g))
        (x ≫ pullback.snd i f) heq
      have hzR : (x ≫ pullback.fst i f) ≫ i = zR ≫ q := by
        dsimp [q, zR]
        rw [← Category.assoc, pullback.lift_fst, heq]
        simp only [Category.assoc, pullback.condition]
      let z : Z ⟶ T := pullback.lift (x ≫ pullback.fst i f) zR hzR
      refine ⟨z, ?_, ?_⟩
      · apply pullback.hom_ext <;> simp only [z, c, zR, Category.assoc, pullback.lift_fst,
          pullback.lift_snd, pullback.lift_snd_assoc]
      · apply pullback.hom_ext
        · simpa only [z, j, Category.assoc, Category.comp_id, Category.id_comp,
            pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
            pullback.lift_snd_assoc, pullback.condition] using hfst
        · apply pullback.hom_ext
          · simp only [z, j, zR, m, Category.assoc, Category.comp_id, pullback.lift_fst,
              pullback.lift_snd, pullback.lift_snd_assoc]
          · simpa only [z, j, zR, m, mapDesc_comp_fst, mapDesc_comp_snd, Category.assoc,
              Category.comp_id, Category.id_comp, pullback.lift_fst, pullback.lift_snd,
              pullback.lift_fst_assoc, pullback.lift_snd_assoc, pullback.condition] using hsnd
  have hj : IsClosedImmersion B S hS j :=
    MorphismProperty.of_isPullback sq hc
  have hn : IsOpenImmersion B S hS (pullback.snd i q') :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback i q') hi
  have hcomp := immersion_comp_openImmersion B S hS j (pullback.snd i q')
    (immersion_of_closedImmersion B S hS j hj) hn
  simpa only [j, Category.assoc, Category.comp_id, Category.id_comp, pullback.lift_fst,
      pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc,
      pullback.condition] using hcomp

private theorem selfOverlap_isClosedImmersion
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X V Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (U : Subfunctor X) (f : V ⟶ X) (g : X ⟶ Y)
    (hsq : AlgebraicGeometry.Space.IsElementaryDistinguishedSquare B S hS hX U f)
    (hV : AlgebraicGeometry.Space.IsSeparated B S hS (f ≫ g))
    (hUV : IsClosedImmersion B S hS (pullback.mapDesc U.ι f g))
    (hVV : IsClosedMorphism B S hS (pullback.mapDesc f f g)) :
    IsClosedImmersion B S hS (pullback.mapDesc f f g) := by
  let R := pullback f f
  let q := pullback.fst f f ≫ f
  let A : ULift.{u} Bool → (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
    fun i => if i.down then pullback U.ι q else V
  let r : ∀ i, A i ⟶ R
    | ⟨false⟩ => pullback.diagonal f
    | ⟨true⟩ => pullback.snd U.ι q
  have hR := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS f f
    hsq.isAlgebraicSpace hsq.isAlgebraicSpace hX
  apply closedImmersion_of_closed_of_openCover B S hS hR
    (AlgebraicGeometry.isAlgebraicSpace_pullback B S hS (f ≫ g) (f ≫ g)
      hsq.isAlgebraicSpace hsq.isAlgebraicSpace hY)
    (pullback.mapDesc f f g) hVV A
    (fun i => by
      rcases i with ⟨i⟩; cases i
      · exact hsq.isAlgebraicSpace
      · exact AlgebraicGeometry.isAlgebraicSpace_pullback B S hS U.ι q
          hsq.isOpenSubspace.1 hR hX) r
  · rintro ⟨i⟩; cases i
    · exact isOpenImmersion_diagonal_of_isUnramified B S hS
        hsq.isAlgebraicSpace hX f (isUnramified_of_isEtale B S hS hsq.isEtale)
    · exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback U.ι q) hsq.isOpenSubspace.2
  · intro x
    obtain hx | hx := overlap_points_covered_by_diagonal_or_open B S hS hX U f hsq x
    · exact ⟨⟨false⟩, hx⟩
    · exact ⟨⟨true⟩, hx⟩
  · rintro ⟨i⟩; cases i
    · have he : pullback.diagonal f ≫ pullback.mapDesc f f g =
          pullback.diagonal (f ≫ g) := by
        apply pullback.hom_ext <;> simp []
      show IsImmersion B S hS
        (pullback.diagonal f ≫ pullback.mapDesc f f g)
      rw [he]
      exact immersion_of_closedImmersion B S hS _ hV
    · exact selfOverlap_openPart_isImmersion B S hS U.ι f g hsq.isOpenSubspace.2 hUV

/-- An étale covering stays one after a surjective reindexing of its members and
isomorphisms of their sources compatible with the structure morphisms. -/
private theorem isEtaleCovering_of_isos
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I J : Type w} {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {X : I → (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : ∀ i, X i ⟶ F}
    (h : AlgebraicGeometry.Space.IsEtaleCovering B S hS X f)
    {Y : J → (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {e : ∀ j, Y j ⟶ F}
    (σ : J → I) (hσ : Function.Surjective σ) (iso : ∀ j, X (σ j) ≅ Y j)
    (hfac : ∀ j, f (σ j) = (iso j).hom ≫ e j) :
    AlgebraicGeometry.Space.IsEtaleCovering B S hS Y e := by
  refine ⟨h.target_isAlgebraicSpace,
    fun j => isAlgebraicSpace_of_iso B S hS (iso j) (h.source_isAlgebraicSpace (σ j)),
    fun j => ?_, ?_⟩
  · intro T φ hφ
    have hinv := etalePresheaf_comp B S hS φ (iso j).inv hφ
      (etalePresheaf_of_iso B S hS (iso j))
    have hres := h.etale (σ j) T (φ ≫ (iso j).inv) hinv
    have hfac' : (iso j).inv ≫ f (σ j) = e j := by
      rw [hfac j, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    simpa only [Category.assoc, hfac'] using hres
  · rw [Set.eq_univ_iff_forall]
    intro z
    obtain ⟨i, hi⟩ :=
      Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp h.jointly_surjective z)
    obtain ⟨j, hj⟩ := hσ i
    subst hj
    obtain ⟨q, hq⟩ := Set.mem_range.mp hi
    refine Set.mem_iUnion.mpr ⟨j, Set.mem_range.mpr
      ⟨pointsMap B S hS (X (σ j)) (iso j).hom q, ?_⟩⟩
    calc pointsMap B S hS (Y j) (e j) (pointsMap B S hS (X (σ j)) (iso j).hom q)
        = pointsMap B S hS (X (σ j)) ((iso j).hom ≫ e j) q :=
          pointsMap_comp_eq B S hS (iso j).hom (e j) q
      _ = z := by rw [← hfac j]; exact hq

/-- The fibre product of `W i` with `W j` over the relative diagonal data of `g`
identifies with the fibre product of `W i` and `W j` over `Y`. -/
private theorem exists_iso_pairwiseFiberProduct
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Wi Wj : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X ⟶ Y)
    (ai : Wi ⟶ X) (aj : Wj ⟶ X) :
    ∃ iso : pullback (pullback.fst (pullback.fst g g) ai ≫ pullback.snd g g) aj ≅
        pullback (ai ≫ g) (aj ≫ g),
      pullback.fst (pullback.fst (pullback.fst g g) ai ≫ pullback.snd g g) aj ≫
          pullback.fst (pullback.fst g g) ai =
        iso.hom ≫ pullback.map (ai ≫ g) (aj ≫ g) g g ai aj (𝟙 Y)
          (by simp) (by simp) := by
  classical
  let Z := pullback g g
  let p₁ := pullback.fst g g
  let p₂ := pullback.snd g g
  let A := pullback p₁ ai
  let r : A ⟶ Z := pullback.fst p₁ ai
  let s : A ⟶ X := r ≫ p₂
  let Bpair := pullback s aj
  let b : Bpair ⟶ A := pullback.fst s aj
  let c : Bpair ⟶ Wj := pullback.snd s aj
  let P := pullback (ai ≫ g) (aj ≫ g)
  let e : P ⟶ Z := pullback.map (ai ≫ g) (aj ≫ g) g g ai aj (𝟙 Y) (by simp) (by simp)
  let Aiso : A ≅ pullback (ai ≫ g) g :=
    (pullbackSymmetry p₁ (ai)).trans
      (pullbackRightPullbackFstIso g g (ai))
  have hAisoSnd :
      (Aiso).hom ≫ pullback.snd (ai ≫ g) g = s := by
    dsimp only [Aiso, s, r, Iso.trans_hom]
    rw [Category.assoc, pullbackRightPullbackFstIso_hom_snd,
      ← Category.assoc, pullbackSymmetry_hom_comp_snd]
  have hAisoFst :
      (Aiso).hom ≫ pullback.fst (ai ≫ g) g = pullback.snd p₁ (ai) := by
    dsimp only [Aiso, Iso.trans_hom]
    rw [Category.assoc, pullbackRightPullbackFstIso_hom_fst,
      pullbackSymmetry_hom_comp_fst]
  let Cpair :=
    pullback (pullback.snd (ai ≫ g) g) (aj)
  let mapA := pullback.map (s) (aj)
    (pullback.snd (ai ≫ g) g) (aj)
    (Aiso).hom (𝟙 _) (𝟙 _)
    (by simpa only [Category.comp_id] using (hAisoSnd).symm)
    (by simp only [Category.comp_id, Category.id_comp])
  let isoB : Bpair ≅ P :=
    asIso (mapA) ≪≫
      pullbackLeftPullbackSndIso (ai ≫ g) g (aj)
  have hmapAFst : mapA ≫ pullback.fst
      (pullback.snd (ai ≫ g) g) (aj) = b ≫ (Aiso).hom :=
    pullback.lift_fst _ _ _
  have hmapASnd : mapA ≫ pullback.snd
      (pullback.snd (ai ≫ g) g) (aj) = c :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hIsoBFst :
      (isoB).hom ≫ pullback.fst (ai ≫ g) (aj ≫ g) =
        b ≫ pullback.snd p₁ (ai) := by
    calc
      (isoB).hom ≫ pullback.fst (ai ≫ g) (aj ≫ g) =
          (mapA ≫ pullback.fst (pullback.snd (ai ≫ g) g) (aj)) ≫
            pullback.fst (ai ≫ g) g := by
        dsimp only [isoB]
        rw [Iso.trans_hom, asIso_hom, Category.assoc,
          pullbackLeftPullbackSndIso_hom_fst, Category.assoc]
      _ = (b ≫ (Aiso).hom) ≫ pullback.fst (ai ≫ g) g := by
        rw [hmapAFst]
      _ = b ≫ pullback.snd p₁ (ai) := by
        calc
          (b ≫ (Aiso).hom) ≫ pullback.fst (ai ≫ g) g =
              b ≫ ((Aiso).hom ≫ pullback.fst (ai ≫ g) g) := by
                simp only [Category.assoc]
          _ = b ≫ pullback.snd p₁ (ai) := by rw [hAisoFst]
  have hIsoBSnd :
      (isoB).hom ≫ pullback.snd (ai ≫ g) (aj ≫ g) = c := by
    calc
      (isoB).hom ≫ pullback.snd (ai ≫ g) (aj ≫ g) =
          mapA ≫ pullback.snd (pullback.snd (ai ≫ g) g) (aj) := by
        dsimp only [isoB, Iso.trans_hom, asIso_hom]
        rw [Category.assoc, pullbackLeftPullbackSndIso_hom_snd]
      _ = c := hmapASnd
  have heFst : e ≫ p₁ =
      pullback.fst (ai ≫ g) (aj ≫ g) ≫ ai :=
    pullback.lift_fst _ _ _
  have heSnd : e ≫ p₂ =
      pullback.snd (ai ≫ g) (aj ≫ g) ≫ aj :=
    pullback.lift_snd _ _ _
  have h : b ≫ r = (isoB).hom ≫ e := by
    apply pullback.hom_ext
    · calc
        b ≫ r ≫ p₁ = b ≫ pullback.fst p₁ (ai) ≫ p₁ := by rfl
        _ = b ≫ pullback.snd p₁ (ai) ≫ ai := by
          rw [pullback.condition (f := p₁) (g := ai)]
        _ = (b ≫ pullback.snd p₁ (ai)) ≫ ai := by
          simp only [Category.assoc]
        _ = ((isoB).hom ≫ pullback.fst (ai ≫ g) (aj ≫ g)) ≫ ai := by
          rw [hIsoBFst]
        _ = (isoB).hom ≫ (pullback.fst (ai ≫ g) (aj ≫ g) ≫ ai) := by
          simp only [Category.assoc]
        _ = (isoB).hom ≫ (e ≫ p₁) := by rw [← heFst]
        _ = (isoB).hom ≫ e ≫ p₁ := by simp only []
    · calc
        b ≫ r ≫ p₂ = b ≫ s := by
          simp only [r, s]
        _ = c ≫ aj := pullback.condition (f := s) (g := aj)
        _ = ((isoB).hom ≫ pullback.snd (ai ≫ g) (aj ≫ g)) ≫ aj := by
          rw [hIsoBSnd]
        _ = (isoB).hom ≫ (pullback.snd (ai ≫ g) (aj ≫ g) ≫ aj) := by
          simp only [Category.assoc]
        _ = (isoB).hom ≫ (e ≫ p₂) := by rw [← heSnd]
        _ = (isoB).hom ≫ e ≫ p₂ := by simp only []
  exact ⟨isoB, h⟩

/-- If a family of étale morphisms covers `X`, the pairwise fibre products of its members
over `Y` form an étale covering of `X ×_Y X`. -/
private theorem isEtaleCovering_pairwiseFiberProduct
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y) (g : X ⟶ Y)
    (W : Bool → (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (a : ∀ i, W i ⟶ X)
    (hCoverX : AlgebraicGeometry.Space.IsEtaleCovering B S hS W a) :
    AlgebraicGeometry.Space.IsEtaleCovering B S hS
      (fun ij : Bool × Bool => pullback (a ij.1 ≫ g) (a ij.2 ≫ g))
      (fun ij : Bool × Bool =>
        pullback.map (a ij.1 ≫ g) (a ij.2 ≫ g) g g (a ij.1) (a ij.2) (𝟙 Y)
          (by simp) (by simp)) := by
  classical
  let Z := pullback g g
  let p₁ := pullback.fst g g
  let p₂ := pullback.snd g g
  let A : Bool → (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
    fun i => pullback p₁ (a i)
  let r : ∀ i, A i ⟶ Z := fun i => pullback.fst p₁ (a i)
  let s : ∀ i, A i ⟶ X := fun i => r i ≫ p₂
  let Bpair : ∀ i j : Bool,
      (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
    fun i j => pullback (s i) (a j)
  let b : ∀ i j, Bpair i j ⟶ A i := fun i j => pullback.fst (s i) (a j)
  let c : ∀ i j, Bpair i j ⟶ W j := fun i j => pullback.snd (s i) (a j)
  have hZspace : AlgebraicGeometry.IsAlgebraicSpace B S hS Z :=
    AlgebraicGeometry.isAlgebraicSpace_pullback B S hS g g hX hX hY
  have hAspace : ∀ i, AlgebraicGeometry.IsAlgebraicSpace B S hS (A i) := by
    intro i
    exact AlgebraicGeometry.isAlgebraicSpace_pullback B S hS p₁ (a i)
      hZspace (hCoverX.source_isAlgebraicSpace i) hX
  have hBspace : ∀ i j, AlgebraicGeometry.IsAlgebraicSpace B S hS (Bpair i j) := by
    intro i j
    exact AlgebraicGeometry.isAlgebraicSpace_pullback B S hS (s i) (a j)
      (hAspace i) (hCoverX.source_isAlgebraicSpace j) hX
  have hCoverA := AlgebraicGeometry.Space.isEtaleCovering_pullback
    B S hS p₁ hZspace W a hCoverX
  have hCoverB (i : Bool) :=
    AlgebraicGeometry.Space.isEtaleCovering_pullback
      B S hS (s i) (hAspace i) W a hCoverX
  have hNestedCover := AlgebraicGeometry.Space.isEtaleCovering_comp
    B S hS (fun _ : Bool => Bool) A r Bpair b hCoverA hCoverB
  let P : Bool → Bool → (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
    fun i j => pullback (a i ≫ g) (a j ≫ g)
  let e : ∀ i j, P i j ⟶ Z := fun i j =>
    pullback.map (a i ≫ g) (a j ≫ g) g g (a i) (a j) (𝟙 Y)
      (by simp) (by simp)
  choose isoB hiso using fun i j : Bool =>
    exists_iso_pairwiseFiberProduct B S hS g (a i) (a j)
  exact isEtaleCovering_of_isos B S hS hNestedCover
    (fun ij : Bool × Bool => (⟨ij.1, ij.2⟩ : (i : Bool) × Bool))
    (fun ij => ⟨(ij.1, ij.2), rfl⟩) (fun ij => isoB ij.1 ij.2)
    (fun ij => hiso ij.1 ij.2)

/-- **Stacks 0F45.** A morphism of algebraic spaces `g : X ⟶ Y` over `S` is separated once an
elementary distinguished square `(U ⊆ X, f : V ⟶ X)` has `U ⟶ Y` and `V ⟶ Y` separated and
has the comparison maps `U ×_X V ⟶ U ×_Y V` and `V ×_X V ⟶ V ×_Y V` closed.

The second comparison map is **not** among the source's hypotheses: Lemma 81.14.1 asks only for
`U ×_X V ⟶ U ×_Y V` to be closed, and its proof asserts that
`(V ×_Y V) ×_{X ×_Y X, Δ} X = V`, which is false — that base change is `V ×_X V`. The source's
hypothesis list is insufficient, and the counterexample in this module's docstring shows the
extra hypothesis cannot be dropped. This statement is therefore the repaired one. -/
@[stacks 0F45 "with the additional hypothesis that V ×_X V ⟶ V ×_Y V is closed; the source's \
hypothesis list is insufficient, see the counterexample in the module docstring"]
public theorem isSeparated_of_elementaryDistinguishedSquare
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X V Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (g : X ⟶ Y) (U : Subfunctor X) (f : V ⟶ X)
    (hsq : AlgebraicGeometry.Space.IsElementaryDistinguishedSquare B S hS hX U f)
    (hU : AlgebraicGeometry.Space.IsSeparated B S hS (U.ι ≫ g))
    (hV : AlgebraicGeometry.Space.IsSeparated B S hS (f ≫ g))
    (hUV : IsClosedMorphism B S hS (pullback.mapDesc U.ι f g))
    (hVV : IsClosedMorphism B S hS (pullback.mapDesc f f g)) :
    AlgebraicGeometry.Space.IsSeparated B S hS g := by
  classical
  let W : Bool → (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
    fun | false => U.toFunctor | true => V
  let a : ∀ i, W i ⟶ X := fun | false => U.ι | true => f
  let XObj : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let YObj : AlgebraicSpaces B S hS := ⟨Y, hY⟩
  let ZObj := AlgebraicSpaces.fiberProduct B S hS
    (ObjectProperty.homMk g : XObj ⟶ YObj)
    (ObjectProperty.homMk g : XObj ⟶ YObj)
  let Z := pullback g g
  let p₁ := pullback.fst g g
  let p₂ := pullback.snd g g
  let hCoverX := elementarySquare_etaleCovering B S hS hX U f hsq
  let P : Bool → Bool → (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
    fun i j => pullback (a i ≫ g) (a j ≫ g)
  let e : ∀ i j, P i j ⟶ Z := fun i j =>
    pullback.map (a i ≫ g) (a j ≫ g) g g (a i) (a j) (𝟙 Y)
      (by simp) (by simp)
  have hZspace : AlgebraicGeometry.IsAlgebraicSpace B S hS Z :=
    AlgebraicGeometry.isAlgebraicSpace_pullback B S hS g g hX hX hY
  have hPCover : AlgebraicGeometry.Space.IsEtaleCovering B S hS
      (fun ij : Bool × Bool => P ij.1 ij.2)
      (fun ij => e ij.1 ij.2) :=
    isEtaleCovering_pairwiseFiberProduct B S hS hX hY g W a hCoverX
  let Zcat := AlgebraicSpaces B S hS
  let ι : Zcat ⥤ (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
    ObjectProperty.ι _
  let Closed : MorphismProperty Zcat := fun _ _ m =>
    IsClosedImmersion B S hS m.hom
  let d : XObj ⟶ ZObj := ObjectProperty.homMk (pullback.diagonal g)
  let Wobj (i : Bool) : Zcat := ⟨W i, hCoverX.source_isAlgebraicSpace i⟩
  let gobj (i : Bool) : Wobj i ⟶ YObj := ObjectProperty.homMk (a i ≫ g)
  let Pobj (ij : Bool × Bool) : Zcat :=
    AlgebraicSpaces.fiberProduct B S hS (gobj ij.1) (gobj ij.2)
  let eobj : ∀ ij : Bool × Bool, Pobj ij ⟶ ZObj := fun ij =>
    ObjectProperty.homMk (e ij.1 ij.2)
  have hClosed : Closed d := by
    let K := AlgebraicGeometry.Space.Topology.precoverage.{u, u} .fpqc B S hS
    let I : Type u := ULift.{u} (Bool × Bool)
    let P' (ij : I) := P ij.down.1 ij.down.2
    let e' (ij : I) := e ij.down.1 ij.down.2
    have hPCover' : AlgebraicGeometry.Space.IsEtaleCovering B S hS P' e' := by
      refine ⟨hPCover.target_isAlgebraicSpace, (fun ij => hPCover.source_isAlgebraicSpace ij.down),
        (fun ij => hPCover.etale ij.down), ?_⟩
      rw [Set.eq_univ_iff_forall]
      intro z
      have hz : z ∈ ⋃ ij : Bool × Bool,
          Set.range (pointsMap B S hS (P ij.1 ij.2) (e ij.1 ij.2)) := by
        rw [hPCover.jointly_surjective]
        exact Set.mem_univ z
      obtain ⟨ij, hz⟩ := Set.mem_iUnion.mp hz
      obtain ⟨q, hq⟩ := Set.mem_range.mp hz
      exact Set.mem_iUnion.mpr ⟨ULift.up ij, Set.mem_range.mpr ⟨q, hq⟩⟩
    let hfpqc := AlgebraicGeometry.Space.isFpqcCovering_of_isEtaleCovering B S hS P' e' hPCover'
    let Pobj' (ij : I) := Pobj ij.down
    let eobj' (ij : I) := eobj ij.down
    have hmem : Presieve.ofArrows Pobj' eobj' ∈ K ZObj :=
      ⟨I, Pobj', eobj', rfl, ZObj.property,
        (fun ij => (Pobj' ij).property), hfpqc⟩
    let E : Precoverage.ZeroHypercover.{u} K ZObj :=
      ⟨{ I₀ := I, X := Pobj', f := eobj' }, hmem⟩
    let : Closed.IsLocalAtTarget K :=
      isClosedImmersion_isLocalAtTarget_fpqc B S hS
    rw [MorphismProperty.IsLocalAtTarget.iff_of_zeroHypercover (P := Closed) E]
    intro ijU
    let ij := ijU.down
    have hmap : IsClosedImmersion B S hS
        (pullback.mapDesc (a ij.1) (a ij.2) g) := by
      have hUVc : IsClosedImmersion B S hS (pullback.mapDesc U.ι f g) :=
        closedImmersion_of_isImmersion_and_isClosed B S hS
          (AlgebraicGeometry.isAlgebraicSpace_pullback B S hS _ _ hsq.isOpenSubspace.1
            hsq.isAlgebraicSpace hX)
          (AlgebraicGeometry.isAlgebraicSpace_pullback B S hS _ _ hsq.isOpenSubspace.1
            hsq.isAlgebraicSpace hY) _
          (overlap_isImmersion B S hS hX hsq.isAlgebraicSpace hY U f g hsq.isOpenSubspace hU) hUV
      rcases ij with ⟨i, j⟩
      cases i <;> cases j
      · simpa only [a, W, Category.assoc, Category.comp_id, Category.id_comp, pullback.lift_fst,
          pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc] using
          (mapDesc_isClosedImmersion_of_mono B S hS U.ι g hU)
      · exact hUVc
      · exact overlap_swap_closedImmersion B S hS U.ι f g hUVc
      · exact selfOverlap_isClosedImmersion B S hS hX hY U f g hsq hV hUVc hVV
    have hpull := pullback_map_diagonal_isPullback (a ij.1) (a ij.2) g
    have hpiece : IsClosedImmersion B S hS
        (pullback.snd (pullback.diagonal g) (e ij.1 ij.2)) := by
      rw [← MorphismProperty.cancel_left_of_respectsIso
          (P := @IsClosedImmersion B S hS)
          hpull.isoPullback.hom (pullback.snd (pullback.diagonal g) (e ij.1 ij.2)),
        IsPullback.isoPullback_hom_snd]
      exact hmap
    let Pcan := AlgebraicSpaces.fiberProduct B S hS d (E.f ijU)
    let sndCan : Pcan ⟶ Pobj ij :=
      ObjectProperty.homMk (pullback.snd (pullback.diagonal g) (e ij.1 ij.2))
    have hcanClosed : Closed sndCan := by
      show IsClosedImmersion B S hS
        (pullback.snd (pullback.diagonal g) (e ij.1 ij.2))
      exact hpiece
    have hcan := AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct B S hS d (E.f ijU)
    have hcomp : Closed (hcan.isoPullback.hom ≫ pullback.snd d (E.f ijU)) := by
      rw [hcan.isoPullback_hom_snd]
      exact hcanClosed
    let : Closed.RespectsIso := by
      show (MorphismProperty.inverseImage
        (@IsClosedImmersion B S hS) ι).RespectsIso
      exact MorphismProperty.RespectsIso.inverseImage _ _
    exact (Closed.cancel_left_of_respectsIso hcan.isoPullback.hom
      (pullback.snd d (E.f ijU))).1 hcomp
  show IsClosedImmersion B S hS (pullback.diagonal g)
  exact hClosed

end AlgebraicGeometry.Space
