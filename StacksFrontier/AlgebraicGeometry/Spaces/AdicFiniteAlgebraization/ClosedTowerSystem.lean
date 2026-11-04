module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdicFiniteAlgebraization.AdicFibreTower
public import StacksFrontier.AlgebraicGeometry.Spaces.AdicFiniteAlgebraization.AffineTowerSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportClosedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceHypotheses
public import StacksFrontier.AlgebraicGeometry.Spaces.DefiningIdealFiniteTypeOfQuotient

/-!
# The coherent system of a tower of closed subspaces of the adic fibres

Let `P` be an algebraic space locally of finite type over a Noetherian ring `A`, with adic fibres
`P_n`, and let `z_n : Z_n ⟶ P_n` be closed immersions forming a cartesian tower,
`Z_n = Z_{n + 1} ×_{P_{n + 1}} P_n`. This file constructs the system `ℱ_n = z_{n, *} 𝒪_{Z_n}` of
coherent modules on the adic fibres, as an object of the category of Stacks 08BF, and shows that
its lowest term has support proper over the base when `Z_0` is proper over `Spec (A / I)`, which
is the support condition of 08BF.

## Main definitions

* `AlgebraicGeometry.Space.closedTowerAffine`: `Z_n` as an algebraic space affine over `P_n`.
* `AlgebraicGeometry.Space.closedTowerSystem`: the coherent system `(z_{n, *} 𝒪_{Z_n})_n`.

## Main results

* `AlgebraicGeometry.Space.hasProperSupport_closedTowerSystem`: the direct image to `P` of the
  lowest term has support proper over `Spec A`.

## References

* [Stacks Project, Tag 08BG](https://stacks.math.columbia.edu/tag/08BG)
* [Stacks Project, Tag 08BF](https://stacks.math.columbia.edu/tag/08BF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (A : Type u) [CommRing A] (I : Ideal A) (B : BigFppfSite.{u})
  (hA : B.Contains (Spec (.of A)))
  {P : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}
  (hP : IsAlgebraicSpace B (Spec (.of A)) hA P) (g : P ⟶ yoneda.obj (baseObject A B hA))
  (Zn : ℕ → AlgebraicSpaces B (Spec (.of A)) hA) (z : ∀ n, Zn n ⟶ adicFibreSpace A I B hA hP g n)
  (tZ : ∀ n, Zn n ⟶ Zn (n + 1))
  (hcart : ∀ n, IsPullback (tZ n) (z n) (z (n + 1)) (adicFibreSuccHom A I B hA hP g n))
  (hci : ∀ n, IsClosedImmersion B (Spec (.of A)) hA (z n).hom)

/-- `Z_n`, as an algebraic space affine over the adic fibre `P_n`: a closed immersion is
finite, hence affine. -/
def closedTowerAffine (n : ℕ) : AffineOver B (Spec (.of A)) hA (adicFibreSpace A I B hA hP g n) :=
  ⟨Over.mk (z n), IsFinite.isAffineHom
    (isFinite_of_isClosedImmersion B (Spec (.of A)) hA _ (hci n))⟩

/-- The direct images `z_{n, *} 𝒪_{Z_n}` are coherent. -/
theorem isCoherent_closedTowerAffine [IsNoetherianRing A]
    (hft : IsLocallyOfFiniteType B (Spec (.of A)) hA g) (n : ℕ) :
    IsCoherent B (Spec (.of A)) hA (adicFibreSpace A I B hA hP g n).1
      (adicFibreSpace A I B hA hP g n).2
      (pushforwardAlgebra B (Spec (.of A)) hA
        (closedTowerAffine A I B hA hP g Zn z hci n).obj).underlyingModule := by
  have : Fact (HasEtaleLocalProperty B (Spec (.of A)) hA (adicFibreSpace A I B hA hP g n).1
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
    ⟨hasEtaleLocalProperty_isLocallyNoetherian_adicFibre A I B hA hP g hft n⟩
  exact isCoherent_underlyingModule_pushforwardAlgebra_of_isFinite B (Spec (.of A)) hA (z n)
    (isFinite_of_isClosedImmersion B (Spec (.of A)) hA _ (hci n))

/-- **The coherent system `(z_{n, *} 𝒪_{Z_n})_n`** of a cartesian tower of closed subspaces of the
adic fibres, an object of the category of Stacks 08BF. -/
def closedTowerSystem [IsNoetherianRing A] (hft : IsLocallyOfFiniteType B (Spec (.of A)) hA g) :
    ThickeningCoherentSystem B (Spec (.of A)) hA (adicFibreSpace A I B hA hP g)
      (adicFibreSuccHom A I B hA hP g) :=
  affineTowerSystem B (Spec (.of A)) hA (adicFibreSuccHom A I B hA hP g)
    (closedTowerAffine A I B hA hP g Zn z hci) tZ hcart
    (isCoherent_closedTowerAffine A I B hA hP g Zn z hci hft)

/-- **The lowest term of the system of a cartesian affine tower over the adic fibres has proper
support** over `Spec A`, once `W_0 ⟶ P_0` is universally closed, `W_0` is proper over
`Spec (A / I)`, and `P` is separated over `Spec A`: its direct image to `P` is supported on the
image of `W_0`, which is proper over `Spec A`. -/
theorem hasProperSupport_affineTowerSystem_zero [IsNoetherianRing A]
    (hft : IsLocallyOfFiniteType B (Spec (.of A)) hA g) (hsep : IsSeparated B (Spec (.of A)) hA g)
    (W : ∀ n, AffineOver B (Spec (.of A)) hA (adicFibreSpace A I B hA hP g n))
    (s : ∀ n, (W n).obj.left ⟶ (W (n + 1)).obj.left)
    (hcartW : ∀ n, IsPullback (s n) (W n).obj.hom (W (n + 1)).obj.hom
      (adicFibreSuccHom A I B hA hP g n))
    (hcoh : ∀ n, IsCoherent B (Spec (.of A)) hA (adicFibreSpace A I B hA hP g n).1
      (adicFibreSpace A I B hA hP g n).2
      (pushforwardAlgebra B (Spec (.of A)) hA (W n).obj).underlyingModule)
    (hW0 : UniversallyClosed B (Spec (.of A)) hA (W 0).obj.hom.hom)
    (hproper : IsProper B (Spec (.of A)) hA ((W 0).obj.hom.hom ≫ adicFibreSnd A I B hA g 0)) :
    HasProperSupport B (Spec (.of A)) hA hP (isAlgebraicSpace_yoneda B (Spec (.of A)) hA _) g hft
      ((SheafOfModules.toSheaf _).obj ((modulePushforward B (Spec (.of A)) hA
        (adicFibreFstHom A I B hA hP g 0)).obj
          ((affineTowerSystem B (Spec (.of A)) hA (adicFibreSuccHom A I B hA hP g) W s hcartW
            hcoh).term 0).obj)) := by
  let ι0 := adicFibreFstHom A I B hA hP g 0
  let w0 := (W 0).obj.hom
  let h : (W 0).obj.left ⟶ ⟨P, hP⟩ := w0 ≫ ι0
  have hι0 : IsClosedImmersion B (Spec (.of A)) hA ι0.hom :=
    isClosedImmersion_adicFibreFstHom A I B hA hP g 0
  have hι0cl : IsClosedMorphism B (Spec (.of A)) hA ι0.hom :=
    isClosedMorphism_of_isClosedImmersion B (Spec (.of A)) hA (adicFibreSpace A I B hA hP g 0).2 hP
      _ hι0
  have hw0cl : IsClosedMorphism B (Spec (.of A)) hA w0.hom := fun T hT =>
    isClosed_image_of_universallyClosed B (Spec (.of A)) hA (W 0).obj.left.2
      (adicFibreSpace A I B hA hP g 0).2 _ hW0 T hT
  have hS0 : IsProper B (Spec (.of A)) hA
      (yoneda.map (adicThickeningMap A I B hA (contains_adicThickening A I B hA) 0)) :=
    isProper_of_isClosedImmersion B (Spec (.of A)) hA (isAlgebraicSpace_yoneda _ _ hA _)
      (isAlgebraicSpace_yoneda _ _ hA _) _
      (isClosedImmersion_yoneda_map_adicThickeningMap A I B hA 0)
  have hZ0 : IsProper B (Spec (.of A)) hA (h.hom ≫ g) := by
    have hw : h.hom ≫ g = (w0.hom ≫ adicFibreSnd A I B hA g 0) ≫
        yoneda.map (adicThickeningMap A I B hA (contains_adicThickening A I B hA) 0) := by
      show (w0.hom ≫ pullback.fst g _) ≫ g = _
      rw [Category.assoc, Category.assoc, pullback.condition]
    rw [hw]
    exact isProper_comp' B (Spec (.of A)) hA _ _ (isAlgebraicSpace_yoneda _ _ hA _)
      (isAlgebraicSpace_yoneda _ _ hA _) hproper hS0
  have hUpr := isProperOver_of_isProper B (Spec (.of A)) hA (W 0).obj.left.2
    (isAlgebraicSpace_yoneda _ _ hA _) _ hZ0.2.1.1 hZ0 Set.univ isClosed_univ
  have hclosed : IsClosedMorphism B (Spec (.of A)) hA h.hom := hι0cl.comp B (Spec (.of A)) hA hw0cl
  have himcl : IsClosed (pointsMap B (Spec (.of A)) hA (W 0).obj.left.1 h.hom '' Set.univ) :=
    hclosed _ isClosed_univ
  have himpr := isProperOver_image_of_isSeparated B (Spec (.of A)) hA (W 0).obj.left.2 hP
    (isAlgebraicSpace_yoneda _ _ hA _) h.hom (h.hom ≫ g) g rfl hZ0.2.1.1 hft hsep _ isClosed_univ
    hUpr himcl
  have hloc : HasEtaleLocalProperty B (Spec (.of A)) hA P
      (fun V : Scheme.{u} => IsLocallyNoetherian V) :=
    hasEtaleLocalProperty_isLocallyNoetherian_of_isFiniteType_baseObject A B hA hP g hft
  let G0 := (affineTowerSystem B (Spec (.of A)) hA (adicFibreSuccHom A I B hA hP g) W s hcartW
    hcoh).term 0
  have hG0 : G0.obj = (modulePushforward B (Spec (.of A)) hA w0).obj
      (SheafOfModules.unit (structureRingSheaf B (Spec (.of A)) hA (W 0).obj.left) :
        Modules.{u, u} B (Spec (.of A)) hA (W 0).obj.left.1 (W 0).obj.left.2) :=
    congrArg (fun F => F.obj (SheafOfModules.unit (structureRingSheaf B (Spec (.of A)) hA
      (W 0).obj.left))) (pushforwardModules_eq_modulePushforward B (Spec (.of A)) hA w0)
  have hcohP : IsCoherent B (Spec (.of A)) hA P hP
      ((modulePushforward B (Spec (.of A)) hA ι0).obj G0.obj) :=
    isCoherent_modulePushforward_of_isClosedImmersion B (Spec (.of A)) hA hloc ι0 hι0 _ G0.property
  have : SheafOfModules.IsCoherentOnSite G0.obj := G0.property.toIsCoherentOnSite
  have : SheafOfModules.IsCoherentOnSite
      ((modulePushforward B (Spec (.of A)) hA ι0).obj G0.obj) := hcohP.toIsCoherentOnSite
  have := isFiniteTypeOnSite_of_isCoherentOnSite B (Spec (.of A)) hA
    (adicFibreSpace A I B hA hP g 0) G0.obj
  have := isFiniteTypeOnSite_of_isCoherentOnSite B (Spec (.of A)) hA ⟨P, hP⟩
    ((modulePushforward B (Spec (.of A)) hA ι0).obj G0.obj)
  have hcl := isClosed_supportOfSheaf_of_isFiniteTypeOnSite B (Spec (.of A)) hA P hP
    ((modulePushforward B (Spec (.of A)) hA ι0).obj G0.obj)
  have hG0cl := isClosed_supportOfSheaf_of_isFiniteTypeOnSite B (Spec (.of A)) hA
    (adicFibreSpace A I B hA hP g 0).1 (adicFibreSpace A I B hA hP g 0).2 G0.obj
  have h1 := supportOfSheaf_modulePushforward_subset_image B (Spec (.of A)) hA ι0 G0.obj
    hι0cl hG0cl
  let O0 : Modules.{u, u} B (Spec (.of A)) hA (W 0).obj.left.1 (W 0).obj.left.2 :=
    SheafOfModules.unit (structureRingSheaf B (Spec (.of A)) hA (W 0).obj.left)
  have : SheafOfModules.IsFiniteTypeOnSite O0 :=
    isFiniteTypeOnSite_unit_structureRingSheaf B (Spec (.of A)) hA (W 0).obj.left
  have hOcl := isClosed_supportOfSheaf_of_isFiniteTypeOnSite B (Spec (.of A)) hA
    (W 0).obj.left.1 (W 0).obj.left.2 O0
  have h3 := supportOfSheaf_modulePushforward_subset_image B (Spec (.of A)) hA w0 O0 hw0cl hOcl
  have h2 : supportOfSheaf B (Spec (.of A)) hA _ ((SheafOfModules.toSheaf _).obj G0.obj) ⊆
      pointsMap B (Spec (.of A)) hA (W 0).obj.left.1 w0.hom '' Set.univ := by
    rw [hG0]
    exact h3.trans (Set.image_mono (Set.subset_univ _))
  refine ⟨hcl, isProperOver_of_subset B (Spec (.of A)) hA hP (isAlgebraicSpace_yoneda _ _ hA _)
    g hft _ _ hcl himcl ?_ himpr⟩
  refine h1.trans ?_
  show _ ⊆ pointsMap B (Spec (.of A)) hA (W 0).obj.left.1 (w0.hom ≫ ι0.hom) '' Set.univ
  rw [pointsMap_comp, Set.image_comp]
  exact Set.image_mono h2

/-- **The lowest term of the system of a tower of closed subspaces has proper support** over
`Spec A` once `Z_0` is proper over `Spec (A / I)` and `P` is separated over `Spec A`. -/
theorem hasProperSupport_closedTowerSystem [IsNoetherianRing A]
    (hft : IsLocallyOfFiniteType B (Spec (.of A)) hA g) (hsep : IsSeparated B (Spec (.of A)) hA g)
    (hproper : IsProper B (Spec (.of A)) hA ((z 0).hom ≫ adicFibreSnd A I B hA g 0)) :
    HasProperSupport B (Spec (.of A)) hA hP (isAlgebraicSpace_yoneda B (Spec (.of A)) hA _) g hft
      ((SheafOfModules.toSheaf _).obj ((modulePushforward B (Spec (.of A)) hA
        (adicFibreFstHom A I B hA hP g 0)).obj
          ((closedTowerSystem A I B hA hP g Zn z tZ hcart hci hft).term 0).obj)) :=
  hasProperSupport_affineTowerSystem_zero A I B hA hP g hft hsep
    (closedTowerAffine A I B hA hP g Zn z hci) tZ hcart
    (isCoherent_closedTowerAffine A I B hA hP g Zn z hci hft)
    (isProper_of_isClosedImmersion B (Spec (.of A)) hA (Zn 0).2
      (adicFibreSpace A I B hA hP g 0).2 _ (hci 0)).2.2 hproper

end AlgebraicGeometry.Space

end
