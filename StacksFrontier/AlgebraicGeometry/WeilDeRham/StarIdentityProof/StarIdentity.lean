module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.DiagonalCupStatements
public import StacksFrontier.AlgebraicGeometry.DeRham.KunnethWedge
public import StacksFrontier.AlgebraicGeometry.DeRham.KunnethWedgeSection
public import StacksFrontier.AlgebraicGeometry.DeRham.KunnethDifferential
public import StacksFrontier.AlgebraicGeometry.DeRham.DeRhamFormsToRelative
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.GradedCommutativity
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.PullbackHgroupRetraction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerShortExact
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.RelativeEmbeddingDimensionForms
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.StarIdentityProof.SheafCup
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.StarIdentityProof.KunnethRelativeForms
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.StarIdentityProof.TopComponents

/-!
# The identity `(★)` of the diagonal argument

Classes of forms on `X ×_A X` (`Stacks.WeilDeRham.classTransport`) and the identity `(★)` of the
proof of [Stacks, Tag 0G8J] from the factorization through the sections
(`Stacks.WeilDeRham.starIdentity_of_cupFactorsThroughSection`).

## References

* [Stacks Project, Tag 0G8J](https://stacks.math.columbia.edu/tag/0G8J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction Stacks.Gysin Stacks.DeRham.GysinCohomologyBaseChange
open AlgebraicGeometry.Scheme.Hom Stacks.DeRham.CohomologicalGysin
open Stacks.DeRham.GysinCupHodge
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.Cohomology.GlobalKunneth (baseSections baseRing)
open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule)
open AlgebraicGeometry.SheafOfModules (moduleDerived canonicalPairingModule tensorBifunctorNat
  baseRingedSpace multiplicationInt)
open scoped Stacks.StandardDerivedModel

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose structureSheafRing
  AlgebraicGeometry.SheafedSpace.sheaf AlgebraicGeometry.SheafOfModules.baseRingedSpace
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.WeilDeRham

attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat
attribute [local instance] Stacks.DeRham.CohomologicalGysin.moduleSheavesHasDerivedCategory
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules
  AlgebraicGeometry.SheafOfModules.hasSheafifyOpens
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijectiveOpens

/-! ### Classes of forms on `X ×_A X` and the identity `(★)` -/

section Bridge

/-- **The pullback of classes of forms is the pullback along the unit followed by the canonical
map on forms**: for a square `g ≫ f = π ≫ t`, `g^*θ = (g^*Ωⁿ ⟶ Ωⁿ)(g^♮θ)`. -/
theorem pullbackHgroup_formsBaseChangeHom_apply {X W S S' : Scheme.{u}} (g : W ⟶ X) (f : X ⟶ S)
    (π : W ⟶ S') (t : S' ⟶ S) (hcomm : g ≫ f = π ≫ t) (n : ℤ) (q : ℕ)
    (θ : Hgroup (structureSheafRing X.toRingedSpace) ⊤ q (relativeDifferentialForms f n)) :
    (pullbackHgroup (CohomologyPullbackComparison.canonical g.toLRSHom.toShHom) 0 (q : ℤ) q
        (by simp) (formsBaseChangeHom g f π t hcomm n)).hom θ =
      (Hfunctor (structureSheafRing W.toRingedSpace) ⊤ q).map
        (relativeDifferentialFormsMap g f π t hcomm n)
        ((unitPullback g (relativeDifferentialForms f n) q).hom θ) := by
  have h := pullbackHgroup_naturality (CohomologyPullbackComparison.canonical g.toLRSHom.toShHom)
    0 (q : ℤ) q (by simp) (𝟙 _) (relativeDifferentialFormsMap g f π t hcomm n)
    ((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app _)
    (formsBaseChangeHom g f π t hcomm n)
    (((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).homEquiv_unit _ _ _).symm.trans
      (Category.id_comp _).symm)
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  exact ConcreteCategory.congr_hom h θ

/-- The transport of a class along equalities of the degree of the forms and of the cohomological
degree. -/
def classTransport {Y : RingedSpace.{u, u}}
    (M : ℤ → _root_.SheafOfModules.{u} (structureSheafRing Y))
    {k k' : ℤ} (hk : k = k') {N N' : ℕ} (hN : N = N') :
    Hgroup (structureSheafRing Y) ⊤ N (M k) ⟶ Hgroup (structureSheafRing Y) ⊤ N' (M k') :=
  (Hfunctor (structureSheafRing Y) ⊤ N).map (eqToHom (congrArg M hk)) ≫
    eqToHom (congrArg (fun q => Hgroup (structureSheafRing Y) ⊤ q (M k')) hN)

/-- The transport of classes commutes with the pullback of classes of forms. -/
theorem classTransport_pullbackHgroup {X W S S' : Scheme.{u}} (g : W ⟶ X) (f : X ⟶ S)
    (π : W ⟶ S') (t : S' ⟶ S) (hcomm : g ≫ f = π ≫ t) {k k' : ℤ} (hk : k = k') {m m' : ℤ}
    (hm : m = m') {N N' : ℕ} (hN : N = N') (h₁ : m - 0 = N) (h₂ : m' - 0 = N')
    (θ : Hgroup (structureSheafRing X.toRingedSpace) ⊤ N (relativeDifferentialForms f k)) :
    (classTransport (relativeDifferentialForms π) hk hN).hom
        ((pullbackHgroup (CohomologyPullbackComparison.canonical g.toLRSHom.toShHom) 0 m N h₁
          (formsBaseChangeHom g f π t hcomm k)).hom θ) =
      (pullbackHgroup (CohomologyPullbackComparison.canonical g.toLRSHom.toShHom) 0 m' N' h₂
          (formsBaseChangeHom g f π t hcomm k')).hom
        ((classTransport (relativeDifferentialForms f) hk hN).hom θ) := by
  subst hk hm hN
  simp only [classTransport, eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

/-- `hgroupModuleShiftIso` reads a transported class in the transported degree. -/
theorem hgroupModuleShiftIso_classTransport {Y : RingedSpace.{u, u}}
    (M : ℤ → _root_.SheafOfModules.{u} (structureSheafRing Y)) {k k' : ℤ} (hk : k = k') {N N' : ℕ}
    (hN : N = N') (m : ℤ) (h : (N : ℤ) + ((0 : ℕ) : ℤ) = m) (h' : (N' : ℤ) + ((0 : ℕ) : ℤ) = m)
    (y : Hgroup (structureSheafRing Y) ⊤ N (M k)) :
    (hgroupModuleShiftIso (M k') 0 N m h).hom ((Hfunctor (structureSheafRing Y) ⊤ N).map
        (eqToHom (congrArg M hk)) y) =
      (hgroupModuleShiftIso (M k') 0 N' m h').hom ((classTransport M hk hN).hom y) := by
  subst hN
  rfl

end Bridge

section Assembly

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]

omit [IsProper f] in
/-- **`cupOnProduct` is the cup product along the wedge product**, the second class transported
to the cohomological and form degree `c`. -/
theorem cupOnProduct_eq_sheafCup (p q c : ℕ)
    (a : Hgroup (structureSheafRing (pullback f f).toRingedSpace) ⊤ q
      (relativeDifferentialForms (prodStructure f) (p : ℤ)))
    (b : Hgroup (structureSheafRing (pullback f f).toRingedSpace) ⊤ (0 + c)
      (relativeDifferentialForms (prodStructure f) (((0 : ℕ) : ℤ) + (c : ℤ)))) :
    cupOnProduct f p q c a b =
      sheafCup (_root_.SheafOfModules.GradedAlgebra.mulSheaf
          (relativeDifferentialFormsAlgebra (prodStructure f)) (p : ℤ) (c : ℤ)) q c a
        ((classTransport (relativeDifferentialForms (prodStructure f))
          (show ((0 : ℕ) : ℤ) + (c : ℤ) = (c : ℤ) by push_cast; ring) (Nat.zero_add c)).hom b) := by
  unfold cupOnProduct sheafCup
  congr 2
  exact hgroupModuleShiftIso_classTransport (relativeDifferentialForms (prodStructure f))
    _ _ _ _ _ b

variable (e : ℕ) [SmoothOfRelativeDimension (e + 1) f]
  (σ : Spec (.of A) ⟶ X) (hσ : σ ≫ f = 𝟙 _) [IsClosedImmersion σ] [LocallyOfFinitePresentation σ]
  [Smooth (σ ≫ f)] [FormallyUnramified (σ ≫ f)]

/-- The normalized Gysin class `ξ ∈ H^{e+1}(X, Ω^{e+1}_{X/A})` of the section. -/
abbrev sectionClassNormalized : Hgroup (structureSheafRing X.toRingedSpace) ⊤ (e + 1)
    (relativeDifferentialForms f ((e + 1 : ℕ) : ℤ)) :=
  (classTransport (relativeDifferentialForms f)
    (show ((0 : ℕ) : ℤ) + ((e + 1 : ℕ) : ℤ) = ((e + 1 : ℕ) : ℤ) by push_cast; ring)
    (Nat.zero_add (e + 1))).hom (sectionGysinClass f σ (e + 1))

/-- The normalized Gysin class `η` of the diagonal. -/
abbrev diagonalClassNormalized : Hgroup (structureSheafRing (pullback f f).toRingedSpace) ⊤ (e + 1)
    (relativeDifferentialForms (prodStructure f) ((e + 1 : ℕ) : ℤ)) :=
  (classTransport (relativeDifferentialForms (prodStructure f))
    (show ((0 : ℕ) : ℤ) + ((e + 1 : ℕ) : ℤ) = ((e + 1 : ℕ) : ℤ) by push_cast; ring)
    (Nat.zero_add (e + 1))).hom (diagonalClass f e)

include hσ in
/-- `j^*η = ξ` for the normalized classes, `j = (σ ∘ f, id)`. -/
theorem pullbackHgroup_sectionFst_diagonalClassNormalized :
    (pullbackHgroup (CohomologyPullbackComparison.canonical
        (sectionFst f σ hσ).toLRSHom.toShHom) 0 ((e + 1 : ℕ) : ℤ) (e + 1) (by simp)
      (formsBaseChangeHom (sectionFst f σ hσ) (prodStructure f) f (𝟙 _)
        (by rw [pullback.lift_fst_assoc, Category.assoc, hσ, Category.comp_id])
        ((e + 1 : ℕ) : ℤ))).hom (diagonalClassNormalized f e) =
      sectionClassNormalized f e σ := by
  have : Smooth f := SmoothOfRelativeDimension.smooth (e + 1) f
  have h := congrArg (classTransport (relativeDifferentialForms f)
    (show ((0 : ℕ) : ℤ) + ((e + 1 : ℕ) : ℤ) = ((e + 1 : ℕ) : ℤ) by push_cast; ring)
    (Nat.zero_add (e + 1))).hom (pullbackHgroup_diagonalGysinUnitClass f (e + 1) σ hσ)
  refine Eq.trans ?_ h
  exact (classTransport_pullbackHgroup _ _ _ _ _ _ (by push_cast; ring) _ _ _ _).symm

include hσ in
/-- `j'^*η = ξ` for the normalized classes, `j' = (id, σ ∘ f)`. -/
theorem pullbackHgroup_sectionSnd_diagonalClassNormalized :
    (pullbackHgroup (CohomologyPullbackComparison.canonical
        (sectionSnd f σ hσ).toLRSHom.toShHom) 0 ((e + 1 : ℕ) : ℤ) (e + 1) (by simp)
      (formsBaseChangeHom (sectionSnd f σ hσ) (prodStructure f) f (𝟙 _)
        (by rw [pullback.lift_fst_assoc, Category.id_comp, Category.comp_id])
        ((e + 1 : ℕ) : ℤ))).hom (diagonalClassNormalized f e) =
      sectionClassNormalized f e σ := by
  have : Smooth f := SmoothOfRelativeDimension.smooth (e + 1) f
  have h := congrArg (classTransport (relativeDifferentialForms f)
    (show ((0 : ℕ) : ℤ) + ((e + 1 : ℕ) : ℤ) = ((e + 1 : ℕ) : ℤ) by push_cast; ring)
    (Nat.zero_add (e + 1))).hom (pullbackHgroup_diagonalGysinUnitClass' f (e + 1) σ hσ)
  refine Eq.trans ?_ h
  exact (classTransport_pullbackHgroup _ _ _ _ _ _ (by push_cast; ring) _ _ _ _).symm

omit [IsProper f] in
/-- The normalized class `p₂^*ξ` is the pullback along the unit followed by the canonical map on
forms. -/
theorem classTransport_sndSectionClass :
    (classTransport (relativeDifferentialForms (prodStructure f))
      (show ((0 : ℕ) : ℤ) + ((e + 1 : ℕ) : ℤ) = ((e + 1 : ℕ) : ℤ) by push_cast; ring)
      (Nat.zero_add (e + 1))).hom (sndSectionClass f e σ) =
      (pullbackHgroup (CohomologyPullbackComparison.canonical (pullback.snd f f).toLRSHom.toShHom)
        0 ((e + 1 : ℕ) : ℤ) (e + 1) (by simp)
        (formsBaseChangeHom (pullback.snd f f) f (pullback.fst f f ≫ f) (𝟙 _)
          (by rw [Category.comp_id, pullback.condition]) ((e + 1 : ℕ) : ℤ))).hom
        (sectionClassNormalized f e σ) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth (e + 1) f
  exact classTransport_pullbackHgroup _ _ _ _ _ _ (by push_cast; ring) _ _ _ _

omit [IsProper f] in
/-- The normalized class `p₁^*ξ` is the pullback along the first projection. -/
theorem classTransport_fstSectionClass :
    (classTransport (relativeDifferentialForms (prodStructure f))
      (show ((0 : ℕ) : ℤ) + ((e + 1 : ℕ) : ℤ) = ((e + 1 : ℕ) : ℤ) by push_cast; ring)
      (Nat.zero_add (e + 1))).hom (fstSectionClass f e σ) =
      (pullbackHgroup (CohomologyPullbackComparison.canonical (pullback.fst f f).toLRSHom.toShHom)
        0 ((e + 1 : ℕ) : ℤ) (e + 1) (by simp)
        (formsBaseChangeHom (pullback.fst f f) f (pullback.fst f f ≫ f) (𝟙 _)
          (by rw [Category.comp_id]) ((e + 1 : ℕ) : ℤ))).hom
        (sectionClassNormalized f e σ) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth (e + 1) f
  exact classTransport_pullbackHgroup _ _ _ _ _ _ (by push_cast; ring) _ _ _ _

omit [IsProper f] in
include hσ in
/-- `j^*p₂^*ξ = ξ`, `j = (σ ∘ f, id)` being a section of `p₂`. -/
theorem pullbackHgroup_sectionFst_sndSectionClass :
    (pullbackHgroup (CohomologyPullbackComparison.canonical
        (sectionFst f σ hσ).toLRSHom.toShHom) 0 ((e + 1 : ℕ) : ℤ) (e + 1) (by simp)
      (formsBaseChangeHom (sectionFst f σ hσ) (prodStructure f) f (𝟙 _)
        (by rw [pullback.lift_fst_assoc, Category.assoc, hσ, Category.comp_id])
        ((e + 1 : ℕ) : ℤ))).hom
      ((pullbackHgroup (CohomologyPullbackComparison.canonical (pullback.snd f f).toLRSHom.toShHom)
        0 ((e + 1 : ℕ) : ℤ) (e + 1) (by simp)
        (formsBaseChangeHom (pullback.snd f f) f (pullback.fst f f ≫ f) (𝟙 _)
          (by rw [Category.comp_id, pullback.condition]) ((e + 1 : ℕ) : ℤ))).hom
        (sectionClassNormalized f e σ)) = sectionClassNormalized f e σ := by
  have w' : sectionFst f σ hσ ≫ prodStructure f = f ≫ 𝟙 _ := by
    rw [pullback.lift_fst_assoc, Category.assoc, hσ, Category.comp_id]
  have hi : sectionFst f σ hσ ≫ pullback.snd f f = 𝟙 X := pullback.lift_snd _ _ _
  have key := pullbackHgroup_formsBaseChangeHom_retraction f (pullback.snd f f)
    (prodStructure f) (snd_comp_eq_prodStructure f) (sectionFst f σ hσ) w' hi 0 ((e + 1 : ℕ) : ℤ)
    (e + 1)
    (by simp) (e + 1)
  exact ConcreteCategory.congr_hom key (sectionClassNormalized f e σ)

omit [IsProper f] in
include hσ in
/-- `j'^*p₁^*ξ = ξ`, `j' = (id, σ ∘ f)` being a section of `p₁`. -/
theorem pullbackHgroup_sectionSnd_fstSectionClass :
    (pullbackHgroup (CohomologyPullbackComparison.canonical
        (sectionSnd f σ hσ).toLRSHom.toShHom) 0 ((e + 1 : ℕ) : ℤ) (e + 1) (by simp)
      (formsBaseChangeHom (sectionSnd f σ hσ) (prodStructure f) f (𝟙 _)
        (by rw [pullback.lift_fst_assoc, Category.id_comp, Category.comp_id])
        ((e + 1 : ℕ) : ℤ))).hom
      ((pullbackHgroup (CohomologyPullbackComparison.canonical (pullback.fst f f).toLRSHom.toShHom)
        0 ((e + 1 : ℕ) : ℤ) (e + 1) (by simp)
        (formsBaseChangeHom (pullback.fst f f) f (pullback.fst f f ≫ f) (𝟙 _)
          (by rw [Category.comp_id]) ((e + 1 : ℕ) : ℤ))).hom
        (sectionClassNormalized f e σ)) = sectionClassNormalized f e σ := by
  have w' : sectionSnd f σ hσ ≫ prodStructure f = f ≫ 𝟙 _ := by
    rw [pullback.lift_fst_assoc, Category.id_comp, Category.comp_id]
  have hi : sectionSnd f σ hσ ≫ pullback.fst f f = 𝟙 X := pullback.lift_fst _ _ _
  have key := pullbackHgroup_formsBaseChangeHom_retraction f (pullback.fst f f)
    (prodStructure f) (fst_comp_eq_prodStructure f) (sectionSnd f σ hσ) w' hi 0 ((e + 1 : ℕ) : ℤ)
    (e + 1)
    (by simp) (e + 1)
  exact ConcreteCategory.congr_hom key (sectionClassNormalized f e σ)

/-- **The identity `(★)` of [Stacks, Tag 0G8J] from the factorization of the cup products through
the two sections.** -/
theorem starIdentity_of_cupFactorsThroughSection
    (h₀ : ∀ θ : Hgroup (structureSheafRing X.toRingedSpace) ⊤ (e + 1)
        (relativeDifferentialForms f (e : ℤ)),
      cupOnProduct f e (e + 1) (e + 1) ((fstPullback f e (e + 1)).hom θ) (diagonalClass f e) =
        cupOnProduct f e (e + 1) (e + 1) ((sndPullback f e (e + 1)).hom θ) (diagonalClass f e))
    (h₁ : CupFactorsThroughSection (pullback.fst f f) (pullback.snd f f) (sectionFst f σ hσ)
      (relativeDifferentialForms f (e : ℤ)) (relativeDifferentialForms f ((e + 1 : ℕ) : ℤ)) (e + 1))
    (h₂ : CupFactorsThroughSection (pullback.snd f f) (pullback.fst f f) (sectionSnd f σ hσ)
      (relativeDifferentialForms f (e : ℤ)) (relativeDifferentialForms f ((e + 1 : ℕ) : ℤ))
        (e + 1)) :
    StarIdentity f e σ := by
  intro θ
  have hfst : (fstPullback f e (e + 1)).hom θ =
      (Hfunctor (structureSheafRing (pullback f f).toRingedSpace) ⊤ (e + 1)).map
        (fstForms f (e : ℤ))
        ((unitPullback (pullback.fst f f) (relativeDifferentialForms f (e : ℤ)) (e + 1)).hom θ) :=
    pullbackHgroup_formsBaseChangeHom_apply _ _ _ _ _ _ _ θ
  have hsnd : (sndPullback f e (e + 1)).hom θ =
      (Hfunctor (structureSheafRing (pullback f f).toRingedSpace) ⊤ (e + 1)).map
        (sndForms f (e : ℤ))
        ((unitPullback (pullback.snd f f) (relativeDifferentialForms f (e : ℤ)) (e + 1)).hom θ) :=
    pullbackHgroup_formsBaseChangeHom_apply _ _ _ _ _ _ _ θ
  have hξ₂ := (classTransport_sndSectionClass f e σ).trans
    (pullbackHgroup_formsBaseChangeHom_apply _ _ _ _ _ _ _ (sectionClassNormalized f e σ))
  have hξ₁ := (classTransport_fstSectionClass f e σ).trans
    (pullbackHgroup_formsBaseChangeHom_apply _ _ _ _ _ _ _ (sectionClassNormalized f e σ))
  have h₀' := h₀ θ
  rw [cupOnProduct_eq_sheafCup, cupOnProduct_eq_sheafCup] at h₀'
  rw [cupOnProduct_eq_sheafCup, cupOnProduct_eq_sheafCup, cupOnProduct_eq_sheafCup]
  rw [hfst, hsnd] at h₀' ⊢
  rw [hξ₁, hξ₂]
  have w₁ : sectionFst f σ hσ ≫ prodStructure f = f ≫ 𝟙 _ := by
    rw [pullback.lift_fst_assoc, Category.assoc, hσ, Category.comp_id]
  have w₂ : sectionSnd f σ hσ ≫ prodStructure f = f ≫ 𝟙 _ := by
    rw [pullback.lift_fst_assoc, Category.id_comp, Category.comp_id]
  refine sheafCup_eq_add_of_components (fstForms f (e : ℤ)) (sndForms f (e : ℤ))
    (_root_.SheafOfModules.GradedAlgebra.mulSheaf
      (relativeDifferentialFormsAlgebra (prodStructure f)) (e : ℤ) ((e + 1 : ℕ) : ℤ))
    (kunnethProj f (e + (e + 1)) (leftTopIndex e)) (kunnethProj f (e + (e + 1)) (rightTopIndex e))
    (kunnethIncl f _ (leftTopIndex e)) (kunnethIncl f _ (rightTopIndex e)) (kunneth_top_split f e)
    (sndProjection f ((e + 1 : ℕ) : ℤ)) (fstProjection f ((e + 1 : ℕ) : ℤ))
    (fstForms f ((e + 1 : ℕ) : ℤ)) (sndForms f ((e + 1 : ℕ) : ℤ))
    (𝟙 _) (signedTranspose f e (e + 1))
    ((fstForms_mul_kunnethProj f e (e + 1)).trans (Category.comp_id _).symm)
    (sndForms_mul_kunnethProj f e (e + 1))
    (sndForms_fstForms_mul_kunnethProj f e (e + 1) (by omega))
    (fstForms_sndForms_mul_kunnethProj f e (e + 1) (by omega))
    (e + 1) (e + 1) _ _ (diagonalClassNormalized f e) _ _ h₀' ?_ ?_
  · refine h₁ θ _ _ ?_
    rw [unitPullback_map_relativeProjection f (pullback.fst f f) (prodStructure f) rfl
        (pullback.snd f f) (IsPullback.of_hasPullback f f).flip (sectionFst f σ hσ) σ
        (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _) w₁ ((e + 1 : ℕ) : ℤ) (e + 1),
      unitPullback_map_relativeProjection f (pullback.fst f f) (prodStructure f) rfl
        (pullback.snd f f) (IsPullback.of_hasPullback f f).flip (sectionFst f σ hσ) σ
        (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _) w₁ ((e + 1 : ℕ) : ℤ) (e + 1),
      ← pullbackHgroup_formsBaseChangeHom_apply,
      pullbackHgroup_sectionFst_diagonalClassNormalized f e σ hσ,
      pullbackHgroup_sectionFst_sndSectionClass f e σ hσ]
  · refine h₂ θ _ _ ?_
    rw [unitPullback_map_relativeProjection f (pullback.snd f f) (prodStructure f)
        pullback.condition.symm (pullback.fst f f) (IsPullback.of_hasPullback f f)
        (sectionSnd f σ hσ) σ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) w₂
        ((e + 1 : ℕ) : ℤ) (e + 1),
      unitPullback_map_relativeProjection f (pullback.snd f f) (prodStructure f)
        pullback.condition.symm (pullback.fst f f) (IsPullback.of_hasPullback f f)
        (sectionSnd f σ hσ) σ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) w₂
        ((e + 1 : ℕ) : ℤ) (e + 1),
      ← pullbackHgroup_formsBaseChangeHom_apply,
      pullbackHgroup_sectionSnd_diagonalClassNormalized f e σ hσ,
      pullbackHgroup_sectionSnd_fstSectionClass f e σ hσ]

end Assembly

end Stacks.WeilDeRham

end
