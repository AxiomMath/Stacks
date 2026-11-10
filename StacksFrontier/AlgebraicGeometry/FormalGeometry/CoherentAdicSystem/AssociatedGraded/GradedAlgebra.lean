module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Filtration.AssociatedGraded
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedDegreeColimits
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.Immersion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Equivalence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Transition
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.KernelCokernel

/-!
# The associated graded algebra of an ideal sheaf

The restriction of a coherent adic system to an open subscheme, the associated graded algebra
`⨁ ℐ ⁿ / ℐ ⁿ⁺¹` of a quasi-coherent sheaf of ideals with the affine identifications of its
homogeneous pieces, and the inverse system of sections of a coherent adic system over an open.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Coherent

/-! ### Restriction of a coherent adic system to an open subscheme -/

section Restriction

/-- The restriction of a coherent adic system to an open subscheme. -/
public abbrev restrictSystem {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (F : CoherentAdicSystems I) (U : X.Opens) :
    CoherentAdicSystems (I.comap U.ι) :=
  ⟨F.obj ⋙ Scheme.Modules.restrictFunctor U.ι, isCoherentAdicSystem_restrict I U.ι F⟩

end Restriction

/-! ### The associated graded algebra of the ideal sheaf -/

section AlgebraConstruction

local instance moduleOfSections {X : Scheme.{u}} (M : SheafOfModules X.ringCatSheaf)
    (U : X.Opens) : Module Γ(X, U) (M.val.obj (op U)) := (M.val.obj (op U)).isModule

local instance isClosedImmersion_resLE {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (U : Y.Opens) : IsClosedImmersion (f.resLE U (f ⁻¹ᵁ U) le_rfl) := by
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  infer_instance

/-- The pushforward of a sheaf of graded algebras along a morphism of schemes. -/
private def gradedAlgebraPushforward {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf) :
    SheafOfModules.GradedAlgebra.{u, u} Y.ringCatSheaf where
  piece n := (Scheme.Modules.pushforward f).obj (A.piece n)
  mul i j :=
    { app U := (A.mul i j).app (op (f ⁻¹ᵁ U.unop))
      map_smul_left U r x y := (A.mul i j).map_smul_left _ ((f.app U.unop).hom r) x y
      map_smul_right U r x y := (A.mul i j).map_smul_right _ ((f.app U.unop).hom r) x y
      naturality g x y :=
        (A.mul i j).naturality ((TopologicalSpace.Opens.map f.base).map g.unop).op x y }
  one :=
    { val := fun U => A.one.eval (op (f ⁻¹ᵁ U.unop))
      property := by
        intro U V g
        exact A.one.property ((TopologicalSpace.Opens.map f.base).map g.unop).op }
  mul_assoc i j k U a b c := A.mul_assoc i j k _ a b c
  one_mul i U a := A.one_mul i _ a
  mul_one i U a := A.mul_one i _ a

/-- The associated graded algebra `⨁ ℐ ⁿ / ℐ ⁿ⁺¹` of a quasi-coherent ideal sheaf, read on the
ambient scheme. -/
private abbrev conormalPushforward {X : Scheme.{u}} (I : X.IdealSheafData) :=
  gradedAlgebraPushforward I.subschemeι (Stacks.Conormal.conormalAlgebra I.subschemeι).algebra

/-- The affine-local presentation of a homogeneous piece of the associated graded algebra. -/
private def conormalLocalMap {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (n : ℕ) :
    AssociatedGraded.power (M := Γ(X, U.1)) (I.ideal U) n →ₗ[Γ(X, U.1)]
      ((conormalPushforward I).piece (n : ℤ)).val.obj (op U.1) := by
  let C := Stacks.Conormal.conormalAlgebra I.subschemeι
  have hI : Stacks.Conormal.chartIdeal I.subschemeι U = I.ideal U := I.ker_subschemeι_app U
  let e : AssociatedGraded.power (M := Γ(X, U.1)) (I.ideal U) n ≃ₗ[Γ(X, U.1)]
      ↥(Stacks.Conormal.chartIdeal I.subschemeι U ^ n) :=
    LinearEquiv.ofEq _ _ (by simp [hI])
  refine { toFun := fun a => C.localMap U inferInstance n (e a)
           map_add' := by intro a b; simp only [map_add]; rfl
           map_smul' := ?_ }
  intro r a
  exact C.localMap_smul U inferInstance n r (e a) (e (r • a)) (by simp [e])

/-- Membership in a power of the chart ideal is membership in the corresponding power of the
ideal of `I`. -/
private lemma mem_chartIdeal_pow_iff {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (n : ℕ) (a : Γ(X, U.1)) :
    a ∈ Stacks.Conormal.chartIdeal I.subschemeι U ^ n ↔
      a ∈ AssociatedGraded.power (M := Γ(X, U.1)) (I.ideal U) n := by
  simp [Stacks.Conormal.chartIdeal, I.ker_subschemeι_app]

private lemma conormalLocalMap_surjective {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (n : ℕ) : Function.Surjective (conormalLocalMap I U n) := by
  let C := Stacks.Conormal.conormalAlgebra I.subschemeι
  intro x
  obtain ⟨a, ha⟩ := C.localMap_surjective U inferInstance n x
  exact ⟨⟨a, (mem_chartIdeal_pow_iff I U n a).1 a.property⟩, ha⟩

private lemma conormalLocalMap_ker {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (n : ℕ) :
    (conormalLocalMap I U n).ker =
      (AssociatedGraded.power (M := Γ(X, U.1)) (I.ideal U) (n + 1)).comap
        (AssociatedGraded.power (M := Γ(X, U.1)) (I.ideal U) n).subtype := by
  ext a
  change conormalLocalMap I U n a = 0 ↔ _
  let b : ↥(Stacks.Conormal.chartIdeal I.subschemeι U ^ n) :=
    ⟨a, (mem_chartIdeal_pow_iff I U n a).2 a.property⟩
  have h := (Stacks.Conormal.conormalAlgebra I.subschemeι).localMap_eq_zero_iff
    U inferInstance n b
  change (Stacks.Conormal.conormalAlgebra I.subschemeι).localMap U _ n b = 0 ↔
    (a : Γ(X, U.1)) ∈ AssociatedGraded.power (M := Γ(X, U.1)) (I.ideal U) (n + 1)
  simpa [Stacks.Conormal.chartIdeal, I.ker_subschemeι_app, b] using h

/-- On an affine open, the degree-`n` piece of the associated graded algebra is `I ⁿ / I ⁿ⁺¹`. -/
private def conormalPieceEquiv {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (n : ℕ) :
    ((conormalPushforward I).piece (n : ℤ)).val.obj (op U.1) ≃ₗ[Γ(X, U.1)]
      AssociatedGraded.piece (M := Γ(X, U.1)) (I.ideal U) n :=
  ((Submodule.quotEquivOfEq _ _ (conormalLocalMap_ker I U n).symm) ≪≫ₗ
    (conormalLocalMap I U n).quotKerEquivOfSurjective
      (conormalLocalMap_surjective I U n)).symm

private lemma conormalPieceEquiv_symm_mk {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (n : ℕ)
    (a : AssociatedGraded.power (M := Γ(X, U.1)) (I.ideal U) n) :
    (conormalPieceEquiv I U n).symm (AssociatedGraded.mk (I.ideal U) n a) =
      conormalLocalMap I U n a := rfl

private lemma conormalPieceEquiv_localMap {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (n : ℕ)
    (a : AssociatedGraded.power (M := Γ(X, U.1)) (I.ideal U) n) :
    conormalPieceEquiv I U n (conormalLocalMap I U n a) =
      AssociatedGraded.mk (I.ideal U) n a := by
  rw [← conormalPieceEquiv_symm_mk]
  exact (conormalPieceEquiv I U n).apply_symm_apply _

private lemma idealPower_restrict_mem {X : Scheme.{u}} (I : X.IdealSheafData)
    (n : ℕ) (U V : X.affineOpens) (h : V.1 ≤ U.1)
    (a : AssociatedGraded.power (M := Γ(X, U.1)) (I.ideal U) n) :
    X.presheaf.map (homOfLE h).op (a : Γ(X, U.1)) ∈
      AssociatedGraded.power (M := Γ(X, V.1)) (I.ideal V) n := by
  rw [AssociatedGraded.ring_power_eq, ← I.map_ideal h, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ (by simpa using a.property)

private lemma conormalLocalMap_restrict {X : Scheme.{u}} (I : X.IdealSheafData)
    (n : ℕ) (U V : X.affineOpens) (h : V.1 ≤ U.1)
    (a : AssociatedGraded.power (M := Γ(X, U.1)) (I.ideal U) n) :
    ((conormalPushforward I).piece (n : ℤ)).val.map (homOfLE h).op
      (conormalLocalMap I U n a) =
    conormalLocalMap I V n
      ⟨X.presheaf.map (homOfLE h).op a, idealPower_restrict_mem I n U V h a⟩ :=
  (Stacks.Conormal.conormalAlgebra I.subschemeι).localMap_naturality U V h
    (fun _ hx => h hx) inferInstance inferInstance n _ _ rfl

/-- Restriction between affine opens, read through the local presentations. -/
private def conormalRestriction {X : Scheme.{u}} (I : X.IdealSheafData)
    (n : ℕ) (U V : X.affineOpens) (h : V.1 ≤ U.1) :
    AssociatedGraded.piece (M := Γ(X, U.1)) (I.ideal U) n →+
      AssociatedGraded.piece (M := Γ(X, V.1)) (I.ideal V) n :=
  (conormalPieceEquiv I V n).toAddMonoidHom.comp
    (((conormalPushforward I).piece (n : ℤ)).val.map (homOfLE h).op).hom.toAddMonoidHom |>.comp
      (conormalPieceEquiv I U n).symm.toAddMonoidHom

private lemma conormalRestriction_mk {X : Scheme.{u}} (I : X.IdealSheafData)
    (n : ℕ) (U V : X.affineOpens) (h : V.1 ≤ U.1)
    (a : AssociatedGraded.power (M := Γ(X, U.1)) (I.ideal U) n) :
    conormalRestriction I n U V h (AssociatedGraded.mk (I.ideal U) n a) =
      AssociatedGraded.mk (I.ideal V) n
        ⟨X.presheaf.map (homOfLE h).op a, idealPower_restrict_mem I n U V h a⟩ := by
  change conormalPieceEquiv I V n
    (((conormalPushforward I).piece (n : ℤ)).val.map (homOfLE h).op
      ((conormalPieceEquiv I U n).symm (AssociatedGraded.mk (I.ideal U) n a))) = _
  rw [conormalPieceEquiv_symm_mk, conormalLocalMap_restrict, conormalPieceEquiv_localMap]

private lemma conormalPieceEquiv_naturality {X : Scheme.{u}} (I : X.IdealSheafData)
    (n : ℕ) (U V : X.affineOpens) (h : V.1 ≤ U.1)
    (a : ((conormalPushforward I).piece (n : ℤ)).val.obj (op U.1)) :
    conormalPieceEquiv I V n
      (((conormalPushforward I).piece (n : ℤ)).val.map (homOfLE h).op a) =
      conormalRestriction I n U V h (conormalPieceEquiv I U n a) := by
  change conormalPieceEquiv I V n
    (((conormalPushforward I).piece (n : ℤ)).val.map (homOfLE h).op a) =
      conormalPieceEquiv I V n
        (((conormalPushforward I).piece (n : ℤ)).val.map (homOfLE h).op
          ((conormalPieceEquiv I U n).symm (conormalPieceEquiv I U n a)))
  rw [LinearEquiv.symm_apply_apply]

private lemma conormalLocalMap_mul {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (n m : ℕ)
    (a : AssociatedGraded.power (M := Γ(X, U.1)) (I.ideal U) n)
    (b : AssociatedGraded.power (M := Γ(X, U.1)) (I.ideal U) m) :
    ((conormalPushforward I).mul (n : ℤ) (m : ℤ)).app (op U.1)
      (conormalLocalMap I U n a) (conormalLocalMap I U m b) =
    conormalLocalMap I U (n + m)
      ⟨(a : Γ(X, U.1)) • (b : Γ(X, U.1)),
        AssociatedGraded.smul_mem_power (I.ideal U) a.property b.property⟩ :=
  ((Stacks.Conormal.conormalAlgebra I.subschemeι).localMap_mul U
    inferInstance n m _ _ _ rfl).symm

private lemma conormalPieceEquiv_mul {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (n m : ℕ)
    (a : ((conormalPushforward I).piece (n : ℤ)).val.obj (op U.1))
    (b : ((conormalPushforward I).piece (m : ℤ)).val.obj (op U.1)) :
    HEq (conormalPieceEquiv I U (n + m)
      (((conormalPushforward I).mul (n : ℤ) (m : ℤ)).app (op U.1) a b))
      (AssociatedGraded.homogeneousSMul (I.ideal U)
        (conormalPieceEquiv I U n a) (conormalPieceEquiv I U m b)) := by
  obtain ⟨a, rfl⟩ := conormalLocalMap_surjective I U n a
  obtain ⟨b, rfl⟩ := conormalLocalMap_surjective I U m b
  rw [conormalLocalMap_mul, conormalPieceEquiv_localMap,
    conormalPieceEquiv_localMap, conormalPieceEquiv_localMap]
  rfl

private lemma conormalPushforward_negative {X : Scheme.{u}} (I : X.IdealSheafData)
    (n : ℤ) (hn : n < 0) : IsZero ((conormalPushforward I).piece n) :=
  Functor.map_isZero (Scheme.Modules.pushforward I.subschemeι)
    ((Stacks.Conormal.conormalAlgebra I.subschemeι).negative_isZero n hn)

private lemma conormalPushforward_quasicoherent {X : Scheme.{u}} (I : X.IdealSheafData)
    (n : ℤ) : ((conormalPushforward I).piece n).IsQuasicoherent := by
  have := (Stacks.Conormal.conormalAlgebra I.subschemeι).isQuasicoherent n
  exact AlgebraicGeometry.pushforward_isQuasicoherent I.subschemeι _

private lemma conormalLocalMap_one {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) :
    conormalLocalMap I U 0 ⟨1, by simp⟩ = (conormalPushforward I).one.eval (op U.1) :=
  (Stacks.Conormal.conormalAlgebra I.subschemeι).localMap_one U inferInstance _ rfl

/-- The affine identification of a conormal piece with the associated graded piece of the
ideal, as an additive equivalence. -/
private def conormalPieceAddEquiv {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (n : ℕ) :
    ((conormalPushforward I).piece (n : ℤ)).val.obj (op U.1) ≃+
      AssociatedGraded.piece (M := Γ(X, U.1)) (I.ideal U) n :=
  (conormalPieceEquiv I U n).toAddEquiv

private lemma conormalPieceAddEquiv_localMap {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (n : ℕ)
    (a : AssociatedGraded.power (M := Γ(X, U.1)) (I.ideal U) n) :
    conormalPieceAddEquiv I U n (conormalLocalMap I U n a) =
      AssociatedGraded.mk (I.ideal U) n a :=
  conormalPieceEquiv_localMap I U n a

end AlgebraConstruction

/-! ### Sections of a coherent adic system over an open -/

/-- Sections of a coherent adic system on an open subset. -/
public abbrev sectionsSystem {X : Scheme.{u}} {I : X.IdealSheafData}
    (F : CoherentAdicSystems I) (U : X.Opens) :
    ℕᵒᵖ ⥤ ModuleCat.{u} Γ(X, U) :=
  F.obj ⋙ SheafOfModules.evaluation X.ringCatSheaf (op U)

/-- Projection from the inverse limit of sections to a system term. -/
public abbrev sectionsProjection {X : Scheme.{u}} {I : X.IdealSheafData}
    (F : CoherentAdicSystems I) (U : X.Opens) (n : ℕ) :
    (limit (sectionsSystem F U) : ModuleCat.{u} Γ(X, U)) ⟶
      (sectionsSystem F U).obj (op n) :=
  limit.π (sectionsSystem F U) (op n)

section ProjectionComparison

open scoped AlgebraicGeometry

local instance moduleOfSections' {X : Scheme.{u}} (M : SheafOfModules X.ringCatSheaf)
    (U : X.Opens) : Module Γ(X, U) (M.val.obj (op U)) := (M.val.obj (op U)).isModule

end ProjectionComparison

end Stacks.Coherent

end
