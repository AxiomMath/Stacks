module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.RepresentableSheafFork
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.SolutionSheaf

/-!
# Sheaves on a small étale site presented as the solutions of a polynomial system

Step (2) of the proof of [Stacks Project, Tag 04I6] presents the representable sheaf `h_V` of an
affine chart `V = Spec C` étale over an affine `Y = Spec B`, with `C = B[x₁, …, x_n]/(P₁, …, Pₙ)`,
as the equalizer `h_V ⟶ ∏ᵢ 𝒪_Y ⇉ ∏ⱼ 𝒪_Y` of the evaluation of the `Pⱼ` against the zero section.
Step (3) uses the *same* presentation on the source side, for the base change `X ×_Y V`, whose
ring is `A ⊗_B C = A[x₁, …, x_n]/(P'₁, …, P'ₙ)` with `P'ⱼ` the image of `Pⱼ` under `φ : B ⟶ A`.

This file isolates what both sides have in common.  A
`AlgebraicGeometry.SolutionPresentation` of a system `P` over a ring `R` on the small étale site
of `S`, relative to a ring map `ψ : R ⟶ Γ(S, ⊤)`, is an object `W` of that site together with a
natural bijection between the charts' points of `W` and the solutions of `P` over the charts,
the coefficients of `P` being pushed along `ψ` and the restriction maps.  The two sides of
step (3) are the two instances `ψ = 𝟙` (for `h_V` on `Y_étale`, which is
`AlgebraicGeometry.smallEtaleHomEquivSolutions`) and `ψ = φ` (for `h_{X ×_Y V}` on `X_étale`).

Taking the bijection as the datum is what makes the source side available without presenting
`A ⊗_B C`: the `X`-morphisms `U ⟶ X ×_Y V` are the `Y`-morphisms `U ⟶ V` by the universal
property of the fibre product, and those are the solutions of `P` over `Γ(U, ⊤)` with
coefficients pushed along `B ⟶ A ⟶ Γ(U, ⊤)` — which is exactly `ψ = φ`.  No presentation of the
tensor product is needed anywhere.

## Main definitions

* `AlgebraicGeometry.smallEtaleCoeff` — the coefficient map `R ⟶ Γ(U, ⊤)` of the system over a
  chart `U`, namely `ψ` followed by restriction.
* `AlgebraicGeometry.SolutionPresentation` — the datum above.
* `AlgebraicGeometry.SolutionPresentation.coord` — the `i`-th coordinate `h_W ⟶ 𝒪_S` of a
  chart-valued point of `W`; the `i`-th component of the map `h_W ⟶ ∏ᵢ 𝒪_S` of the source.

## Main results

* `AlgebraicGeometry.SolutionPresentation.isSolution_coord` — the coordinates of a chart-valued
  point are a solution: the fork commutes.
* `AlgebraicGeometry.SolutionPresentation.hom_ext` — a morphism of sheaves into `h_W` is
  determined by its `n` coordinates.
* `AlgebraicGeometry.SolutionPresentation.existsUnique_hom` — **the fork is a limit**: a sheaf
  with `n` maps to `𝒪_S` whose values are everywhere a solution has exactly one morphism to
  `h_W` inducing them.  This is the source's "unique dotted arrow", now available on both sides
  of step (3).
* `AlgebraicGeometry.ofStandardPresentationOver` — the instance `ψ = 𝟙` on an affine base, which
  recovers `AlgebraicGeometry.existsUnique_hom_smallEtaleYoneda_of_isSolution`.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

section Coeff

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of the small étale site of `S` commutes with the structure morphisms. -/
theorem smallEtaleStructureHom_comp {U U' : SmallEtale B S hS} (k : U' ⟶ U) :
    (SmallEtale.toScheme B S hS).map k ≫ AlgebraicGeometry.SmallEtale.schemeStructureHom B S hS U =
      AlgebraicGeometry.SmallEtale.schemeStructureHom B S hS U' :=
  (B.inclusion.map_comp k.hom.left U.obj.hom).symm.trans
    (congrArg B.inclusion.map (Over.w k.hom))

/-- Restriction along a morphism of the small étale site, on global functions. -/
abbrev smallEtaleRestrict {U U' : SmallEtale B S hS} (k : U' ⟶ U) :
    ↥Γ((SmallEtale.toScheme B S hS).obj U, ⊤) →+*
      ↥Γ((SmallEtale.toScheme B S hS).obj U', ⊤) :=
  ((SmallEtale.toScheme B S hS).map k).appTop.hom

variable {R : Type u} [CommRing R] (ψ : R →+* ↥Γ(S, ⊤))

/-- **The coefficients of the system over a chart.**  A ring map `ψ : R ⟶ Γ(S, ⊤)` and a chart
`U` of the small étale site of `S` give a ring map `R ⟶ Γ(U, ⊤)`, namely `ψ` followed by
restriction along the structure morphism of `U`. -/
def smallEtaleCoeff (U : SmallEtale B S hS) :
    R →+* ↥Γ((SmallEtale.toScheme B S hS).obj U, ⊤) :=
  (AlgebraicGeometry.SmallEtale.schemeStructureHom B S hS U).appTop.hom.comp ψ

/-- The coefficient maps of `AlgebraicGeometry.smallEtaleCoeff` are compatible with
restriction. -/
theorem smallEtaleCoeff_comp {U U' : SmallEtale B S hS} (k : U' ⟶ U) :
    (smallEtaleRestrict B S hS k).comp (smallEtaleCoeff B S hS ψ U) =
      smallEtaleCoeff B S hS ψ U' := by
  have h : (AlgebraicGeometry.SmallEtale.schemeStructureHom B S hS U).appTop ≫
      ((SmallEtale.toScheme B S hS).map k).appTop =
      (AlgebraicGeometry.SmallEtale.schemeStructureHom B S hS U').appTop := by
    rw [← Scheme.Hom.comp_appTop, smallEtaleStructureHom_comp]
  have h' := congrArg CommRingCat.Hom.hom h
  rw [CommRingCat.hom_comp] at h'
  rw [smallEtaleCoeff, smallEtaleCoeff, ← h', RingHom.comp_assoc]

/-- Restricting a solution of the system over a chart gives a solution over a smaller chart. -/
theorem isSolution_smallEtaleRestrict {n : ℕ} (P : Fin n → MvPolynomial (Fin n) R)
    {U U' : SmallEtale B S hS} (k : U' ⟶ U)
    {a : Fin n → ↥Γ((SmallEtale.toScheme B S hS).obj U, ⊤)}
    (ha : MvPolynomial.IsSolution P (smallEtaleCoeff B S hS ψ U) a) :
    MvPolynomial.IsSolution P (smallEtaleCoeff B S hS ψ U')
      (fun i => smallEtaleRestrict B S hS k (a i)) :=
  (smallEtaleCoeff_comp B S hS ψ k) ▸
    MvPolynomial.isSolution_comp _ (smallEtaleRestrict B S hS k) ha

end Coeff

/-- **A sheaf on the small étale site presented as the solution sheaf of a polynomial system.**
Let `S` be a scheme of a big étale site, let `ψ : R ⟶ Γ(S, ⊤)` be a ring map and let
`P₁, …, Pₙ ∈ R[x₁, …, x_n]`.  A solution presentation is an object `W` of the small étale site of
`S` whose chart-valued points are, naturally in the chart, the solutions of the system `P` over
the chart's global functions, with the coefficients of `P` pushed along `ψ` and restriction.

This is the datum step (2) of the proof of [Stacks Project, Tag 04I6] produces from a standard
presentation of an affine chart, and which step (3) needs on both the source and the target. -/
structure SolutionPresentation (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {R : Type u} [CommRing R] (ψ : R →+* ↥Γ(S, ⊤)) {n : ℕ}
    (P : Fin n → MvPolynomial (Fin n) R) where
  /-- The presented object of the small étale site. -/
  obj : SmallEtale B S hS
  /-- Its chart-valued points are the solutions of the system over the chart. -/
  equiv (U : SmallEtale B S hS) :
    (U ⟶ obj) ≃
      {a : Fin n → ↥Γ((SmallEtale.toScheme B S hS).obj U, ⊤) //
        MvPolynomial.IsSolution P (smallEtaleCoeff B S hS ψ U) a}
  /-- The identification is natural in the chart. -/
  equiv_naturality {U U' : SmallEtale B S hS} (k : U' ⟶ U) (f : U ⟶ obj) (i : Fin n) :
    (equiv U' (k ≫ f)).1 i = smallEtaleRestrict B S hS k ((equiv U f).1 i)

namespace SolutionPresentation

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {R : Type u} [CommRing R] {ψ : R →+* ↥Γ(S, ⊤)} {n : ℕ}
  {P : Fin n → MvPolynomial (Fin n) R} (pres : SolutionPresentation B S hS ψ P)

/-- Two morphisms of sheaves of types which agree on every section are equal. -/
private theorem sheaf_hom_ext_of_app_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    {F G : Sheaf J (Type u)} {φ χ : F ⟶ G}
    (h : ∀ (U : Cᵒᵖ) (t : F.obj.obj U), φ.hom.app U t = χ.hom.app U t) : φ = χ :=
  Sheaf.hom_ext (NatTrans.ext (funext fun U => TypeCat.homEquiv.injective (funext (h U))))

/-- The representable sheaf `h_W` of the presented object. -/
abbrev sheaf : Sheaf (SmallEtale.topology B S hS) (Type u) :=
  (smallEtaleYoneda B S hS).obj pres.obj

/-- **The `i`-th coordinate of a chart-valued point of `W`, as a morphism of sheaves
`h_W ⟶ 𝒪_S`.**  This is the `i`-th component of the map `h_W ⟶ ∏ᵢ 𝒪_S` of step (2) of the proof
of [Stacks Project, Tag 04I6]. -/
def coord (i : Fin n) : pres.sheaf ⟶ setStructureSheaf B S hS where
  hom :=
    { app := fun U => TypeCat.ofHom fun f => (pres.equiv U.unop f).1 i
      naturality := fun U U' (k : U ⟶ U') => TypeCat.homEquiv.injective (funext fun f =>
        pres.equiv_naturality k.unop f i) }

/-- The value of the `i`-th coordinate on a chart-valued point `f` of `W` is the `i`-th entry of
the solution corresponding to `f`. -/
@[simp]
theorem coord_hom_app (i : Fin n) (U : (SmallEtale B S hS)ᵒᵖ) (f : U.unop ⟶ pres.obj) :
    (pres.coord i).hom.app U f = (pres.equiv U.unop f).1 i :=
  rfl

/-- **The fork `h_W ⟶ ∏ᵢ 𝒪_S ⇉ ∏ⱼ 𝒪_S` commutes.**  The `n` coordinates of a chart-valued point
of `W` are a solution of the presented system. -/
theorem isSolution_coord (U : (SmallEtale B S hS)ᵒᵖ) (f : U.unop ⟶ pres.obj) :
    MvPolynomial.IsSolution P (smallEtaleCoeff B S hS ψ U.unop)
      (fun i => (pres.coord i).hom.app U f) :=
  (pres.equiv U.unop f).2

/-- Two morphisms of sheaves into `h_W` which agree on all `n` coordinates are equal. -/
theorem hom_ext {F : Sheaf (SmallEtale.topology B S hS) (Type u)} (φ χ : F ⟶ pres.sheaf)
    (h : ∀ i, φ ≫ pres.coord i = χ ≫ pres.coord i) :
    φ = χ := by
  refine sheaf_hom_ext_of_app_apply fun U t =>
    (pres.equiv U.unop).injective (Subtype.ext (funext fun i => ?_))
  exact congrArg (fun α : F ⟶ setStructureSheaf B S hS => α.hom.app U t) (h i)

/-- **The fork `h_W ⟶ ∏ᵢ 𝒪_S ⇉ ∏ⱼ 𝒪_S` is a limit.**  A sheaf of sets `F` on the small étale
site of `S` equipped with `n` morphisms `s₁, …, sₙ : F ⟶ 𝒪_S` whose values over every chart are
a solution of the presented system admits exactly one morphism `F ⟶ h_W` whose `i`-th coordinate
is `sᵢ`.

This is the "unique dotted arrow" of step (2) of the proof of [Stacks Project, Tag 04I6]. -/
theorem existsUnique_hom (F : Sheaf (SmallEtale.topology B S hS) (Type u))
    (s : Fin n → (F ⟶ setStructureSheaf B S hS))
    (hs : ∀ (U : (SmallEtale B S hS)ᵒᵖ) (t : F.obj.obj U),
      MvPolynomial.IsSolution P (smallEtaleCoeff B S hS ψ U.unop)
        (fun i => (s i).hom.app U t)) :
    ∃! φ : F ⟶ pres.sheaf, ∀ i, φ ≫ pres.coord i = s i := by
  let a : ∀ U : (SmallEtale B S hS)ᵒᵖ, F.obj.obj U → (U.unop ⟶ pres.obj) :=
    fun U t => (pres.equiv U.unop).symm ⟨fun i => (s i).hom.app U t, hs U t⟩
  have hcoord : ∀ (U : (SmallEtale B S hS)ᵒᵖ) (t : F.obj.obj U) (i : Fin n),
      (pres.equiv U.unop (a U t)).1 i = (s i).hom.app U t :=
    fun U t i => congrFun (congrArg Subtype.val
      ((pres.equiv U.unop).apply_symm_apply ⟨fun j => (s j).hom.app U t, hs U t⟩)) i
  have hnat : ∀ (U U' : (SmallEtale B S hS)ᵒᵖ) (k : U ⟶ U') (t : F.obj.obj U),
      a U' (F.obj.map k t) = k.unop ≫ a U t := by
    intro U U' k t
    refine (pres.equiv U'.unop).injective (Subtype.ext (funext fun i => ?_))
    exact ((hcoord U' (F.obj.map k t) i).trans
      (ConcreteCategory.congr_hom ((s i).hom.naturality k) t)).trans
      ((pres.equiv_naturality k.unop (a U t) i).trans
        (congrArg (smallEtaleRestrict B S hS k.unop) (hcoord U t i))).symm
  refine ⟨⟨{ app := fun U => TypeCat.ofHom (a U)
             naturality := fun U U' k =>
               TypeCat.homEquiv.injective (funext fun t => hnat U U' k t) }⟩, fun i => ?_, ?_⟩
  · exact sheaf_hom_ext_of_app_apply fun U t => hcoord U t i
  · intro χ hχ
    refine sheaf_hom_ext_of_app_apply fun U t => ?_
    refine Eq.trans ((pres.equiv U.unop).symm_apply_apply (χ.hom.app U t)).symm ?_
    refine congrArg (pres.equiv U.unop).symm (Subtype.ext (funext fun i => ?_))
    exact congrArg (fun α : F ⟶ setStructureSheaf B S hS => α.hom.app U t) (hχ i)

/-- The morphism `F ⟶ h_W` of `AlgebraicGeometry.SolutionPresentation.existsUnique_hom`. -/
def homOfIsSolution (F : Sheaf (SmallEtale.topology B S hS) (Type u))
    (s : Fin n → (F ⟶ setStructureSheaf B S hS))
    (hs : ∀ (U : (SmallEtale B S hS)ᵒᵖ) (t : F.obj.obj U),
      MvPolynomial.IsSolution P (smallEtaleCoeff B S hS ψ U.unop)
        (fun i => (s i).hom.app U t)) :
    F ⟶ pres.sheaf :=
  (pres.existsUnique_hom F s hs).choose

/-- The `i`-th coordinate of `homOfIsSolution F s hs` is `s i`. -/
@[simp]
theorem homOfIsSolution_comp_coord (F : Sheaf (SmallEtale.topology B S hS) (Type u))
    (s : Fin n → (F ⟶ setStructureSheaf B S hS))
    (hs : ∀ (U : (SmallEtale B S hS)ᵒᵖ) (t : F.obj.obj U),
      MvPolynomial.IsSolution P (smallEtaleCoeff B S hS ψ U.unop)
        (fun i => (s i).hom.app U t)) (i : Fin n) :
    pres.homOfIsSolution F s hs ≫ pres.coord i = s i :=
  (pres.existsUnique_hom F s hs).choose_spec.1 i

end SolutionPresentation

/-! ### The instance supplied by a standard presentation on an affine base

For `Y` affine and `V` an affine chart with a standard presentation of `Γ(V, ⊤)` over `Γ(Y, ⊤)`,
`AlgebraicGeometry.smallEtaleHomEquivSolutions` is a solution presentation with `ψ = 𝟙`. -/

section Affine

variable {B : BigEtaleSite.{u}} {Y : B.Scheme} [IsAffine (B.inclusion.obj Y)]
  (V : SmallEtale B Y.obj Y.property)
  [IsAffine ((SmallEtale.toScheme B Y.obj Y.property).obj V)] {n : ℕ}
  (P : Fin n → MvPolynomial (Fin n) Γ(B.inclusion.obj Y, ⊤))
  (pres : Stacks.EtaleCohomology.StandardPresentationOver
    ((SmallEtale.toScheme B Y.obj Y.property).obj V) (B.inclusion.map V.obj.hom) P)

omit [IsAffine (B.inclusion.obj Y)] in
/-- With `ψ = 𝟙`, the coefficient map of a chart is restriction along its structure morphism. -/
theorem smallEtaleCoeff_id (U : SmallEtale B Y.obj Y.property) :
    smallEtaleCoeff B Y.obj Y.property (RingHom.id ↥Γ(B.inclusion.obj Y, ⊤)) U =
      (B.inclusion.map U.obj.hom).appTop.hom :=
  RingHom.comp_id _

/-- **A standard presentation of an affine chart is a solution presentation.**  This is
`AlgebraicGeometry.smallEtaleHomEquivSolutions`, which identifies the chart-valued points of `V`
with the solutions of the presented system, repackaged as the datum both sides of step (3) of the
proof of [Stacks Project, Tag 04I6] consume. -/
def ofStandardPresentationOver :
    SolutionPresentation B Y.obj Y.property
      (RingHom.id ↥Γ(B.inclusion.obj Y, ⊤)) P where
  obj := V
  equiv U := (smallEtaleHomEquivSolutions V P pres U).trans
    (Equiv.subtypeEquivRight fun a => by
      rw [smallEtaleCoeff_id])
  equiv_naturality k f i := smallEtaleHomEquivSolutions_naturality V P pres k f i

/-- The presented object of `ofStandardPresentationOver V P pres` is `V`. -/
@[simp]
theorem ofStandardPresentationOver_obj :
    (ofStandardPresentationOver V P pres).obj = V :=
  rfl

/-- The coordinates of a chart-valued point of `V` under `ofStandardPresentationOver V P pres` are
those given by `AlgebraicGeometry.smallEtaleHomEquivSolutions`. -/
@[simp]
theorem ofStandardPresentationOver_equiv_coe (U : SmallEtale B Y.obj Y.property) (f : U ⟶ V)
    (i : Fin n) :
    ((ofStandardPresentationOver V P pres).equiv U f).1 i =
      (smallEtaleHomEquivSolutions V P pres U f).1 i :=
  rfl

end Affine

end AlgebraicGeometry

end
