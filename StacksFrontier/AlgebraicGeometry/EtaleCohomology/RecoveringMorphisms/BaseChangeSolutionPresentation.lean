module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.SolutionPresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange

/-!
# The base change of an affine chart is a solution presentation on the source

Step (3) of the proof of [Stacks Project, Tag 04I6] needs the equalizer presentation of step (2)
on the *source* side: for `X = Spec A` and `V = Spec C` étale over `Y = Spec B` with
`C = B[x₁, …, x_n]/(P₁, …, Pₙ)`, the representable sheaf `h_{X ×_Y V}` on `X_étale` must be the
equalizer of the same system `P`, its coefficients pushed along `φ : B ⟶ A`.  The source states
this by presenting `A ⊗_B C` as `A[x₁, …, x_n]/(P'₁, …, P'ₙ)` with `P'ⱼ = φ(Pⱼ)`.

No presentation of the tensor product is needed.  The `X`-morphisms `U ⟶ X ×_Y V` are the
`Y`-morphisms `U ⟶ V` by the universal property of the fibre product, and those are the
solutions of `P` over `Γ(U, ⊤)` with coefficients pushed along `B ⟶ A ⟶ Γ(U, ⊤)` — which is
exactly `AlgebraicGeometry.smallEtaleCoeff` for `ψ = φ`.  So the base change carries a
`AlgebraicGeometry.SolutionPresentation` of the *same* system over the *same* ring, twisted by
`φ`, and `AlgebraicGeometry.SolutionPresentation.existsUnique_hom` becomes available on the
source side.

## Main definitions

* `AlgebraicGeometry.smallEtaleBaseChangeHomEquiv` — the universal property of the fibre
  product, on the small étale sites: an `X`-morphism into `X ×_Y V` is a morphism to `V`
  commuting with the structure morphisms to `Y`.
* `AlgebraicGeometry.baseChangeSolutionPresentation` — the solution presentation of
  `h_{X ×_Y V}` on `X_étale`, with twist `φ = f^♯` on global functions.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable {B : BigEtaleSite.{u}} {X Y : B.Scheme} (f : X ⟶ Y)

/-! ### The universal property of the fibre product on the small étale sites -/

/-- A morphism of a full subcategory is a morphism of the ambient category. -/
def smallEtaleHomEquivOverHom {S : Scheme.{u}} {hS : B.Contains S}
    (U V : SmallEtale B S hS) : (U ⟶ V) ≃ (U.obj ⟶ V.obj) where
  toFun k := k.hom
  invFun m := ObjectProperty.homMk m
  left_inv k := by apply ObjectProperty.hom_ext; rfl
  right_inv m := rfl

/-- **An `X`-morphism into `X ×_Y V` is a morphism to `V` over `Y`.**  The universal property of
the fibre product, read on the small étale sites: the base change
`AlgebraicGeometry.smallEtaleBaseChange` is `CategoryTheory.Over.pullback`, which is right
adjoint to `CategoryTheory.Over.map`. -/
def smallEtaleBaseChangeOverHomEquiv (U : SmallEtale B X.obj X.property)
    (V : SmallEtale B Y.obj Y.property) :
    (U ⟶ (smallEtaleBaseChange B f).obj V) ≃ ((Over.map f).obj U.obj ⟶ V.obj) :=
  (smallEtaleHomEquivOverHom U ((smallEtaleBaseChange B f).obj V)).trans
    ((Over.mapPullbackAdj f).homEquiv U.obj V.obj).symm

/-- The morphism of schemes over `Y` attached to an `X`-morphism into `X ×_Y V`. -/
abbrev baseChangeSchemeHom (U : SmallEtale B X.obj X.property)
    (V : SmallEtale B Y.obj Y.property) (k : U ⟶ (smallEtaleBaseChange B f).obj V) :
    (SmallEtale.toScheme B X.obj X.property).obj U ⟶
      (SmallEtale.toScheme B Y.obj Y.property).obj V :=
  B.inclusion.map (smallEtaleBaseChangeOverHomEquiv f U V k).left

/-- The morphism of schemes `baseChangeSchemeHom f U V k : U ⟶ V` commutes with the structure
morphisms to `Y`. -/
theorem baseChangeSchemeHom_comp (U : SmallEtale B X.obj X.property)
    (V : SmallEtale B Y.obj Y.property) (k : U ⟶ (smallEtaleBaseChange B f).obj V) :
    baseChangeSchemeHom f U V k ≫ B.inclusion.map V.obj.hom =
      B.inclusion.map U.obj.hom ≫ B.inclusion.map f := by
  have hw := Over.w (smallEtaleBaseChangeOverHomEquiv f U V k)
  rw [Over.map_obj_hom] at hw
  rw [← B.inclusion.map_comp, hw, B.inclusion.map_comp]

/-- The same universal property with the morphisms read as morphisms of schemes, using that the
inclusion of the big étale site into schemes is fully faithful. -/
def smallEtaleBaseChangeSchemeHomEquiv (U : SmallEtale B X.obj X.property)
    (V : SmallEtale B Y.obj Y.property) :
    (U ⟶ (smallEtaleBaseChange B f).obj V) ≃
      {m : (SmallEtale.toScheme B X.obj X.property).obj U ⟶
          (SmallEtale.toScheme B Y.obj Y.property).obj V //
        m ≫ B.inclusion.map V.obj.hom =
          B.inclusion.map U.obj.hom ≫ B.inclusion.map f} where
  toFun k := ⟨baseChangeSchemeHom f U V k, baseChangeSchemeHom_comp f U V k⟩
  invFun m := (smallEtaleBaseChangeOverHomEquiv f U V).symm
    (Over.homMk (B.inclusion.preimage m.1) (by
      refine B.inclusion.map_injective ?_
      rw [B.inclusion.map_comp, B.inclusion.map_preimage, m.2, Over.map_obj_hom,
        B.inclusion.map_comp]))
  left_inv k := by
    refine Eq.trans (congrArg (smallEtaleBaseChangeOverHomEquiv f U V).symm ?_)
      ((smallEtaleBaseChangeOverHomEquiv f U V).symm_apply_apply k)
    refine Over.OverMorphism.ext ?_
    exact B.inclusion.preimage_map _
  right_inv m := by
    refine Subtype.ext ?_
    change B.inclusion.map
      ((smallEtaleBaseChangeOverHomEquiv f U V) ((smallEtaleBaseChangeOverHomEquiv f U V).symm
        (Over.homMk (B.inclusion.preimage m.1) _))).left = m.1
    rw [(smallEtaleBaseChangeOverHomEquiv f U V).apply_symm_apply]
    exact B.inclusion.map_preimage m.1

/-- The morphism of schemes underlying `smallEtaleBaseChangeSchemeHomEquiv f U V k` is
`baseChangeSchemeHom f U V k`. -/
@[simp]
theorem smallEtaleBaseChangeSchemeHomEquiv_apply_coe (U : SmallEtale B X.obj X.property)
    (V : SmallEtale B Y.obj Y.property) (k : U ⟶ (smallEtaleBaseChange B f).obj V) :
    (smallEtaleBaseChangeSchemeHomEquiv f U V k).1 = baseChangeSchemeHom f U V k :=
  rfl

/-- **The universal property of the fibre product is natural in the chart**, before passing to
schemes: this is naturality of the adjunction `Over.map f ⊣ Over.pullback f` in its left
variable. -/
theorem smallEtaleBaseChangeOverHomEquiv_naturality
    {U U' : SmallEtale B X.obj X.property} (k : U' ⟶ U)
    (V : SmallEtale B Y.obj Y.property) (g : U ⟶ (smallEtaleBaseChange B f).obj V) :
    (smallEtaleBaseChangeOverHomEquiv f U' V (k ≫ g)).left =
      k.hom.left ≫ (smallEtaleBaseChangeOverHomEquiv f U V g).left := by
  let g' : U.obj ⟶ (Over.pullback f).obj V.obj := g.hom
  let k' : U'.obj ⟶ U.obj := k.hom
  calc (smallEtaleBaseChangeOverHomEquiv f U' V (k ≫ g)).left
      = (((Over.mapPullbackAdj f).homEquiv U'.obj V.obj).symm (k' ≫ g')).left := rfl
    _ = ((Over.map f).map k' ≫
          ((Over.mapPullbackAdj f).homEquiv U.obj V.obj).symm g').left := by
        rw [Adjunction.homEquiv_naturality_left_symm]
    _ = k.hom.left ≫ (smallEtaleBaseChangeOverHomEquiv f U V g).left := by
        rw [Over.comp_left, Over.map_map_left]
        rfl

/-- **The universal property of the fibre product is natural in the chart.**  Precomposing an
`X`-morphism `U ⟶ X ×_Y V` with `k : U' ⟶ U` precomposes the corresponding morphism of schemes
with `k`. -/
theorem smallEtaleBaseChangeSchemeHomEquiv_naturality
    {U U' : SmallEtale B X.obj X.property} (k : U' ⟶ U)
    (V : SmallEtale B Y.obj Y.property) (g : U ⟶ (smallEtaleBaseChange B f).obj V) :
    (smallEtaleBaseChangeSchemeHomEquiv f U' V (k ≫ g)).1 =
      (SmallEtale.toScheme B X.obj X.property).map k ≫
        (smallEtaleBaseChangeSchemeHomEquiv f U V g).1 := by
  rw [smallEtaleBaseChangeSchemeHomEquiv_apply_coe,
    smallEtaleBaseChangeSchemeHomEquiv_apply_coe]
  change B.inclusion.map (smallEtaleBaseChangeOverHomEquiv f U' V (k ≫ g)).left = _
  rw [smallEtaleBaseChangeOverHomEquiv_naturality f k V g, B.inclusion.map_comp]
  rfl

/-! ### The twist of the system on the source side -/

/-- The ring map `φ : Γ(Y, ⊤) ⟶ Γ(X, ⊤)` on global functions of a morphism of schemes of the big
étale site. -/
abbrev bigEtaleAppTopHom : ↥Γ(B.inclusion.obj Y, ⊤) →+* ↥Γ(B.inclusion.obj X, ⊤) :=
  (B.inclusion.map f).appTop.hom

/-- **The coefficient map of a chart of `X_étale` twisted by `φ` is the coefficient map of that
chart read over `Y`.**  Both are the ring map induced on global functions by the composite
`U ⟶ X ⟶ Y`. -/
theorem smallEtaleCoeff_appTopHom (U : SmallEtale B X.obj X.property) :
    smallEtaleCoeff B X.obj X.property (bigEtaleAppTopHom f) U =
      (B.inclusion.map U.obj.hom ≫ B.inclusion.map f).appTop.hom := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  rfl

/-! ### The solution presentation of the base change -/

section Presentation

variable [IsAffine (B.inclusion.obj Y)] (V : SmallEtale B Y.obj Y.property)
  [IsAffine ((SmallEtale.toScheme B Y.obj Y.property).obj V)] {n : ℕ}
  (P : Fin n → MvPolynomial (Fin n) Γ(B.inclusion.obj Y, ⊤))
  (pres : Stacks.EtaleCohomology.StandardPresentationOver
    ((SmallEtale.toScheme B Y.obj Y.property).obj V) (B.inclusion.map V.obj.hom) P)

/-- **The chart-valued points of `X ×_Y V` are the solutions of the twisted system.**  The
universal property of the fibre product turns an `X`-morphism `U ⟶ X ×_Y V` into a `Y`-morphism
`U ⟶ V`, and the equalizer presentation of step (2) of the proof of [Stacks Project, Tag 04I6]
turns that into a solution of `P` over `Γ(U, ⊤)` with coefficients pushed along
`Γ(Y, ⊤) ⟶ Γ(X, ⊤) ⟶ Γ(U, ⊤)`. -/
def baseChangeHomEquivSolutions (U : SmallEtale B X.obj X.property) :
    (U ⟶ (smallEtaleBaseChange B f).obj V) ≃
      {a : Fin n → ↥Γ((SmallEtale.toScheme B X.obj X.property).obj U, ⊤) //
        MvPolynomial.IsSolution P
          (smallEtaleCoeff B X.obj X.property (bigEtaleAppTopHom f) U) a} :=
  (smallEtaleBaseChangeSchemeHomEquiv f U V).trans
    ((Stacks.EtaleCohomology.homOverEquivSolutions
        ((SmallEtale.toScheme B X.obj X.property).obj U)
        ((SmallEtale.toScheme B Y.obj Y.property).obj V)
        (B.inclusion.map V.obj.hom)
        (B.inclusion.map U.obj.hom ≫ B.inclusion.map f) P pres).trans
      (Equiv.subtypeEquivRight fun a => by rw [smallEtaleCoeff_appTopHom]))

/-- The `i`-th coordinate of the solution `baseChangeHomEquivSolutions f V P pres U g` is the
`i`-th coordinate of the solution attached by `Stacks.EtaleCohomology.homOverEquivSolutions` to the
morphism of schemes `smallEtaleBaseChangeSchemeHomEquiv f U V g`. -/
theorem baseChangeHomEquivSolutions_apply_coe (U : SmallEtale B X.obj X.property)
    (g : U ⟶ (smallEtaleBaseChange B f).obj V) (i : Fin n) :
    (baseChangeHomEquivSolutions f V P pres U g).1 i =
      (Stacks.EtaleCohomology.homOverEquivSolutions
        ((SmallEtale.toScheme B X.obj X.property).obj U)
        ((SmallEtale.toScheme B Y.obj Y.property).obj V)
        (B.inclusion.map V.obj.hom)
        (B.inclusion.map U.obj.hom ≫ B.inclusion.map f) P pres
        (smallEtaleBaseChangeSchemeHomEquiv f U V g)).1 i :=
  rfl

/-- **The base change `X ×_Y V` is a solution presentation on the source.**  This is the lower
row of the comparison diagram of step (3) of the proof of [Stacks Project, Tag 04I6]: the same
system `P` over the same ring `Γ(Y, ⊤)`, with the twist `φ` on global functions. -/
def baseChangeSolutionPresentation :
    SolutionPresentation B X.obj X.property (bigEtaleAppTopHom f) P where
  obj := (smallEtaleBaseChange B f).obj V
  equiv U := baseChangeHomEquivSolutions f V P pres U
  equiv_naturality {U U'} k g i := by
    rw [baseChangeHomEquivSolutions_apply_coe, baseChangeHomEquivSolutions_apply_coe]
    have hk : (SmallEtale.toScheme B X.obj X.property).map k ≫
        (B.inclusion.map U.obj.hom ≫ B.inclusion.map f) =
        B.inclusion.map U'.obj.hom ≫ B.inclusion.map f := by
      rw [← Category.assoc, smallEtaleStructureHom_comp B X.obj X.property k]
    have hnat := Stacks.EtaleCohomology.homOverEquivSolutions_naturality pres
      ((SmallEtale.toScheme B X.obj X.property).map k) hk
      (smallEtaleBaseChangeSchemeHomEquiv f U V g) i
    refine Eq.trans ?_ hnat
    refine congrArg (fun m => (Stacks.EtaleCohomology.homOverEquivSolutions
      ((SmallEtale.toScheme B X.obj X.property).obj U')
      ((SmallEtale.toScheme B Y.obj Y.property).obj V)
      (B.inclusion.map V.obj.hom)
      (B.inclusion.map U'.obj.hom ≫ B.inclusion.map f) P pres m).1 i) ?_
    exact Subtype.ext (smallEtaleBaseChangeSchemeHomEquiv_naturality f k V g)

/-- The object of `baseChangeSolutionPresentation f V P pres` is the base change `X ×_Y V`. -/
@[simp]
theorem baseChangeSolutionPresentation_obj :
    (baseChangeSolutionPresentation f V P pres).obj = (smallEtaleBaseChange B f).obj V :=
  rfl

end Presentation

end AlgebraicGeometry

end
