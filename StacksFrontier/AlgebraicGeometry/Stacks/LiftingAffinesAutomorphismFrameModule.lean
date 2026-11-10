module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesAutomorphismModuleLaw
public import StacksFrontier.CategoryTheory.Sites.Gerbe.BandModuleOfBanding
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesFamilyDescentAux

/-!
# The `𝒪`-module structure on the automorphism groups of smooth lifts (Stacks 0CKG (2))

For an object `x` of the fibre over an étale open `U` of `W` of the category of smooth lifts
(`AlgebraicGeometry.Stack.EtaleSmoothLift`, Stacks 0CJP), the endomorphisms of `x` in the fibre
are parametrized by `Hom(Δ^*Ω, 𝒞_{U/U'})` (`AlgebraicGeometry.Stack.EtaleSmoothLift.paramOf`), on
which `Γ(U, 𝒪_U)` acts by multiplication on `𝒞` (Stacks 0CKH). Transporting the action gives a
`Γ(U, 𝒪_U)`-module structure on `Aut(x)` (`AlgebraicGeometry.Stack.EtaleSmoothLift.frameSmul`, the
group law being composition), and the module laws, the linearity of conjugation by isomorphisms of
the fibre, and the semilinearity of pullback hold
(`AlgebraicGeometry.Stack.EtaleSmoothLift.frameSmul_conj`,
`AlgebraicGeometry.Stack.EtaleSmoothLift.pullbackFiberHom_frameSmul`): the inputs of the descent
of module structures to the band, `CategoryTheory.Functor.exists_bandSmul`.

## References

* [Stacks Project, Tag 0CKG](https://stacks.math.columbia.edu/tag/0CKG)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack.EtaleSmoothLift

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} {ι : 𝒳 ⟶ 𝒳'} {hι : IsThickening ι}
  {W : AlgebraicSpaces B S hS}
  {x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳}
  {hx : AlgebraicStacks.IsSmooth B S hS x}

attribute [local irreducible] Space.modulePullback Space.smallEtaleRingedSite Space.structureSheaf
  Space.smallEtaleRingedToposHom Space.chartFunctor Space.comparisonFunctor
  Space.modulePullbackCompIso

variable (B S hS W) in
/-- The structure sheaf of the spaces-étale site of `W`, with commutativity forgotten: the ring
`Γ(U, 𝒪_U)` of an étale open `U` of `W`. -/
abbrev bandRing : (Space.SpacesEtale B S hS W)ᵒᵖ ⥤ RingCat.{u + 1} :=
  (Space.SpacesEtale.structureSheaf B S hS W).obj ⋙ forget₂ CommRingCat RingCat

variable (hι₁ : AlgebraicStacks.IsFirstOrderThickening B S hS ι)

/-- A function on `U`, read on the base of an object of the fibre over `U`. -/
def frameScalar {U : Space.SpacesEtale B S hS W}
    (ζ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U)
    (r : (bandRing B S hS W).obj (op U)) : Space.globalFunctions' B S hS ζ.1.base.obj.left.1 :=
  ((bandRing B S hS W).map (eqToHom (congrArg op ζ.2.symm))).hom r

/-- **The parameter of an endomorphism in a fibre**, Stacks 0CKH. -/
def paramOf {U : Space.SpacesEtale B S hS W}
    {ζ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U} (α : ζ ⟶ ζ) :
    LiftsActingGroup hι₁ ζ.1 :=
  autParam hι₁ ζ.1 (Functor.Fiber.fiberInclusion.map α) (base_eq_id_of_fiber α)

/-- An endomorphism in the fibre is determined by its parameter. -/
theorem paramOf_injective {U : Space.SpacesEtale B S hS W}
    {ζ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U} {α β : ζ ⟶ ζ}
    (h : paramOf hι₁ α = paramOf hι₁ β) : α = β :=
  Functor.Fiber.fiberInclusion.map_injective
    (autParam_injective hι₁ ζ.1 (base_eq_id_of_fiber α) (base_eq_id_of_fiber β) h)

/-- The parameter of a composite of endomorphisms in the fibre is the sum of their parameters. -/
theorem paramOf_comp {U : Space.SpacesEtale B S hS W}
    {ζ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U} (α β : ζ ⟶ ζ) :
    paramOf hι₁ (α ≫ β) = paramOf hι₁ α + paramOf hι₁ β :=
  autParam_comp hι₁ ζ.1 _ _ (base_eq_id_of_fiber α) (base_eq_id_of_fiber β)

/-- The parameter of the identity in the fibre is zero. -/
theorem paramOf_id {U : Space.SpacesEtale B S hS W}
    (ζ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) :
    paramOf hι₁ (𝟙 ζ) = 0 :=
  autParam_id hι₁ ζ.1

/-- The endomorphism of `ζ` given by a lift lies over the identity of `U`. -/
theorem isHomLift_homOfLift {U : Space.SpacesEtale B S hS W}
    (ζ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) (s : Lifts hι₁ ζ.1) :
    (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsHomLift (𝟙 U) (homOfLift hι₁ ζ.1 s) :=
  IsHomLift.of_fac _ (𝟙 U) (homOfLift hι₁ ζ.1 s) ζ.2 ζ.2 (by
    change 𝟙 U = eqToHom _ ≫ 𝟙 ζ.1.base ≫ eqToHom _
    exact ((congrArg (_ ≫ ·) (Category.id_comp _)).trans
      ((eqToHom_trans _ _).trans (eqToHom_refl _ _))).symm)

/-- **The endomorphism with a given parameter**, in the fibre. -/
def ofParam {U : Space.SpacesEtale B S hS W}
    (ζ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) (θ : LiftsActingGroup hι₁ ζ.1) :
    ζ ⟶ ζ :=
  haveI := isHomLift_homOfLift hι₁ ζ (liftsEquiv hι₁ ζ.1 θ)
  Functor.Fiber.homMk _ U (homOfLift hι₁ ζ.1 (liftsEquiv hι₁ ζ.1 θ))

/-- The endomorphism with parameter `θ` has parameter `θ`. -/
theorem paramOf_ofParam {U : Space.SpacesEtale B S hS W}
    (ζ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) (θ : LiftsActingGroup hι₁ ζ.1) :
    paramOf hι₁ (ofParam hι₁ ζ θ) = θ :=
  autParam_homOfLift hι₁ ζ.1 θ

/-- Multiplication by a function on `U` on the target `𝒞_{U/U'}` of the parameters of `ζ`. -/
def frameMul {U : Space.SpacesEtale B S hS W}
    (ζ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U)
    (r : (bandRing B S hS W).obj (op U)) :
    Space.conormalModule B S hS ζ.1.ambient (liftsZ hι₁ ζ.1) ⟶
      Space.conormalModule B S hS ζ.1.ambient (liftsZ hι₁ ζ.1) :=
  Space.globalFunctionsSmul B S hS (X := liftsZSpace hι₁ ζ.1)
    (liftsScalar hι₁ ζ.1 (frameScalar ζ r))
    (Space.conormalModule B S hS ζ.1.ambient (liftsZ hι₁ ζ.1))

/-- **The `Γ(U, 𝒪_U)`-module structure on the automorphisms of an object of the fibre**: `r · α`
has parameter the parameter of `α` multiplied by `r` on `𝒞_{U/U'}`. -/
def frameSmul {U : Space.SpacesEtale B S hS W}
    (ζ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U)
    (r : (bandRing B S hS W).obj (op U)) (α : ζ ⟶ ζ) : ζ ⟶ ζ :=
  ofParam hι₁ ζ (paramOf hι₁ α ≫ frameMul hι₁ ζ r)

/-- The parameter of `r · α` is the parameter of `α` followed by multiplication by `r`. -/
theorem paramOf_frameSmul {U : Space.SpacesEtale B S hS W}
    (ζ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U)
    (r : (bandRing B S hS W).obj (op U)) (α : ζ ⟶ ζ) :
    paramOf hι₁ (frameSmul hι₁ ζ r α) = paramOf hι₁ α ≫ frameMul hι₁ ζ r :=
  paramOf_ofParam hι₁ ζ _

section Laws

variable {U : Space.SpacesEtale B S hS W}
  (ζ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U)

/-- Multiplication by `r` is multiplication by any function `t` equal to `r` read on `ζ.1`. -/
private theorem frameMul_eq_smul (r : (bandRing B S hS W).obj (op U))
    {t : Space.globalFunctions' B S hS (liftsZSpace hι₁ ζ.1).1}
    (h : Space.globalFunctionsMap B S hS (zProjection hι₁ ζ.1) (frameScalar ζ r) = t) :
    frameMul hι₁ ζ r = Space.globalFunctionsSmul B S hS (X := liftsZSpace hι₁ ζ.1) t
      (Space.conormalModule B S hS ζ.1.ambient (liftsZ hι₁ ζ.1)) :=
  congrArg (Space.globalFunctionsSmul B S hS (X := liftsZSpace hι₁ ζ.1) · _) h

/-- Multiplication by `r + s` is the sum of multiplication by `r` and by `s`. -/
theorem frameMul_add (r s : (bandRing B S hS W).obj (op U)) :
    frameMul hι₁ ζ (r + s) = frameMul hι₁ ζ r + frameMul hι₁ ζ s :=
  (frameMul_eq_smul hι₁ ζ _ ((congrArg _ (map_add _ r s)).trans (map_add _ _ _))).trans
    (Space.globalFunctionsSmul_add B S hS _ _ _)

/-- Multiplication by `0` is the zero morphism. -/
theorem frameMul_zero : frameMul hι₁ ζ 0 = 0 :=
  (frameMul_eq_smul hι₁ ζ _ ((congrArg _ (map_zero _)).trans (map_zero _))).trans
    (Space.globalFunctionsSmul_zero B S hS _)

/-- Multiplication by `1` is the identity. -/
theorem frameMul_one : frameMul hι₁ ζ 1 = 𝟙 _ :=
  (frameMul_eq_smul hι₁ ζ _ ((congrArg _ (map_one _)).trans (map_one _))).trans
    (Space.globalFunctionsSmul_one B S hS _)

/-- Multiplication by `r * s` is multiplication by `s` followed by multiplication by `r`. -/
theorem frameMul_mul (r s : (bandRing B S hS W).obj (op U)) :
    frameMul hι₁ ζ (r * s) = frameMul hι₁ ζ s ≫ frameMul hι₁ ζ r :=
  (frameMul_eq_smul hι₁ ζ _ ((congrArg _ (map_mul _ r s)).trans (map_mul _ _ _))).trans
    (Space.globalFunctionsSmul_mul B S hS _ _ _)

/-- `r · α = β` as soon as the parameter of `β` is the parameter of `α` times `r`. -/
private theorem frameSmul_eq_of_paramOf_eq (r : (bandRing B S hS W).obj (op U)) {α β : ζ ⟶ ζ}
    (h : paramOf hι₁ α ≫ frameMul hι₁ ζ r = paramOf hι₁ β) : frameSmul hι₁ ζ r α = β :=
  paramOf_injective hι₁ ((paramOf_frameSmul hι₁ ζ r α).trans h)

/-- The action of `r` respects composition of automorphisms: `r · (α ≫ β) = r · α ≫ r · β`. -/
theorem frameSmul_comp (r : (bandRing B S hS W).obj (op U)) (α β : ζ ⟶ ζ) :
    frameSmul hι₁ ζ r (α ≫ β) = frameSmul hι₁ ζ r α ≫ frameSmul hι₁ ζ r β :=
  frameSmul_eq_of_paramOf_eq hι₁ ζ r
    ((congrArg (· ≫ frameMul hι₁ ζ r) (paramOf_comp hι₁ α β)).trans
    ((Preadditive.add_comp _ _ _ _ _ _).trans ((congrArg₂ (· + ·)
      (paramOf_frameSmul hι₁ ζ r α).symm (paramOf_frameSmul hι₁ ζ r β).symm).trans
      (paramOf_comp hι₁ _ _).symm)))

/-- The action of `r` fixes the identity. -/
theorem frameSmul_id (r : (bandRing B S hS W).obj (op U)) : frameSmul hι₁ ζ r (𝟙 ζ) = 𝟙 ζ :=
  frameSmul_eq_of_paramOf_eq hι₁ ζ r
    ((congrArg (· ≫ frameMul hι₁ ζ r) (paramOf_id hι₁ ζ)).trans
      ((Limits.zero_comp).trans (paramOf_id hι₁ ζ).symm))

/-- The action is additive in the scalar: `(r + s) · α = r · α ≫ s · α`. -/
theorem frameSmul_add (r s : (bandRing B S hS W).obj (op U)) (α : ζ ⟶ ζ) :
    frameSmul hι₁ ζ (r + s) α = frameSmul hι₁ ζ r α ≫ frameSmul hι₁ ζ s α :=
  frameSmul_eq_of_paramOf_eq hι₁ ζ _
    ((congrArg (paramOf hι₁ α ≫ ·) (frameMul_add hι₁ ζ r s)).trans
      ((Preadditive.comp_add _ _ _ _ _ _).trans ((congrArg₂ (· + ·)
        (paramOf_frameSmul hι₁ ζ r α).symm (paramOf_frameSmul hι₁ ζ s α).symm).trans
        (paramOf_comp hι₁ _ _).symm)))

/-- The scalar `0` acts by sending every automorphism to the identity. -/
theorem frameSmul_zero (α : ζ ⟶ ζ) : frameSmul hι₁ ζ 0 α = 𝟙 ζ :=
  frameSmul_eq_of_paramOf_eq hι₁ ζ 0
    ((congrArg (paramOf hι₁ α ≫ ·) (frameMul_zero hι₁ ζ)).trans
      ((Limits.comp_zero).trans (paramOf_id hι₁ ζ).symm))

/-- The scalar `1` acts trivially: `1 · α = α`. -/
theorem frameSmul_one (α : ζ ⟶ ζ) : frameSmul hι₁ ζ 1 α = α :=
  frameSmul_eq_of_paramOf_eq hι₁ ζ 1
    ((congrArg (paramOf hι₁ α ≫ ·) (frameMul_one hι₁ ζ)).trans (Category.comp_id _))

/-- The action is associative: `(r * s) · α = r · (s · α)`. -/
theorem frameSmul_mul (r s : (bandRing B S hS W).obj (op U)) (α : ζ ⟶ ζ) :
    frameSmul hι₁ ζ (r * s) α = frameSmul hι₁ ζ r (frameSmul hι₁ ζ s α) :=
  frameSmul_eq_of_paramOf_eq hι₁ ζ _
    ((congrArg (paramOf hι₁ α ≫ ·) (frameMul_mul hι₁ ζ r s)).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ frameMul hι₁ ζ r)
        (paramOf_frameSmul hι₁ ζ s α).symm).trans (paramOf_frameSmul hι₁ ζ r _).symm)))

end Laws

section Compat

attribute [local instance] isFibered_proj

/-- Functions on `U` read on the base of `ζ`, pulled back along a morphism `m` of smooth lifts
lying over `g : V ⟶ U`, are functions on `V` read on the base of `ζ'`. -/
theorem globalFunctionsMap_frameScalar {U V : Space.SpacesEtale B S hS W}
    (ζ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U)
    (ζ' : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber V) (g : V ⟶ U)
    (m : ζ'.1 ⟶ ζ.1) (hm : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsHomLift g m)
    (r : (bandRing B S hS W).obj (op U)) :
    Space.globalFunctionsMap B S hS (Hom.base m).hom.left (frameScalar ζ r) =
      frameScalar ζ' (((bandRing B S hS W).map g.op).hom r) := by
  obtain ⟨ξ, rfl⟩ := ζ
  obtain ⟨ξ', rfl⟩ := ζ'
  have hg : Hom.base m = g := (IsHomLift.eq_of_isHomLift (p := proj) g m).symm
  subst hg
  unfold frameScalar
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, RingCat.hom_id, RingHom.id_apply]
  rfl

variable {U : Space.SpacesEtale B S hS W}

/-- If `α'` and `β'` are intertwined with `α` and `β` by a morphism `m` of lifts over `g` and
`r · α = β`, then `(g^* r) · α' = β'`. -/
private theorem frameSmul_eq_of_comp_eq {V : Space.SpacesEtale B S hS W} (g : V ⟶ U)
    {ζ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U}
    {ζ' : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber V} (m : ζ'.1 ⟶ ζ.1)
    (hm : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsHomLift g m)
    (r : (bandRing B S hS W).obj (op U)) {α β : ζ ⟶ ζ} {α' β' : ζ' ⟶ ζ'}
    (hα : (Functor.Fiber.fiberInclusion.map α').comp m =
      m.comp (Functor.Fiber.fiberInclusion.map α))
    (hβ : (Functor.Fiber.fiberInclusion.map β').comp m =
      m.comp (Functor.Fiber.fiberInclusion.map β))
    (h : frameSmul hι₁ ζ r α = β) :
    frameSmul hι₁ ζ' (((bandRing B S hS W).map g.op).hom r) α' = β' := by
  have key := autParam_eq_of_comp_eq hι₁ m (Functor.Fiber.fiberInclusion.map α')
    (Functor.Fiber.fiberInclusion.map β') (Functor.Fiber.fiberInclusion.map α)
    (Functor.Fiber.fiberInclusion.map β) (base_eq_id_of_fiber _) (base_eq_id_of_fiber _)
    (base_eq_id_of_fiber _) (base_eq_id_of_fiber _) hα hβ (frameScalar ζ r)
    (h ▸ paramOf_frameSmul hι₁ ζ r α)
  rw [globalFunctionsMap_frameScalar ζ ζ' g m hm r] at key
  exact paramOf_injective hι₁ ((paramOf_frameSmul hι₁ ζ' _ α').trans key.symm)

/-- **Pullback of automorphisms is semilinear.** -/
theorem pullbackFiberHom_frameSmul {V : Space.SpacesEtale B S hS W} (g : V ⟶ U)
    (ζ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U)
    (r : (bandRing B S hS W).obj (op U)) (α : ζ ⟶ ζ) :
    Functor.pullbackFiberHom (frameSmul hι₁ ζ r α) g =
      frameSmul hι₁ (Functor.pullbackFiber proj ζ g) (((bandRing B S hS W).map g.op).hom r)
        (Functor.pullbackFiberHom α g) :=
  (frameSmul_eq_of_comp_eq hι₁ g _ inferInstance r (Functor.pullbackFiberHom_fac α g)
    (Functor.pullbackFiberHom_fac (frameSmul hι₁ ζ r α) g) rfl).symm

/-- **Conjugation by isomorphisms of the fibre is linear.** -/
theorem frameSmul_conj (ζ ζ' : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U)
    (φ : ζ ≅ ζ') (r : (bandRing B S hS W).obj (op U)) (α : ζ ⟶ ζ) :
    frameSmul hι₁ ζ' r (φ.inv ≫ α ≫ φ.hom) = φ.inv ≫ frameSmul hι₁ ζ r α ≫ φ.hom := by
  have hτ (γ : ζ ⟶ ζ) : (Functor.Fiber.fiberInclusion.map (φ.inv ≫ γ ≫ φ.hom)).comp
      (Functor.Fiber.fiberInclusion.map φ.inv) =
      (Functor.Fiber.fiberInclusion.map φ.inv).comp (Functor.Fiber.fiberInclusion.map γ) := by
    change Functor.Fiber.fiberInclusion.map ((φ.inv ≫ γ ≫ φ.hom) ≫ φ.inv) =
      Functor.Fiber.fiberInclusion.map (φ.inv ≫ γ)
    simp
  have h0 : (((bandRing B S hS W).map (𝟙 U).op).hom r) = r := by
    rw [op_id, CategoryTheory.Functor.map_id]
    rfl
  have := frameSmul_eq_of_comp_eq hι₁ (𝟙 U) _ φ.inv.2 r (hτ α) (hτ (frameSmul hι₁ ζ r α)) rfl
  rwa [h0] at this

end Compat

end AlgebraicGeometry.Stack.EtaleSmoothLift
