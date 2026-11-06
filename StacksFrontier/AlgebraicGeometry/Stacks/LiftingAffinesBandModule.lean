module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesAutomorphismFrameModule
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModuleAbelianSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleChartGlobalFunctions

/-!
# The band of the gerbe of smooth lifts is an `𝒪_W`-module (Stacks 0CKG (2), the module)

Let `p : 𝒞 ⟶ W_{spaces,étale}` be the category of smooth lifts of étale opens of `W` of
Stacks 0CJP (`AlgebraicGeometry.Stack.EtaleSmoothLift.proj`), along a first order thickening
`𝒳 ⊂ 𝒳'`, and let `𝒢` be a sheaf of groups banding it as in Stacks 0CJY. Every automorphism group
`Aut(ξ)`, `ξ` over `U`, is a `Γ(U, 𝒪_U)`-module
(`AlgebraicGeometry.Stack.EtaleSmoothLift.frameSmul`, through the identification
`Aut(ξ) = Hom(Δ^*Ω_{I/U'}, 𝒞_{U/U'})` of the proof of Stacks 0CKG), conjugation is linear and
pullback is semilinear. When `p` is locally nonempty and locally connected these structures
descend to `𝒢` (`CategoryTheory.Functor.exists_bandSmul`), the gluing step of the source's proof
(Sites, Section 04TP).

This file performs that descent and reads the result on the small étale site `W_étale` of
Stacks 03ED, where `𝒪_W`-modules live: the restriction of `𝒢` along the comparison functor of
Stacks 03G1 is the underlying abelian sheaf of a sheaf of `𝒪_W`-modules
(`AlgebraicGeometry.Stack.EtaleSmoothLift.bandModule`), the scalars `Γ(V, 𝒪_V)` of an étale
chart `V` acting through the identification of `Γ(V, 𝒪_V)` with the functions on the algebraic
space `V` (`AlgebraicGeometry.Space.comparisonStructureSheafIso`).

## Main definitions

* `AlgebraicGeometry.Stack.EtaleSmoothLift.bandSmul`: the descended product on `𝒢`.
* `AlgebraicGeometry.Stack.EtaleSmoothLift.bandModule`: the sheaf of `𝒪_W`-modules on `W_étale`.
* `AlgebraicGeometry.Stack.EtaleSmoothLift.bandModuleIso`: its underlying abelian sheaf is the
  restriction of `𝒢` to `W_étale`.

## References

* [Stacks Project, Tag 0CKG](https://stacks.math.columbia.edu/tag/0CKG)
* [Stacks Project, Tag 0CJY](https://stacks.math.columbia.edu/tag/0CJY)
* [Stacks Project, Tag 04TP](https://stacks.math.columbia.edu/tag/04TP)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
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

attribute [local instance] isFibered_proj

variable (hι₁ : AlgebraicStacks.IsFirstOrderThickening B S hS ι)
  (hne : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).LocallyNonempty
    (Space.SpacesEtale.topology B S hS W))
  (hlc : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).LocallyConnected
    (Space.SpacesEtale.topology B S hS W))
  (𝒢 : Sheaf (Space.SpacesEtale.topology B S hS W) CommGrpCat.{u + 1})
  (θ : ∀ (U : Space.SpacesEtale B S hS W)
    (ξ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U),
    (Over.forget U).op ⋙ 𝒢.obj ⋙ forget CommGrpCat.{u + 1} ≅
      (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).morPresheaf ξ ξ ⋙
        uliftFunctor.{u + 1, u + 1})
  (h₁ : ∀ (U : Space.SpacesEtale B S hS W)
    (ξ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) (g : Over U)
    (a b : 𝒢.obj.obj (op g.left)),
      ((θ U ξ).hom.app (op g) (a * b)).down =
        ((θ U ξ).hom.app (op g) a).down ≫ ((θ U ξ).hom.app (op g) b).down)
  (h₂ : ∀ (U : Space.SpacesEtale B S hS W)
    (ξ ζ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) (φ : ξ ⟶ ζ) (g : Over U)
    (a : 𝒢.obj.obj (op g.left)),
      haveI : ∀ U, IsGroupoid ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) :=
        isFiberedInGroupoids_proj.fiber_isGroupoid
      ((θ U ζ).hom.app (op g) a).down =
        Functor.pullbackFiberHom (CategoryTheory.inv φ) g.hom ≫
          ((θ U ξ).hom.app (op g) a).down ≫ Functor.pullbackFiberHom φ g.hom)
  (h₃ : ∀ (U : Space.SpacesEtale B S hS W)
    (ξ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) (g : Over U)
    (a : 𝒢.obj.obj (op g.left)),
      ((θ U ξ).hom.app (op g) a).down =
        (Functor.pullbackFiberIdIso (Functor.pullbackFiber
          (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _) ξ g.hom)).inv ≫
          ((θ g.left (Functor.pullbackFiber (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _) ξ
            g.hom)).hom.app (op (Over.mk (𝟙 g.left))) a).down ≫
          (Functor.pullbackFiberIdIso (Functor.pullbackFiber
            (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _) ξ g.hom)).hom)

include hι₁ hne hlc h₁ h₂ h₃ in
/-- **The module structures of the automorphism groups descend to the band** (Stacks 0CKG (2),
the gluing step). -/
theorem exists_bandSmul_proj :
    ∃ bsmul : ∀ U : Space.SpacesEtale B S hS W, (bandRing B S hS W).obj (op U) →
        𝒢.obj.obj (op U) → 𝒢.obj.obj (op U),
      (∀ (U V : Space.SpacesEtale B S hS W) (g : V ⟶ U)
          (y : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber V)
          (r : (bandRing B S hS W).obj (op U)) (a : 𝒢.obj.obj (op U)),
        Functor.bandFrame θ V y (𝒢.obj.map g.op (bsmul U r a)) =
          frameSmul hι₁ y ((bandRing B S hS W).map g.op r)
            (Functor.bandFrame θ V y (𝒢.obj.map g.op a))) ∧
      (∀ (U : Space.SpacesEtale B S hS W) (r : (bandRing B S hS W).obj (op U))
          (a b : 𝒢.obj.obj (op U)), bsmul U r (a * b) = bsmul U r a * bsmul U r b) ∧
      (∀ (U : Space.SpacesEtale B S hS W) (r : (bandRing B S hS W).obj (op U)),
        bsmul U r 1 = 1) ∧
      (∀ (U : Space.SpacesEtale B S hS W) (r s : (bandRing B S hS W).obj (op U))
          (a : 𝒢.obj.obj (op U)), bsmul U (r + s) a = bsmul U r a * bsmul U s a) ∧
      (∀ (U : Space.SpacesEtale B S hS W) (a : 𝒢.obj.obj (op U)), bsmul U 0 a = 1) ∧
      (∀ (U : Space.SpacesEtale B S hS W) (a : 𝒢.obj.obj (op U)), bsmul U 1 a = a) ∧
      (∀ (U : Space.SpacesEtale B S hS W) (r s : (bandRing B S hS W).obj (op U))
          (a : 𝒢.obj.obj (op U)), bsmul U (r * s) a = bsmul U r (bsmul U s a)) ∧
      (∀ (U V : Space.SpacesEtale B S hS W) (h : V ⟶ U) (r : (bandRing B S hS W).obj (op U))
          (a : 𝒢.obj.obj (op U)),
        𝒢.obj.map h.op (bsmul U r a) = bsmul V ((bandRing B S hS W).map h.op r)
          (𝒢.obj.map h.op a)) := by
  have : ∀ U, IsGroupoid ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) :=
    isFiberedInGroupoids_proj.fiber_isGroupoid
  have hsh : Presieve.IsSheaf (Space.SpacesEtale.topology B S hS W)
      (𝒢.obj ⋙ forget CommGrpCat.{u + 1}) :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget CommGrpCat.{u + 1})).1 𝒢.2)
  exact Functor.exists_bandSmul (p := proj) (J := Space.SpacesEtale.topology B S hS W) (𝒢 := 𝒢)
    (R := bandRing B S hS W) (Θ := Functor.bandFrame θ)
    (smul := fun U ζ r α => frameSmul hι₁ ζ r α)
    (Functor.bandFrame_mul θ h₁) (Functor.bandFrame_conj θ h₂) (Functor.bandFrame_res θ h₃)
    (fun U ζ r α β => frameSmul_comp hι₁ ζ r α β) (fun U ζ r => frameSmul_id hι₁ ζ r)
    (fun U ζ r s α => frameSmul_add hι₁ ζ r s α) (fun U ζ α => frameSmul_zero hι₁ ζ α)
    (fun U ζ α => frameSmul_one hι₁ ζ α) (fun U ζ r s α => frameSmul_mul hι₁ ζ r s α)
    (fun U ζ ζ' φ r α => frameSmul_conj hι₁ ζ ζ' φ r α)
    (fun U V g ζ r α => pullbackFiberHom_frameSmul hι₁ g ζ r α) hsh hne
    (Functor.nonempty_iso_pullbackFiber_of_locallyConnected isFiberedInGroupoids_proj hlc)

include hι₁ hne hlc h₁ h₂ h₃ in
/-- **The descended product on the band**: `r · a` for a function `r` on `U` and a section `a` of
`𝒢` over `U`, read by every frame as the module structure of its automorphism group
(`AlgebraicGeometry.Stack.EtaleSmoothLift.exists_bandSmul_proj`). -/
def bandSmul (U : Space.SpacesEtale B S hS W) (r : (bandRing B S hS W).obj (op U))
    (a : 𝒢.obj.obj (op U)) : 𝒢.obj.obj (op U) :=
  (exists_bandSmul_proj hι₁ hne hlc 𝒢 θ h₁ h₂ h₃).choose U r a

/-- Every frame `y` over `V` reads the restriction to `V` of `r · a` as the action of the
restriction of `r` on the restriction of `a`. -/
theorem bandFrame_bandSmul (U V : Space.SpacesEtale B S hS W) (g : V ⟶ U)
    (y : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber V)
    (r : (bandRing B S hS W).obj (op U)) (a : 𝒢.obj.obj (op U)) :
    Functor.bandFrame θ V y (𝒢.obj.map g.op (bandSmul hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ U r a)) =
      frameSmul hι₁ y ((bandRing B S hS W).map g.op r)
        (Functor.bandFrame θ V y (𝒢.obj.map g.op a)) :=
  (exists_bandSmul_proj hι₁ hne hlc 𝒢 θ h₁ h₂ h₃).choose_spec.1 U V g y r a

/-- The product `r · -` is multiplicative in the section of the band. -/
theorem bandSmul_mul (U : Space.SpacesEtale B S hS W) (r : (bandRing B S hS W).obj (op U))
    (a b : 𝒢.obj.obj (op U)) :
    bandSmul hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ U r (a * b) =
      bandSmul hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ U r a * bandSmul hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ U r b :=
  (exists_bandSmul_proj hι₁ hne hlc 𝒢 θ h₁ h₂ h₃).choose_spec.2.1 U r a b

/-- The product `r · 1` is `1`. -/
theorem bandSmul_one (U : Space.SpacesEtale B S hS W) (r : (bandRing B S hS W).obj (op U)) :
    bandSmul hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ U r 1 = 1 :=
  (exists_bandSmul_proj hι₁ hne hlc 𝒢 θ h₁ h₂ h₃).choose_spec.2.2.1 U r

/-- The product `(r + s) · a` is `(r · a) * (s · a)`. -/
theorem bandSmul_add (U : Space.SpacesEtale B S hS W) (r s : (bandRing B S hS W).obj (op U))
    (a : 𝒢.obj.obj (op U)) :
    bandSmul hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ U (r + s) a =
      bandSmul hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ U r a * bandSmul hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ U s a :=
  (exists_bandSmul_proj hι₁ hne hlc 𝒢 θ h₁ h₂ h₃).choose_spec.2.2.2.1 U r s a

/-- The product `0 · a` is `1`. -/
theorem bandSmul_zero (U : Space.SpacesEtale B S hS W) (a : 𝒢.obj.obj (op U)) :
    bandSmul hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ U 0 a = 1 :=
  (exists_bandSmul_proj hι₁ hne hlc 𝒢 θ h₁ h₂ h₃).choose_spec.2.2.2.2.1 U a

/-- The product `1 · a` is `a`. -/
theorem bandSmul_one_left (U : Space.SpacesEtale B S hS W) (a : 𝒢.obj.obj (op U)) :
    bandSmul hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ U 1 a = a :=
  (exists_bandSmul_proj hι₁ hne hlc 𝒢 θ h₁ h₂ h₃).choose_spec.2.2.2.2.2.1 U a

/-- The product `(r * s) · a` is `r · (s · a)`. -/
theorem bandSmul_mul_left (U : Space.SpacesEtale B S hS W) (r s : (bandRing B S hS W).obj (op U))
    (a : 𝒢.obj.obj (op U)) :
    bandSmul hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ U (r * s) a =
      bandSmul hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ U r (bandSmul hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ U s a) :=
  (exists_bandSmul_proj hι₁ hne hlc 𝒢 θ h₁ h₂ h₃).choose_spec.2.2.2.2.2.2.1 U r s a

/-- Restriction along `h : V ⟶ U` carries `r · a` to the product of the restrictions of `r` and
`a`. -/
theorem map_bandSmul (U V : Space.SpacesEtale B S hS W) (h : V ⟶ U)
    (r : (bandRing B S hS W).obj (op U)) (a : 𝒢.obj.obj (op U)) :
    𝒢.obj.map h.op (bandSmul hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ U r a) =
      bandSmul hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ V ((bandRing B S hS W).map h.op r) (𝒢.obj.map h.op a) :=
  (exists_bandSmul_proj hι₁ hne hlc 𝒢 θ h₁ h₂ h₃).choose_spec.2.2.2.2.2.2.2 U V h r a

section Chart

variable (B S hS W) in
/-- **A function on an étale chart `V` of `W` as a function on the algebraic space `V`**, the
inverse of the identification `AlgebraicGeometry.Space.comparisonStructureSheafIso`. -/
def chartScalar (V : Space.SmallEtale B S hS W.1) :
    (Space.structureRingSheaf B S hS W).obj.obj (op V) →+*
      (bandRing B S hS W).obj (op ((Space.comparisonFunctor B S hS W).obj V)) :=
  ((Space.comparisonStructureSheafIso B S hS W).inv.app (op V)).hom.comp
    ULift.ringEquiv.symm.toRingHom

/-- `AlgebraicGeometry.Stack.EtaleSmoothLift.chartScalar` commutes with restriction along a
morphism `f : V₂ ⟶ V₁` of étale charts. -/
theorem bandRing_map_chartScalar {V₁ V₂ : Space.SmallEtale B S hS W.1} (f : V₂ ⟶ V₁)
    (r : (Space.structureRingSheaf B S hS W).obj.obj (op V₁)) :
    ((bandRing B S hS W).map ((Space.comparisonFunctor B S hS W).map f).op).hom
        (chartScalar B S hS W V₁ r) =
      chartScalar B S hS W V₂ (((Space.structureRingSheaf B S hS W).obj.map f.op).hom r) := by
  have h := (Space.comparisonStructureSheafIso B S hS W).inv.naturality f.op
  have h' := congrArg (fun φ => φ.hom (ULift.up.{u + 1} r)) h
  exact h'.symm

/-- **The `Γ(V, 𝒪_V)`-module structure on the sections of the band over an étale chart `V`.** -/
@[instance_reducible]
def bandModuleStructure (V : Space.SmallEtale B S hS W.1) :
    Module ((Space.structureRingSheaf B S hS W).obj.obj (op V))
      (Additive (𝒢.obj.obj (op ((Space.comparisonFunctor B S hS W).obj V)))) where
  smul r a := Additive.ofMul (bandSmul hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ _ (chartScalar B S hS W V r)
    a.toMul)
  one_smul a := by
    change Additive.ofMul (bandSmul hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ _ _ a.toMul) = a
    rw [map_one, bandSmul_one_left]
    rfl
  mul_smul r s a := by
    change Additive.ofMul (bandSmul hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ _ _ a.toMul) =
      Additive.ofMul (bandSmul hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ _ _ (bandSmul hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ _ _
        a.toMul))
    rw [map_mul, bandSmul_mul_left]
  smul_zero r := by
    change Additive.ofMul (bandSmul hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ _ _ 1) = Additive.ofMul 1
    rw [bandSmul_one]
  smul_add r a b := by
    change Additive.ofMul (bandSmul hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ _ _ (a.toMul * b.toMul)) =
      Additive.ofMul (bandSmul hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ _ _ a.toMul *
        bandSmul hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ _ _ b.toMul)
    rw [bandSmul_mul]
  add_smul r s a := by
    change Additive.ofMul (bandSmul hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ _ _ a.toMul) =
      Additive.ofMul (bandSmul hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ _ _ a.toMul *
        bandSmul hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ _ _ a.toMul)
    rw [map_add, bandSmul_add]
  zero_smul a := by
    change Additive.ofMul (bandSmul hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ _ _ a.toMul) = Additive.ofMul 1
    rw [map_zero, bandSmul_zero]

/-- The restriction of `𝒢` to the small étale site `W_étale`, as a sheaf of abelian groups. -/
abbrev bandAbelian : Sheaf (Space.SmallEtale.topology B S hS W.1) AddCommGrpCat.{u + 1} :=
  (Space.spacesEtaleAbelianRestriction B S hS W).obj
    ((sheafCompose _ commGroupAddCommGroupEquivalence.{u + 1}.functor).obj 𝒢)

/-- **The band as a sheaf of `𝒪_W`-modules on `W_étale`** (Stacks 0CKG (2), the module). -/
def bandModule : SheafOfModules.{u + 1} (Space.structureRingSheaf B S hS W) where
  val := @PresheafOfModules.ofPresheaf _ _ _ (bandAbelian 𝒢).obj
    (fun V => bandModuleStructure hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ V.unop) (fun V₁ V₂ f r a => by
      change Additive.ofMul (𝒢.obj.map ((Space.comparisonFunctor B S hS W).map f.unop).op
          (bandSmul hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ _ (chartScalar B S hS W V₁.unop r) a.toMul)) =
        Additive.ofMul (bandSmul hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ _
          (chartScalar B S hS W V₂.unop (((Space.structureRingSheaf B S hS W).obj.map f).hom r))
          (𝒢.obj.map ((Space.comparisonFunctor B S hS W).map f.unop).op a.toMul))
      exact congrArg Additive.ofMul ((map_bandSmul hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ _ _
        ((Space.comparisonFunctor B S hS W).map f.unop) _ _).trans
          (congrArg (fun t => bandSmul hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ _ t _)
            (bandRing_map_chartScalar f.unop r))))
  isSheaf := (bandAbelian 𝒢).property

/-- **The underlying abelian sheaf of the band module is the restriction of `𝒢` to `W_étale`.** -/
def bandModuleIso :
    bandAbelian 𝒢 ≅ (SheafOfModules.toSheaf _).obj (bandModule hι₁ hne hlc 𝒢 θ h₁ h₂ h₃) :=
  Iso.refl _

/-- The scalars of the band module over an étale chart `V` act through the descended product. -/
theorem bandModule_smul (V : Space.SmallEtale B S hS W.1)
    (r : (Space.structureRingSheaf B S hS W).obj.obj (op V))
    (a : (bandModule hι₁ hne hlc 𝒢 θ h₁ h₂ h₃).val.obj (op V)) :
    r • a = (Additive.ofMul (bandSmul hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ _ (chartScalar B S hS W V r)
      (Additive.toMul (α := 𝒢.obj.obj (op ((Space.comparisonFunctor B S hS W).obj V))) a)) :
        (bandModule hι₁ hne hlc 𝒢 θ h₁ h₂ h₃).val.obj (op V)) :=
  rfl

end Chart

end AlgebraicGeometry.Stack.EtaleSmoothLift
