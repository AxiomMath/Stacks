module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineFlatMorphismTerminalArrow
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.TensorPushforwardStackCounterexample
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductBaseMorphism
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProductFstCompTerminal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 0GRN, corrected: one leg affine

Let `a : 𝒴 ⟶ 𝒳` and `b : 𝒵 ⟶ 𝒳` be 1-morphisms of algebraic stacks over `S`, let
`𝒫 = 𝒴 ×_𝒳 𝒵` be the canonical 2-fibre product
(`AlgebraicGeometry.Stack.twoFibreProductSquareAlgebraicStacks`) and `f = pr₁ ≫ a : 𝒫 ⟶ 𝒳`.
**Stacks 0GRN** asserts `a_{QCoh,*}𝒪_𝒴 ⊗_{𝒪_𝒳} b_{QCoh,*}𝒪_𝒵 = f_{QCoh,*}𝒪_𝒫` when `a` and `b`
are representable, quasi-compact, quasi-separated and flat. As printed this is false
(`AlgebraicGeometry.Stack.AlgebraicStacks.not_forall_nonempty_tensorPushforwardUnits_iso`: two
disjoint punctured planes). This file proves the corrected statement in which **`a` is affine**:
for `a` affine (Stacks 0CHQ), quasi-compact, quasi-separated and flat and `b` representable,
quasi-compact and quasi-separated, the canonical map

`μ : a_{QCoh,*}𝒪_𝒴 ⊗ b_{QCoh,*}𝒪_𝒵 ⟶ f_{QCoh,*}𝒪_𝒫`, `s ⊗ t ↦ pr₁^*s · pr₂^*t`,

is an isomorphism. Here `QCoh(𝒪_𝒳)` is
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModules`
with the monoidal structure `fppfModulesMonoidal` of Stacks 0GQM (the tensor product sheaf),
`𝟙_` is the structure sheaf, and `g_{QCoh,*}` is
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentDirectImage` (Stacks 077A,
`Q ∘ g_* ∘ i`). Flatness of `b` is not needed.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.tensorPushforwardMap`: the canonical map `μ`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isIso_tensorPushforwardMap`: **Stacks 0GRN, corrected
  (one leg affine)**.
* `AlgebraicGeometry.Stack.AlgebraicStacks.nonempty_iso_tensorPushforward`: the asserted
  isomorphism.

## The proof

A map of quasi-coherent modules is an isomorphism as soon as it is bijective on sections over
flat objects lying over affine schemes (`isIso_of_flatObject_of_isAffine`). Over such an `x`,
over `U`, the coherator does not change the sections of the three direct images (Stacks 0GQQ),
and the sections of the tensor product are the tensor product of the sections. Let `(y₀, α)` be
the terminal arrow of `a` at `x`, lying over an affine `V` flat over `U`
(`exists_isTerminal_of_isAffineHom_of_isFlat`), and `(z₁, β)` the terminal
arrow of `b` at `a y₀`; they combine to the terminal arrow of `f` at `x`
(`CategoryTheory.TwoFibreProductOver.exists_isTerminal_fst_comp`), and on sections `μ` becomes
the base change `Γ(V) ⊗_{Γ(U)} (b_*𝒪)(x) ⟶ (b_*𝒪)(a y₀) = Γ(z₁, 𝒪)` along the flat morphism
`α`, which is bijective because `Q(b_*𝒪)` is quasi-coherent and agrees with `b_*𝒪` on the flat
objects `x` and `a y₀` (`bijective_tensorPushforwardMapApp`).

## Implementation notes

The map `AlgebraicGeometry.Stack.quasicoherentTensorPushforwardMap` lives on
`FibredSite.quasicoherentModules` and `LQCoh^fbc` at module universe `u + 1`, with the three
direct images `aStar`, `bStar`, `fStar`, the tensor product `TLQ` and the cup product `cup` taken
as unconstrained data; nothing ties that data to `quasicoherentDirectImage` or to the monoidal
structure of `quasicoherentModules`, so its invertibility cannot be stated about the objects of
the tag. The map here is built directly from the right Kan extension description of the direct
images.

## References

* [Stacks Project, Tag 0GRN](https://stacks.math.columbia.edu/tag/0GRN)
* [Stacks Project, Tag 0GQQ](https://stacks.math.columbia.edu/tag/0GQQ)
* [Stacks Project, Tag 0GQM](https://stacks.math.columbia.edu/tag/0GQM)
* [Stacks Project, Tag 077A](https://stacks.math.columbia.edu/tag/077A)
* [Stacks Project, Tag 0CHQ](https://stacks.math.columbia.edu/tag/0CHQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u w

namespace CategoryTheory.TwoFibreProductOver

variable {𝒞 : Type*} [Category 𝒞] {𝒴 : Type*} [Category 𝒴] {𝒵 : Type*} [Category 𝒵]
  {𝒳 : Type*} [Category 𝒳] {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒵 : 𝒵 ⥤ 𝒞} {p𝒳 : 𝒳 ⥤ 𝒞} {F : 𝒴 ⥤ 𝒳} {G : 𝒵 ⥤ 𝒳}

/-- The base of a morphism `f : P ⟶ Q` of the 2-fibre product, followed by the identification
`Q.base = p𝒴 Q.x`, is the image of `f.a` under `p𝒴`. -/
lemma Hom.hbase_comp_eqToHom_fst {P Q : TwoFibreProductOver p𝒴 p𝒵 p𝒳 F G} (f : P ⟶ Q) :
    f.hbase ≫ eqToHom Q.hx.symm = eqToHom P.hx.symm ≫ p𝒴.map f.a := by
  rw [Hom.hbase_eq]
  simp

/-- The base of a morphism `f : P ⟶ Q` of the 2-fibre product, followed by the identification
`Q.base = p𝒵 Q.y`, is the image of `f.b` under `p𝒵`. -/
lemma Hom.hbase_comp_eqToHom_snd {P Q : TwoFibreProductOver p𝒴 p𝒵 p𝒳 F G} (f : P ⟶ Q) :
    f.hbase ≫ eqToHom Q.hy.symm = eqToHom P.hy.symm ≫ p𝒵.map f.b := by
  rw [Hom.hbase_eq_snd]
  simp

/-- A morphism `f : P ⟶ Q` of the 2-fibre product commutes with the inverses of the comparison
isomorphisms: `P.iso.inv ≫ F.map f.a = G.map f.b ≫ Q.iso.inv`. -/
lemma Hom.iso_inv_comp_map {P Q : TwoFibreProductOver p𝒴 p𝒵 p𝒳 F G} (f : P ⟶ Q) :
    P.iso.inv ≫ F.map f.a = G.map f.b ≫ Q.iso.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← f.w, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- `G.map f.b ≫ Q.iso.inv ≫ h = P.iso.inv ≫ F.map f.a ≫ h` for a morphism `f : P ⟶ Q` of the
2-fibre product and any `h : F.obj Q.x ⟶ x`. -/
lemma Hom.map_b_comp_iso_inv_comp {P Q : TwoFibreProductOver p𝒴 p𝒵 p𝒳 F G} (f : P ⟶ Q) {x : 𝒳}
    (h : F.obj Q.x ⟶ x) : G.map f.b ≫ Q.iso.inv ≫ h = P.iso.inv ≫ F.map f.a ≫ h := by
  rw [← Category.assoc, ← Hom.iso_inv_comp_map, Category.assoc]

/-- The base of the comparison isomorphism of an object of the 2-fibre product, read through a
factorization `P.iso ≫ β = F k`. -/
lemma eqToHom_comp_map_eq_of_iso_comp {P : TwoFibreProductOver p𝒴 p𝒵 p𝒳 F G}
    (hF : F ⋙ p𝒳 = p𝒴) (hG : G ⋙ p𝒳 = p𝒵) {y₀ : 𝒴} (k : P.x ⟶ y₀)
    (β : G.obj P.y ⟶ F.obj y₀) (hk : P.iso.hom ≫ β = F.map k) :
    eqToHom P.hy.symm ≫ eqToHom (Functor.congr_obj hG P.y).symm ≫ p𝒳.map β ≫
      eqToHom (Functor.congr_obj hF y₀) = eqToHom P.hx.symm ≫ p𝒴.map k := by
  subst hF hG
  have hv := P.vertical
  have h1 : p𝒳.map (F.map k) = p𝒳.map P.iso.hom ≫ p𝒳.map β := by
    rw [← hk, Functor.map_comp]
  change _ = eqToHom P.hx.symm ≫ p𝒳.map (F.map k)
  rw [h1, IsHomLift.fac' p𝒳 (𝟙 P.base) P.iso.hom]
  simp

end CategoryTheory.TwoFibreProductOver

/-- **A map out of a tensor product which is the base change of a bijection along two linear
equivalences is bijective.** -/
lemma Function.Bijective.of_tmul_eq {R : Type*} [CommRing R] {M N M' N' T : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup M'] [Module R M']
    [AddCommGroup N'] [Module R N'] [AddCommGroup T] (τ : M ≃ₗ[R] M') (σ : N ≃ₗ[R] N')
    (Θ : TensorProduct R M N →+ T) (Φ : TensorProduct R M' N' →+ T) (hΦ : Function.Bijective Φ)
    (h : ∀ m n, Θ (m ⊗ₜ n) = Φ (τ m ⊗ₜ σ n)) : Function.Bijective Θ := by
  have : Θ = Φ.comp (TensorProduct.congr τ σ).toLinearMap.toAddMonoidHom := by
    ext z
    induction z using TensorProduct.inductionOn with
    | tmul m n => simp [h]
    | add z z' hz hz' => rw [map_add, map_add, hz, hz']
  rw [this]
  exact hΦ.comp (TensorProduct.congr τ σ).bijective

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (a : 𝒴 ⟶ 𝒳) (b : 𝒵 ⟶ 𝒳)

/-! ### Rings of functions and the maps between them -/

/-- The ring map `Γ(V, 𝒪) ⟶ Γ(U, 𝒪)` of a morphism `U ⟶ V` of the big fppf site. -/
abbrev baseRingHom {U V : BigFppfOver B S hS} (g : U ⟶ V) :
    Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) →+* Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) :=
  ((BigFppfOver.toScheme B S hS).map g).appTop.hom

/-- `baseRingHom` is contravariantly functorial:
`baseRingHom (g ≫ h) = baseRingHom g ∘ baseRingHom h`. -/
lemma baseRingHom_comp {U V W : BigFppfOver B S hS} (g : U ⟶ V) (h : V ⟶ W)
    (r : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)) :
    baseRingHom (g ≫ h) r = baseRingHom g (baseRingHom h r) := by
  rw [baseRingHom, Functor.map_comp, Scheme.Hom.comp_appTop]
  rfl

/-- The ring maps of two composable identifications `U = V`, `V = W` compose to the ring map of
`U = W`. -/
lemma baseRingHom_eqToHom_eqToHom {U V W : BigFppfOver B S hS} (h₁ : U = V) (h₂ : V = W)
    (r : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)) :
    baseRingHom (eqToHom h₁) (baseRingHom (eqToHom h₂) r) =
      baseRingHom (eqToHom (h₁.trans h₂)) r := by
  rw [← baseRingHom_comp, eqToHom_trans]

/-- Two factorizations `g₁ ≫ h₁ = g₂ ≫ h₂` of a morphism give the same restriction of functions. -/
lemma baseRingHom_comp_eq {U V V' W : BigFppfOver B S hS} (g₁ : U ⟶ V) (h₁ : V ⟶ W)
    (g₂ : U ⟶ V') (h₂ : V' ⟶ W) (h : g₁ ≫ h₁ = g₂ ≫ h₂)
    (r : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)) :
    baseRingHom g₁ (baseRingHom h₁ r) = baseRingHom g₂ (baseRingHom h₂ r) := by
  rw [← baseRingHom_comp, ← baseRingHom_comp, h]

section ScalarPi

variable {𝒜 : Type*} [Category 𝒜] {𝒬 : Type*} [Category 𝒬] (p : 𝒜 ⥤ BigFppfOver B S hS)
  (q : 𝒬 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (F : 𝒜 ⥤ 𝒬) (hF : F ⋙ q = p) (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
  [F.IsCocontinuous (associatedTopology B S hS p τ) (associatedTopology B S hS q τ)]
  [∀ G : 𝒜ᵒᵖ ⥤ RingCat.{u}, F.op.HasPointwiseRightKanExtension G]

/-- The ring map that the structure map of a direct image cuts out at a leg `(U, ψ)` is
restriction of functions along the morphism of schemes underneath `ψ`. -/
lemma scalarπ_moduleDirectImageStructureMap_apply {y : 𝒬} (j : StructuredArrow (op y) F.op)
    (r : Γ((BigFppfOver.toScheme B S hS).obj (q.obj y), ⊤)) :
    (Stacks.SheafOfModules.scalarπ F
      (moduleDirectImageStructureMap B S hS p q hp hq F hF τ hτ).hom (op y) j).hom r =
      baseRingHom (eqToHom (Functor.congr_obj hF j.right.unop).symm)
        (baseRingHom (q.map j.hom.unop) r) := by
  rw [scalarπ_moduleDirectImageStructureMap]
  subst hF
  simp only [eqToHom_refl]
  rfl

end ScalarPi

section TerminalComparison

variable {𝒴₀ : Type*} [Category 𝒴₀] {𝒵₀ : Type*} [Category 𝒵₀] {𝒳₀ : Type*} [Category 𝒳₀]
  {p𝒴 : 𝒴₀ ⥤ BigFppfOver B S hS} {p𝒵 : 𝒵₀ ⥤ BigFppfOver B S hS} {p𝒳 : 𝒳₀ ⥤ BigFppfOver B S hS}
  {F : 𝒴₀ ⥤ 𝒳₀} {G : 𝒵₀ ⥤ 𝒳₀}

/-- Pulling a function on `y₀` back to the 2-fibre product through `k : P.x ⟶ y₀` is pulling it
back through `β`. -/
lemma baseRingHom_fst_eq_snd (hF : F ⋙ p𝒳 = p𝒴) (hG : G ⋙ p𝒳 = p𝒵)
    (P : TwoFibreProductOver p𝒴 p𝒵 p𝒳 F G) {y₀ : 𝒴₀} {z₁ : 𝒵₀} (k : P.x ⟶ y₀)
    (β : G.obj z₁ ⟶ F.obj y₀) (hPy : P.y = z₁) (hk : P.iso.hom ≫ G.map (eqToHom hPy) ≫ β = F.map k)
    (z : Γ((BigFppfOver.toScheme B S hS).obj (p𝒴.obj y₀), ⊤)) :
    baseRingHom (eqToHom P.hx.symm) (baseRingHom (p𝒴.map k) z) =
      baseRingHom (eqToHom P.hy.symm) (baseRingHom (p𝒵.map (eqToHom hPy))
        (baseRingHom (eqToHom (Functor.congr_obj hG z₁).symm) (baseRingHom (p𝒳.map β)
          (baseRingHom (eqToHom (Functor.congr_obj hF y₀)) z)))) := by
  subst hPy
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp] at hk
  have h := TwoFibreProductOver.eqToHom_comp_map_eq_of_iso_comp hF hG k β hk
  simp only [← baseRingHom_comp, eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← h]

/-- `(α.op ≫ β.op) ≫ G.op.map (eqToHom hPy).op = (F.map k ≫ α).op ≫ P.iso.inv.op` when
`P.iso.hom ≫ G.map (eqToHom hPy) ≫ β = F.map k`. -/
lemma op_comp_map_eqToHom_op_eq {P : TwoFibreProductOver p𝒴 p𝒵 p𝒳 F G} {y₀ : 𝒴₀} {z₁ : 𝒵₀}
    {x : 𝒳₀} (k : P.x ⟶ y₀) (β : G.obj z₁ ⟶ F.obj y₀) (hPy : P.y = z₁)
    (hk : P.iso.hom ≫ G.map (eqToHom hPy) ≫ β = F.map k) (α : F.obj y₀ ⟶ x) :
    (α.op ≫ β.op) ≫ G.op.map (eqToHom hPy).op = (F.map k ≫ α).op ≫ P.iso.inv.op := by
  subst hPy
  apply Quiver.Hom.unop_inj
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp] at hk
  simp [← hk]

end TerminalComparison

section Legs

variable {𝒲 𝒱 : AlgebraicStacks.{u, w} B S hS}

/-- The direct image of modules along a 1-morphism of algebraic stacks, as the canonical direct
image along its underlying cocontinuous functor (isomorphic to
`AlgebraicGeometry.Stack.fppfModulesPushforward`). -/
abbrev canonicalDirectImage (g : 𝒲 ⟶ 𝒱) :
    Stack.fppfModules B S hS 𝒲 ⥤ Stack.fppfModules B S hS 𝒱 :=
  moduleDirectImage.{u, u + 1, u, u + 1, u, u} B S hS 𝒲.val.val.p 𝒱.val.val.p
    𝒲.val.isFiberedInGroupoids 𝒱.val.isFiberedInGroupoids (CatFiberedInGroupoids.homFunctor g.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p g.hom) B.topology le_rfl

/-- The structure sheaf `𝒪_𝒲` as a module over itself. -/
abbrev unitModule (𝒲 : AlgebraicStacks.{u, w} B S hS) : Stack.fppfModules B S hS 𝒲 :=
  SheafOfModules.unit _

/-- `g_*𝒪_𝒲`, through the canonical direct image. -/
abbrev pushUnit (g : 𝒲 ⟶ 𝒱) : Stack.fppfModules B S hS 𝒱 :=
  (canonicalDirectImage g).obj (unitModule 𝒲)

/-- The leg at `(w, ψ : g w ⟶ x)` of the limit computing the sections of `g_*𝒪_𝒲` over `x`. -/
abbrev unitLeg (g : 𝒲 ⟶ 𝒱) {x : 𝒱.val.val.obj}
    (j : StructuredArrow (op x) (CatFiberedInGroupoids.homFunctor g.hom).op) :
    (pushUnit g).val.obj (op x) →+ FibredSite.objRing B S hS 𝒲.val.val.p j.right.unop :=
  (Stacks.SheafOfModules.ranπ (CatFiberedInGroupoids.homFunctor g.hom).op
    (unitModule 𝒲).val.presheaf (op x) j).hom

/-- The structure ring map at a leg. -/
abbrev legRingHom (g : 𝒲 ⟶ 𝒱) {x : 𝒱.val.val.obj}
    (j : StructuredArrow (op x) (CatFiberedInGroupoids.homFunctor g.hom).op) :
    FibredSite.objRing B S hS 𝒱.val.val.p x →+*
      FibredSite.objRing B S hS 𝒲.val.val.p j.right.unop :=
  (Stacks.SheafOfModules.scalarπ (CatFiberedInGroupoids.homFunctor g.hom)
    (moduleDirectImageStructureMap B S hS 𝒲.val.val.p 𝒱.val.val.p 𝒲.val.isFiberedInGroupoids
      𝒱.val.isFiberedInGroupoids (CatFiberedInGroupoids.homFunctor g.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p g.hom) B.topology le_rfl).hom (op x) j).hom

/-- The structure ring map at a leg `(w, ψ)` is restriction of functions along the morphism of
schemes underneath `ψ`. -/
lemma legRingHom_apply (g : 𝒲 ⟶ 𝒱) {x : 𝒱.val.val.obj}
    (j : StructuredArrow (op x) (CatFiberedInGroupoids.homFunctor g.hom).op)
    (r : FibredSite.objRing B S hS 𝒱.val.val.p x) :
    legRingHom g j r = baseRingHom (eqToHom (Functor.congr_obj
      (CatFiberedInGroupoids.homFunctor_comp_p g.hom) j.right.unop).symm)
        (baseRingHom (𝒱.val.val.p.map j.hom.unop) r) :=
  scalarπ_moduleDirectImageStructureMap_apply _ _ _ _ _ _ _ _ j r

/-- The legs are semilinear along `legRingHom`. -/
lemma unitLeg_smul (g : 𝒲 ⟶ 𝒱) {x : 𝒱.val.val.obj}
    (j : StructuredArrow (op x) (CatFiberedInGroupoids.homFunctor g.hom).op)
    (r : (FibredSite.ringStructureSheafCore B S hS 𝒱.val.val.p 𝒱.val.isFiberedInGroupoids
      .fppf).obj.obj (op x)) (m : (pushUnit g).val.obj (op x)) :
    unitLeg g j (r • m) = legRingHom g j r * unitLeg g j m :=
  ConcreteCategory.congr_hom (Stacks.SheafOfModules.ranSMul_π
    (CatFiberedInGroupoids.homFunctor g.hom)
    (moduleDirectImageStructureMap B S hS 𝒲.val.val.p 𝒱.val.val.p 𝒲.val.isFiberedInGroupoids
      𝒱.val.isFiberedInGroupoids (CatFiberedInGroupoids.homFunctor g.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p g.hom) B.topology le_rfl).hom
    (unitModule 𝒲).val (op x) r j) m

/-- The legs form a cone. -/
lemma unitLeg_naturality (g : 𝒲 ⟶ 𝒱) {x : 𝒱.val.val.obj}
    {j₁ j₂ : StructuredArrow (op x) (CatFiberedInGroupoids.homFunctor g.hom).op} (φ : j₁ ⟶ j₂)
    (m : (pushUnit g).val.obj (op x)) :
    baseRingHom (𝒲.val.val.p.map φ.right.unop) (unitLeg g j₁ m) = unitLeg g j₂ m :=
  ConcreteCategory.congr_hom (Stacks.SheafOfModules.ranπ_naturality
    (CatFiberedInGroupoids.homFunctor g.hom).op (unitModule 𝒲).val.presheaf φ) m

/-- Restriction followed by a leg is a leg. -/
lemma unitLeg_map (g : 𝒲 ⟶ 𝒱) {x x' : 𝒱.val.val.obj} (k : op x ⟶ op x')
    (j : StructuredArrow (op x') (CatFiberedInGroupoids.homFunctor g.hom).op)
    (m : (pushUnit g).val.obj (op x)) :
    unitLeg g j ((pushUnit g).val.map k m) = unitLeg g ((StructuredArrow.map k).obj j) m :=
  ConcreteCategory.congr_hom (Stacks.SheafOfModules.ranπ_map
    (CatFiberedInGroupoids.homFunctor g.hom).op (unitModule 𝒲).val.presheaf k j) m

end Legs

/-- If `f₁ a₁ = f₂ a₂`, then `f₁ (a₁ * x₁) * f₂ x₂ = f₁ x₁ * f₂ (a₂ * x₂)`. -/
lemma mul_map_mul_eq_map_mul_mul {R₁ R₂ T : Type*} [CommRing R₁] [CommRing R₂]
    [CommRing T] (f₁ : R₁ →+* T) (f₂ : R₂ →+* T) (a₁ x₁ : R₁) (a₂ x₂ : R₂)
    (h : f₁ a₁ = f₂ a₂) : f₁ (a₁ * x₁) * f₂ x₂ = f₁ x₁ * f₂ (a₂ * x₂) := by
  rw [map_mul, map_mul, h]
  ring

section Construction

/-- The apex `𝒴 ×_𝒳 𝒵` of the canonical 2-fibre product square of `(a, b)`. -/
abbrev tensorApex : AlgebraicStacks.{u, w} B S hS :=
  (twoFibreProductSquareAlgebraicStacks B S hS a b).pt

/-- The projection `f = pr₁ ≫ a : 𝒴 ×_𝒳 𝒵 ⟶ 𝒳`. -/
abbrev tensorProj : tensorApex a b ⟶ 𝒳 :=
  (twoFibreProductSquareAlgebraicStacks B S hS a b).fst ≫ a

variable {a b} {x : 𝒳.val.val.obj}

/-- The leg of `a_*𝒪_𝒴` underneath a leg `(c, h : a c.x ⟶ x)` of `f_*𝒪`. -/
abbrev legFst
    (j : StructuredArrow (op x) (CatFiberedInGroupoids.homFunctor (tensorProj a b).hom).op) :
    StructuredArrow (op x) (CatFiberedInGroupoids.homFunctor a.hom).op :=
  StructuredArrow.mk (Y := op j.right.unop.x) j.hom

/-- The leg of `b_*𝒪_𝒵` underneath a leg `(c, h : a c.x ⟶ x)` of `f_*𝒪`: `b c.y ≅ a c.x ⟶ x`. -/
abbrev legSnd
    (j : StructuredArrow (op x) (CatFiberedInGroupoids.homFunctor (tensorProj a b).hom).op) :
    StructuredArrow (op x) (CatFiberedInGroupoids.homFunctor b.hom).op :=
  StructuredArrow.mk (Y := op j.right.unop.y) (j.hom ≫ j.right.unop.iso.inv.op)

/-- `Γ(c.x, 𝒪_𝒴) = Γ(c, 𝒪_𝒫)`: both are the functions on the scheme `c` lies over. -/
abbrev fstRingHom (c : (tensorApex a b).val.val.obj) :
    FibredSite.objRing B S hS 𝒴.val.val.p c.x →+*
      FibredSite.objRing B S hS (tensorApex a b).val.val.p c :=
  baseRingHom (eqToHom c.hx.symm)

/-- `Γ(c.y, 𝒪_𝒵) = Γ(c, 𝒪_𝒫)`. -/
abbrev sndRingHom (c : (tensorApex a b).val.val.obj) :
    FibredSite.objRing B S hS 𝒵.val.val.p c.y →+*
      FibredSite.objRing B S hS (tensorApex a b).val.val.p c :=
  baseRingHom (eqToHom c.hy.symm)

/-- Restricting a function on `x` to a leg `(c, h)` of `f_*𝒪_𝒫` through `c.x` is restricting it
directly. -/
lemma fstRingHom_legRingHom
    (j : StructuredArrow (op x) (CatFiberedInGroupoids.homFunctor (tensorProj a b).hom).op)
    (r : FibredSite.objRing B S hS 𝒳.val.val.p x) :
    fstRingHom j.right.unop (legRingHom a (legFst j) r) = legRingHom (tensorProj a b) j r := by
  rw [legRingHom_apply, legRingHom_apply]
  exact baseRingHom_eqToHom_eqToHom _ _ _

/-- Restricting a function on `x` to a leg `(c, h)` of `f_*𝒪_𝒫` through `c.y` is restricting it
directly. -/
lemma sndRingHom_legRingHom
    (j : StructuredArrow (op x) (CatFiberedInGroupoids.homFunctor (tensorProj a b).hom).op)
    (r : FibredSite.objRing B S hS 𝒳.val.val.p x) :
    sndRingHom j.right.unop (legRingHom b (legSnd j) r) = legRingHom (tensorProj a b) j r := by
  have hv := j.right.unop.vertical
  have : 𝒳.val.val.p.IsHomLift (𝟙 j.right.unop.base) j.right.unop.iso.inv := inferInstance
  have h : 𝒳.val.val.p.map (legSnd j).hom.unop =
      eqToHom ((Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p b.hom)
        j.right.unop.y).trans (j.right.unop.hy.trans (j.right.unop.hx.symm.trans
          (Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p a.hom)
            j.right.unop.x).symm))) ≫ 𝒳.val.val.p.map j.hom.unop := by
    rw [show (legSnd j).hom.unop = j.right.unop.iso.inv ≫ j.hom.unop from rfl]
    refine (Functor.map_comp 𝒳.val.val.p j.right.unop.iso.inv j.hom.unop).trans ?_
    rw [IsHomLift.fac' 𝒳.val.val.p (𝟙 j.right.unop.base) j.right.unop.iso.inv]
    simp
  have h2 : ∀ r', baseRingHom (𝒳.val.val.p.map (legSnd j).hom.unop) r' =
      baseRingHom (eqToHom ((Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p b.hom)
        j.right.unop.y).trans (j.right.unop.hy.trans (j.right.unop.hx.symm.trans
          (Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p a.hom)
            j.right.unop.x).symm))))
        (baseRingHom (𝒳.val.val.p.map j.hom.unop) r') := fun r' =>
    (congrArg (fun m => baseRingHom m r') h).trans (baseRingHom_comp _ _ r')
  refine ((congrArg (sndRingHom j.right.unop) (legRingHom_apply b (legSnd j) r)).trans ?_).trans
    (legRingHom_apply _ j r).symm
  refine (congrArg (fun t => sndRingHom j.right.unop (baseRingHom (eqToHom _) t)) (h2 r)).trans ?_
  exact (baseRingHom_eqToHom_eqToHom _ _ _).trans (baseRingHom_eqToHom_eqToHom _ _ _)

/-- The bilinear map `(s, t) ↦ pr₁^*s · pr₂^*t` on the sections over `x` of `a_*𝒪_𝒴` and
`b_*𝒪_𝒵`, at the leg `(c, h)` of `f_*𝒪_𝒫`. -/
def tensorLegBilin
    (j : StructuredArrow (op x) (CatFiberedInGroupoids.homFunctor (tensorProj a b).hom).op) :
    (pushUnit a).val.obj (op x) →+ (pushUnit b).val.obj (op x) →+
      FibredSite.objRing B S hS (tensorApex a b).val.val.p j.right.unop :=
  (AddMonoidHom.mul.comp ((fstRingHom j.right.unop).toAddMonoidHom.comp
    (unitLeg a (legFst j)))).compl₂
      ((sndRingHom j.right.unop).toAddMonoidHom.comp (unitLeg b (legSnd j)))

/-- `tensorLegBilin j s t = pr₁^*s · pr₂^*t`. -/
lemma tensorLegBilin_apply
    (j : StructuredArrow (op x) (CatFiberedInGroupoids.homFunctor (tensorProj a b).hom).op)
    (s : (pushUnit a).val.obj (op x)) (t : (pushUnit b).val.obj (op x)) :
    tensorLegBilin j s t =
      fstRingHom j.right.unop (unitLeg a (legFst j) s) *
        sndRingHom j.right.unop (unitLeg b (legSnd j) t) :=
  rfl

variable (a b x) in
/-- The objectwise tensor product of the sections of `a_*𝒪_𝒴` and `b_*𝒪_𝒵` over `x`. -/
abbrev tensorPushforwardSections :=
  (PresheafOfModulesOfCommRing.Monoidal.tensorObj
    (R := (FibredSite.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf).obj)
    (pushUnit a).val (pushUnit b).val).obj (op x)

/-- The leg at `(c, h)` of the map `a_*𝒪_𝒴 ⊗ b_*𝒪_𝒵 ⟶ f_*𝒪_𝒫` over `x`. -/
def tensorLeg
    (j : StructuredArrow (op x) (CatFiberedInGroupoids.homFunctor (tensorProj a b).hom).op) :
    tensorPushforwardSections a b x →+
      FibredSite.objRing B S hS (tensorApex a b).val.val.p j.right.unop :=
  TensorProduct.liftAddHom (tensorLegBilin j) (fun r s t => by
    have e₁ : unitLeg a (legFst j) (r • s) = legRingHom a (legFst j) r * unitLeg a (legFst j) s :=
      unitLeg_smul a (legFst j) r s
    have e₂ : unitLeg b (legSnd j) (r • t) = legRingHom b (legSnd j) r * unitLeg b (legSnd j) t :=
      unitLeg_smul b (legSnd j) r t
    rw [tensorLegBilin_apply, tensorLegBilin_apply, e₁, e₂]
    exact mul_map_mul_eq_map_mul_mul _ _ _ _ _ _
      ((fstRingHom_legRingHom j r).trans (sndRingHom_legRingHom j r).symm))

/-- `tensorLeg j (s ⊗ₜ t) = pr₁^*s · pr₂^*t`. -/
lemma tensorLeg_tmul
    (j : StructuredArrow (op x) (CatFiberedInGroupoids.homFunctor (tensorProj a b).hom).op)
    (s : (pushUnit a).val.obj (op x)) (t : (pushUnit b).val.obj (op x)) :
    tensorLeg j (s ⊗ₜ t) =
      fstRingHom j.right.unop (unitLeg a (legFst j) s) *
        sndRingHom j.right.unop (unitLeg b (legSnd j) t) :=
  rfl

/-- The morphism of legs of `a_*𝒪_𝒴` underneath a morphism of legs of `f_*𝒪_𝒫`. -/
abbrev legFstMap
    {j₁ j₂ : StructuredArrow (op x) (CatFiberedInGroupoids.homFunctor (tensorProj a b).hom).op}
    (φ : j₁ ⟶ j₂) : legFst j₁ ⟶ legFst j₂ :=
  StructuredArrow.homMk (φ.right.unop.a).op (StructuredArrow.w φ)

/-- The morphism of legs of `b_*𝒪_𝒵` underneath a morphism of legs of `f_*𝒪_𝒫`. -/
abbrev legSndMap
    {j₁ j₂ : StructuredArrow (op x) (CatFiberedInGroupoids.homFunctor (tensorProj a b).hom).op}
    (φ : j₁ ⟶ j₂) : legSnd j₁ ⟶ legSnd j₂ :=
  StructuredArrow.homMk (φ.right.unop.b).op (Quiver.Hom.unop_inj
    ((TwoFibreProductOver.Hom.map_b_comp_iso_inv_comp φ.right.unop j₁.hom.unop).trans
      (congrArg (j₂.right.unop.iso.inv ≫ ·) (congrArg Quiver.Hom.unop (StructuredArrow.w φ)))))

/-- `fstRingHom` is natural in morphisms of legs of `f_*𝒪_𝒫`. -/
lemma fstRingHom_naturality
    {j₁ j₂ : StructuredArrow (op x) (CatFiberedInGroupoids.homFunctor (tensorProj a b).hom).op}
    (φ : j₁ ⟶ j₂) (z : FibredSite.objRing B S hS 𝒴.val.val.p j₁.right.unop.x) :
    baseRingHom ((tensorApex a b).val.val.p.map φ.right.unop) (fstRingHom j₁.right.unop z) =
      fstRingHom j₂.right.unop (baseRingHom (𝒴.val.val.p.map φ.right.unop.a) z) :=
  baseRingHom_comp_eq _ _ _ _ (TwoFibreProductOver.Hom.hbase_comp_eqToHom_fst φ.right.unop) z

/-- `sndRingHom` is natural in morphisms of legs of `f_*𝒪_𝒫`. -/
lemma sndRingHom_naturality
    {j₁ j₂ : StructuredArrow (op x) (CatFiberedInGroupoids.homFunctor (tensorProj a b).hom).op}
    (φ : j₁ ⟶ j₂) (z : FibredSite.objRing B S hS 𝒵.val.val.p j₁.right.unop.y) :
    baseRingHom ((tensorApex a b).val.val.p.map φ.right.unop) (sndRingHom j₁.right.unop z) =
      sndRingHom j₂.right.unop (baseRingHom (𝒵.val.val.p.map φ.right.unop.b) z) :=
  baseRingHom_comp_eq _ _ _ _ (TwoFibreProductOver.Hom.hbase_comp_eqToHom_snd φ.right.unop) z

/-- The tensor legs form a cone: they are compatible with morphisms of legs of `f_*𝒪_𝒫`. -/
lemma tensorLeg_naturality
    {j₁ j₂ : StructuredArrow (op x) (CatFiberedInGroupoids.homFunctor (tensorProj a b).hom).op}
    (φ : j₁ ⟶ j₂) (m : tensorPushforwardSections a b x) :
    baseRingHom ((tensorApex a b).val.val.p.map φ.right.unop) (tensorLeg j₁ m) =
      tensorLeg j₂ m := by
  induction m using TensorProduct.inductionOn with
  | tmul s t =>
    exact (congrArg (baseRingHom ((tensorApex a b).val.val.p.map φ.right.unop))
      (tensorLeg_tmul j₁ s t)).trans (((map_mul _ _ _).trans (congrArg₂ (· * ·)
        ((fstRingHom_naturality φ _).trans (congrArg (fstRingHom j₂.right.unop)
          (unitLeg_naturality a (legFstMap φ) s)))
        ((sndRingHom_naturality φ _).trans (congrArg (sndRingHom j₂.right.unop)
          (unitLeg_naturality b (legSndMap φ) t))))).trans (tensorLeg_tmul j₂ s t).symm)
  | add m m' hm hm' =>
    exact (congrArg (baseRingHom ((tensorApex a b).val.val.p.map φ.right.unop))
      ((tensorLeg j₁).map_add m m')).trans (((map_add _ _ _).trans
        (congrArg₂ (· + ·) hm hm')).trans ((tensorLeg j₂).map_add m m').symm)

/-- Restriction of functions along the image of an identity is the identity. -/
lemma baseRingHom_map_id (𝒲 : AlgebraicStacks.{u, w} B S hS) (w : 𝒲.val.val.obj)
    (z : FibredSite.objRing B S hS 𝒲.val.val.p w) :
    baseRingHom (𝒲.val.val.p.map (𝟙 w)) z = z :=
  (congrArg (fun m => baseRingHom m z) (𝒲.val.val.p.map_id w)).trans rfl

/-- Restriction along `g : op x ⟶ op x'` followed by a tensor leg at `j` is the tensor leg at the
leg `j` precomposed with `g`. -/
lemma tensorLeg_map {x' : 𝒳.val.val.obj} (g : op x ⟶ op x')
    (j : StructuredArrow (op x') (CatFiberedInGroupoids.homFunctor (tensorProj a b).hom).op)
    (m : tensorPushforwardSections a b x) :
    tensorLeg j ((PresheafOfModulesOfCommRing.Monoidal.tensorObj
      (R := (FibredSite.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf).obj)
      (pushUnit a).val (pushUnit b).val).map g m) =
        tensorLeg ((StructuredArrow.map g).obj j) m := by
  induction m using TensorProduct.inductionOn with
  | tmul s t =>
    have hb : unitLeg b (legSnd j) ((pushUnit b).val.map g t) =
        unitLeg b (legSnd ((StructuredArrow.map g).obj j)) t :=
      (unitLeg_map b g (legSnd j) t).trans ((baseRingHom_map_id 𝒵 _ _).symm.trans
        (unitLeg_naturality b (StructuredArrow.homMk (𝟙 _) (((congrArg (_ ≫ ·)
          ((CatFiberedInGroupoids.homFunctor b.hom).op.map_id _)).trans (Category.comp_id _)).trans
            (Category.assoc _ _ _).symm) :
          (StructuredArrow.map g).obj (legSnd j) ⟶ legSnd ((StructuredArrow.map g).obj j)) t))
    exact (tensorLeg_tmul j _ _).trans ((congrArg₂ (· * ·)
      (congrArg (fstRingHom j.right.unop) (unitLeg_map a g (legFst j) s))
      (congrArg (sndRingHom j.right.unop) hb)).trans
        (tensorLeg_tmul ((StructuredArrow.map g).obj j) s t).symm)
  | add m m' hm hm' =>
    exact (congrArg (tensorLeg j) (map_add ((PresheafOfModulesOfCommRing.Monoidal.tensorObj
      (R := (FibredSite.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf).obj)
      (pushUnit a).val (pushUnit b).val).map g).hom m m')).trans (((tensorLeg j).map_add _ _).trans
      ((congrArg₂ (· + ·) hm hm').trans ((tensorLeg _).map_add m m').symm))

variable (a b x) in
/-- The cone of tensor legs over the diagram computing the sections of `f_*𝒪_𝒫` over `x`. -/
def tensorCone : Cone (StructuredArrow.proj (op x)
    (CatFiberedInGroupoids.homFunctor (tensorProj a b).hom).op ⋙
      (unitModule (tensorApex a b)).val.presheaf) where
  pt := AddCommGrpCat.of (tensorPushforwardSections a b x)
  π :=
    { app := fun j => AddCommGrpCat.ofHom (tensorLeg j)
      naturality := fun j₁ j₂ φ => by
        ext m
        exact (tensorLeg_naturality φ m).symm }

variable (a b x) in
/-- **The map `a_*𝒪_𝒴 ⊗ b_*𝒪_𝒵 ⟶ f_*𝒪_𝒫` on sections over `x`**: `s ⊗ t ↦ pr₁^*s · pr₂^*t`,
defined by its legs. -/
def tensorPushforwardMapApp :
    AddCommGrpCat.of (tensorPushforwardSections a b x) ⟶
      (pushUnit (tensorProj a b)).val.presheaf.obj (op x) :=
  (Stacks.SheafOfModules.ranIsLimit (CatFiberedInGroupoids.homFunctor (tensorProj a b).hom).op
    (unitModule (tensorApex a b)).val.presheaf (op x)).lift (tensorCone a b x)

/-- The leg of `f_*𝒪_𝒫` at `j` of `tensorPushforwardMapApp a b x m` is `tensorLeg j m`. -/
lemma unitLeg_tensorPushforwardMapApp
    (j : StructuredArrow (op x) (CatFiberedInGroupoids.homFunctor (tensorProj a b).hom).op)
    (m : tensorPushforwardSections a b x) :
    unitLeg (tensorProj a b) j (tensorPushforwardMapApp a b x m) = tensorLeg j m :=
  ConcreteCategory.congr_hom ((Stacks.SheafOfModules.ranIsLimit
    (CatFiberedInGroupoids.homFunctor (tensorProj a b).hom).op
    (unitModule (tensorApex a b)).val.presheaf (op x)).fac (tensorCone a b x) j) m

/-- The tensor legs are semilinear along `legRingHom`. -/
lemma tensorLeg_smul
    (j : StructuredArrow (op x) (CatFiberedInGroupoids.homFunctor (tensorProj a b).hom).op)
    (r : ((FibredSite.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf).obj ⋙
      forget₂ CommRingCat RingCat).obj (op x)) (m : tensorPushforwardSections a b x) :
    tensorLeg j (r • m) = legRingHom (tensorProj a b) j r * tensorLeg j m := by
  induction m using TensorProduct.inductionOn with
  | tmul s t =>
    have e₁ : unitLeg a (legFst j) (r • s) = legRingHom a (legFst j) r * unitLeg a (legFst j) s :=
      unitLeg_smul a (legFst j) r s
    refine (congrArg (tensorLeg j) (TensorProduct.smul_tmul'
      (show ((FibredSite.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        .fppf).obj.obj (op x)) from r) s t)).trans ?_
    refine (tensorLeg_tmul j (r • s) t).trans ?_
    refine (congrArg (fun z => fstRingHom j.right.unop z * sndRingHom j.right.unop
      (unitLeg b (legSnd j) t)) e₁).trans ?_
    refine (congrArg (· * sndRingHom j.right.unop (unitLeg b (legSnd j) t)) ((map_mul _ _ _).trans
      (congrArg (fun z => z * fstRingHom j.right.unop (unitLeg a (legFst j) s))
        (fstRingHom_legRingHom j r)))).trans ?_
    exact (mul_assoc _ _ _).trans (congrArg (_ * ·) (tensorLeg_tmul j s t).symm)
  | add m m' hm hm' =>
    exact (congrArg (tensorLeg j) (smul_add
      (show ((FibredSite.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        .fppf).obj.obj (op x)) from r) m m')).trans (((tensorLeg j).map_add _ _).trans
      ((congrArg₂ (· + ·) hm hm').trans ((mul_add _ _ _).symm.trans
        (congrArg (_ * ·) ((tensorLeg j).map_add m m').symm))))

variable (a b) in
/-- **The canonical map `a_*𝒪_𝒴 ⊗ b_*𝒪_𝒵 ⟶ f_*𝒪_𝒫` of presheaves of modules**, from the
objectwise tensor product: `s ⊗ t ↦ pr₁^*s · pr₂^*t`. -/
def tensorPushforwardPresheafMap :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj
      (R := (FibredSite.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf).obj)
      (pushUnit a).val (pushUnit b).val ⟶ (pushUnit (tensorProj a b)).val :=
  PresheafOfModules.homMk
    { app := fun X => tensorPushforwardMapApp a b X.unop
      naturality := fun X X' g => by
        refine Stacks.SheafOfModules.ran_hom_ext _ _ (fun j => ?_)
        ext m
        exact (unitLeg_tensorPushforwardMapApp j _).trans ((tensorLeg_map g j m).trans
          ((unitLeg_tensorPushforwardMapApp _ m).symm.trans (unitLeg_map _ g j _).symm)) }
    (fun X r m => by
      let σ : AddCommGrpCat.of (tensorPushforwardSections a b X.unop) ⟶
          AddCommGrpCat.of (tensorPushforwardSections a b X.unop) :=
        AddCommGrpCat.ofHom (AddMonoidHom.mk' (fun m => r • m) (smul_add r))
      have h : σ ≫ tensorPushforwardMapApp a b X.unop =
          tensorPushforwardMapApp a b X.unop ≫ Stacks.SheafOfModules.ranSMul
            (CatFiberedInGroupoids.homFunctor (tensorProj a b).hom)
            (moduleDirectImageStructureMap B S hS (tensorApex a b).val.val.p 𝒳.val.val.p
              (tensorApex a b).val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
              (CatFiberedInGroupoids.homFunctor (tensorProj a b).hom)
              (CatFiberedInGroupoids.homFunctor_comp_p (tensorProj a b).hom) B.topology
              le_rfl).hom
            (unitModule (tensorApex a b)).val X r := by
        refine Stacks.SheafOfModules.ran_hom_ext _ _ (fun j => ?_)
        ext m'
        exact (unitLeg_tensorPushforwardMapApp j _).trans ((tensorLeg_smul j r m').trans
          ((congrArg (_ * ·) (unitLeg_tensorPushforwardMapApp j m').symm).trans
            (unitLeg_smul (tensorProj a b) j r _).symm))
      exact ConcreteCategory.congr_hom h m)

variable (a b) in
/-- The first factor of `AlgebraicGeometry.Stack.AlgebraicStacks.tensorPushforwardPresheafComp`:
the objectwise tensor product of the counits `Q(a_*𝒪) ⟶ a_*𝒪`, `Q(b_*𝒪) ⟶ b_*𝒪`. -/
def tensorPushforwardCounitTensor :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj
      (R := (FibredSite.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf).obj)
      ((quasicoherentInclusion B S hS 𝒳).obj (pushforwardUnit a)).val
      ((quasicoherentInclusion B S hS 𝒳).obj (pushforwardUnit b)).val ⟶
    PresheafOfModulesOfCommRing.Monoidal.tensorObj
      (R := (FibredSite.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf).obj)
      (pushUnit a).val (pushUnit b).val :=
  PresheafOfModulesOfCommRing.Monoidal.tensorHom
    ((coheratorAdjunction B S hS 𝒳).counit.app _ ≫
      (fppfModulesPushforwardIsoModuleDirectImage B S hS a).hom.app _).val
    ((coheratorAdjunction B S hS 𝒳).counit.app _ ≫
      (fppfModulesPushforwardIsoModuleDirectImage B S hS b).hom.app _).val

variable (a b) in
/-- The last factor of `AlgebraicGeometry.Stack.AlgebraicStacks.tensorPushforwardPresheafComp`. -/
def tensorPushforwardIsoInv :
    (pushUnit (tensorProj a b)).val ⟶
    ((fppfModulesPushforward B S hS (tensorProj a b)).obj
      ((quasicoherentInclusion B S hS (tensorApex a b)).obj (qcUnit (tensorApex a b)))).val :=
  ((fppfModulesPushforwardIsoModuleDirectImage B S hS (tensorProj a b)).inv.app _).val

variable (a b) in
/-- The presheaf map underlying `AlgebraicGeometry.Stack.AlgebraicStacks.tensorPushforwardMap`:
`Q(a_*𝒪) ⊗_p Q(b_*𝒪) ⟶ a_*𝒪 ⊗_p b_*𝒪 ⟶ f_*𝒪`, through the counits of the coherator. -/
def tensorPushforwardPresheafComp :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj
      (R := (FibredSite.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf).obj)
      ((quasicoherentInclusion B S hS 𝒳).obj (pushforwardUnit a)).val
      ((quasicoherentInclusion B S hS 𝒳).obj (pushforwardUnit b)).val ⟶
    ((fppfModulesPushforward B S hS (tensorProj a b)).obj
      ((quasicoherentInclusion B S hS (tensorApex a b)).obj (qcUnit (tensorApex a b)))).val :=
  tensorPushforwardCounitTensor a b ≫ tensorPushforwardPresheafMap a b ≫
    tensorPushforwardIsoInv a b

attribute [local instance] fppfModulesMonoidal fppfModulesBraided fppfModulesSymmetric in
variable (a b) in
/-- **The canonical map of Stacks 0GRN**, `μ : a_{QCoh,*}𝒪_𝒴 ⊗ b_{QCoh,*}𝒪_𝒵 ⟶ f_{QCoh,*}𝒪_𝒫`
in `QCoh(𝒪_𝒳)`, for `f : 𝒫 = 𝒴 ×_𝒳 𝒵 ⟶ 𝒳` the projection of the 2-fibre product. On sections
it is `s ⊗ t ↦ pr₁^*s · pr₂^*t`. It is the adjoint transpose, along the coherator adjunction
`i ⊣ Q`, of the map `Q(a_*𝒪) ⊗ Q(b_*𝒪) ⟶ a_*𝒪 ⊗ b_*𝒪 ⟶ f_*𝒪_𝒫` of `𝒪_𝒳`-modules, the second
arrow being the sheafification of the objectwise map
`AlgebraicGeometry.Stack.AlgebraicStacks.tensorPushforwardPresheafMap`.

In terms of the abbreviations
`pushforwardUnit g = (quasicoherentDirectImage B S hS g).obj (𝟙_ _)`,
`tensorPushforwardUnits a b = pushforwardUnit a ⊗ pushforwardUnit b` and
`tensorProj a b = (twoFibreProductSquareAlgebraicStacks B S hS a b).fst ≫ a`, `μ` is a map
`(quasicoherentDirectImage a).obj (𝟙_ _) ⊗ (quasicoherentDirectImage b).obj (𝟙_ _) ⟶
(quasicoherentDirectImage (pr₁ ≫ a)).obj (𝟙_ _)`, as
`AlgebraicGeometry.Stack.AlgebraicStacks.nonempty_iso_tensorPushforward` states. -/
def tensorPushforwardMap : tensorPushforwardUnits a b ⟶ pushforwardUnit (tensorProj a b) :=
  (coheratorAdjunction B S hS 𝒳).homEquiv _ _
    (((PresheafOfModules.sheafificationAdjunction
      (𝟙 (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        .fppf).obj)).homEquiv _ _).symm (tensorPushforwardPresheafComp a b))

end Construction

section Bijective

attribute [local instance] FibredSite.objModule

/-- The leg of a direct image at a terminal arrow is bijective. -/
lemma bijective_unitLeg_of_isTerminal {𝒲 𝒱 : AlgebraicStacks.{u, w} B S hS} (g : 𝒲 ⟶ 𝒱)
    {x : 𝒱.val.val.obj} {t : CostructuredArrow (CatFiberedInGroupoids.homFunctor g.hom) x}
    (ht : IsTerminal t) :
    Function.Bijective (unitLeg g (StructuredArrow.mk (Y := op t.left) t.hom.op)) := by
  have := Stacks.SheafOfModules.isIso_ranπ_of_isTerminal
    (CatFiberedInGroupoids.homFunctor g.hom) (unitModule 𝒲).val.presheaf ht
  set π := Stacks.SheafOfModules.ranπ (CatFiberedInGroupoids.homFunctor g.hom).op
    (unitModule 𝒲).val.presheaf (op x) (StructuredArrow.mk (Y := op t.left) t.hom.op) with hπ
  have e₁ : ∀ m, inv π (π m) = m := fun m => by
    have e := ConcreteCategory.congr_hom (IsIso.hom_inv_id π) m
    simpa only [CategoryTheory.comp_apply, CategoryTheory.id_apply] using e
  have e₂ : ∀ z, π (inv π z) = z := fun z => by
    have e := ConcreteCategory.congr_hom (IsIso.inv_hom_id π) z
    simpa only [CategoryTheory.comp_apply, CategoryTheory.id_apply] using e
  exact ⟨fun m₁ m₂ h => (e₁ m₁).symm.trans ((congrArg (inv π) h).trans (e₁ m₂)),
    fun z => ⟨inv π z, e₂ z⟩⟩

/-- An isomorphism of sheaves of modules is bijective on sections. -/
lemma bijective_val_app_of_iso {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R} (e : M ≅ N) (X : Cᵒᵖ) :
    Function.Bijective (e.hom.val.app X) := by
  have : IsIso (e.hom.val.app X) :=
    (inferInstance : IsIso ((SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj X).mapIso
      e).hom)
  exact ConcreteCategory.bijective_of_isIso _

/-- The counit of the coherator followed by the pushforward comparison isomorphism is bijective on
sections over a flat object, for `g` quasi-compact and quasi-separated. -/
private theorem bijective_counit_comp_pushforwardIso_app {𝒲 𝒱 : AlgebraicStacks.{u, w} B S hS}
    (g : 𝒲 ⟶ 𝒱) (hqc : IsQuasiCompactMorphism B S hS g)
    (hqs : AlgebraicStacks.IsQuasiSeparated B S hS g)
    (F : quasicoherentModules B S hS 𝒲) {x : 𝒱.val.val.obj} (hx : flatObject B S hS 𝒱.val x) :
    Function.Bijective (((coheratorAdjunction B S hS 𝒱).counit.app
      ((fppfModulesPushforward B S hS g).obj ((quasicoherentInclusion B S hS 𝒲).obj F)) ≫
        (fppfModulesPushforwardIsoModuleDirectImage B S hS g).hom.app
          ((quasicoherentInclusion B S hS 𝒲).obj F)).val.app (op x)) :=
  (bijective_val_app_of_iso ((fppfModulesPushforwardIsoModuleDirectImage B S hS g).app _)
    (op x)).comp (bijective_coheratorAdjunction_counit_directImage B S hS g hqc hqs F x hx).1

/-- The inverse of a natural isomorphism of functors to sheaves of modules is bijective on
sections. -/
lemma bijective_natIso_inv_val_app {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {D : Type*} [Category D] {F G : D ⥤ SheafOfModules.{u} R}
    (α : F ≅ G) (M : D) (X : Cᵒᵖ) : Function.Bijective ((α.inv.app M).val.app X) :=
  bijective_val_app_of_iso (α.app M).symm X

/-- Equal morphisms of presheaves of modules have equal components. -/
lemma presheafOfModules_congr_app {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    {M N : PresheafOfModules.{u} R} {f g : M ⟶ N} (h : f = g) (X : Cᵒᵖ) : f.app X = g.app X := by
  rw [h]

/-- Sections of a composite of morphisms of sheaves of modules. -/
lemma bijective_comp_val_app {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N K : SheafOfModules.{u} R} (f : M ⟶ N) (g : N ⟶ K) (X : Cᵒᵖ)
    (hf : Function.Bijective (f.val.app X)) (hg : Function.Bijective (g.val.app X)) :
    Function.Bijective ((f ≫ g).val.app X) :=
  hg.comp hf

/-- Sections of a composite of morphisms of presheaves of modules. -/
lemma bijective_comp_app {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    {M N K : PresheafOfModules.{u} R} (f : M ⟶ N) (g : N ⟶ K) (X : Cᵒᵖ)
    (hf : Function.Bijective (f.app X)) (hg : Function.Bijective (g.app X)) :
    Function.Bijective ((f ≫ g).app X) :=
  hg.comp hf

/-- The ring map of an identification of the base is bijective. -/
lemma bijective_baseRingHom_eqToHom {U V : BigFppfOver B S hS} (h : U = V) :
    Function.Bijective (baseRingHom (eqToHom h)) := by
  subst h
  simpa [baseRingHom] using Function.bijective_id

/-- For `a` affine and flat and `b` representable, quasi-compact and quasi-separated, the map
`s ⊗ t ↦ pr₁^*s · pr₂^*t` is bijective on sections over a flat object `x` lying over an affine
scheme. -/
theorem bijective_tensorPushforwardMapApp (ha : AlgebraicStacks.IsAffineHom B S hS a)
    (haf : AlgebraicStacks.IsFlat B S hS a)
    (hbr : Stacks.RepresentableMorphism.IsRepresentableMorphism 𝒵.val.val.p 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor b.hom))
    (hbqc : IsQuasiCompactMorphism B S hS b) (hbqs : AlgebraicStacks.IsQuasiSeparated B S hS b)
    {x : 𝒳.val.val.obj} (hx : flatObject B S hS 𝒳.val x)
    (hxa : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x))) :
    Function.Bijective (tensorPushforwardMapApp a b x) := by
  obtain ⟨ta, ⟨hta⟩, hVa, hαf⟩ :=
    exists_isTerminal_of_isAffineHom_of_isFlat B S hS a ha haf x hxa
  obtain ⟨tb, ⟨htb⟩⟩ := Stacks.RepresentableMorphism.exists_isTerminal_costructuredArrow
    (CatFiberedInGroupoids.homFunctor_comp_p b.hom) 𝒳.val.isFiberedInGroupoids hbr
    ((CatFiberedInGroupoids.homFunctor a.hom).obj ta.left)
  obtain ⟨P, k, hPy, hk, ⟨htf⟩⟩ := TwoFibreProductOver.exists_isTerminal_fst_comp
    𝒴.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor_comp_p a.hom) (CatFiberedInGroupoids.homFunctor_comp_p b.hom)
    hta htb
  let jF : StructuredArrow (op x) (CatFiberedInGroupoids.homFunctor (tensorProj a b).hom).op :=
    StructuredArrow.mk (Y := op P) ((CatFiberedInGroupoids.homFunctor a.hom).map k ≫ ta.hom).op
  have hπF : Function.Bijective (unitLeg (tensorProj a b) jF) :=
    bijective_unitLeg_of_isTerminal (tensorProj a b) htf
  refine (Function.Bijective.of_comp_iff' hπF _).1 ?_
  have hcomp : (unitLeg (tensorProj a b) jF) ∘ (tensorPushforwardMapApp a b x) = tensorLeg jF :=
    funext (unitLeg_tensorPushforwardMapApp jF)
  rw [hcomp]
  let y := (CatFiberedInGroupoids.homFunctor a.hom).obj ta.left
  let α : y ⟶ x := ta.hom
  have hya : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y)) := by
    rw [show 𝒳.val.val.p.obj y = 𝒴.val.val.p.obj ta.left from
      Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p a.hom) ta.left]
    exact hVa
  have hyf : flatObject B S hS 𝒳.val y := flatObject_of_flat B S hS 𝒳 α hαf hx
  let QB := (quasicoherentInclusion B S hS 𝒳).obj (pushforwardUnit b)
  let ψB : QB ⟶ pushUnit b := (coheratorAdjunction B S hS 𝒳).counit.app _ ≫
    (fppfModulesPushforwardIsoModuleDirectImage B S hS b).hom.app _
  have hψB : ∀ z : 𝒳.val.val.obj, flatObject B S hS 𝒳.val z →
      Function.Bijective (ψB.val.app (op z)) := fun z hz =>
    bijective_counit_comp_pushforwardIso_app b hbqc hbqs (qcUnit 𝒵) hz
  let := FibredSite.objAlgebra B S hS 𝒳.val.val.p α
  let : Module (FibredSite.objRing B S hS 𝒳.val.val.p x) (QB.val.obj (op y)) :=
    Module.compHom _ (algebraMap (FibredSite.objRing B S hS 𝒳.val.val.p x)
      (FibredSite.objRing B S hS 𝒳.val.val.p y))
  have : IsScalarTower (FibredSite.objRing B S hS 𝒳.val.val.p x)
      (FibredSite.objRing B S hS 𝒳.val.val.p y) (QB.val.obj (op y)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let jA : StructuredArrow (op x) (CatFiberedInGroupoids.homFunctor a.hom).op :=
    StructuredArrow.mk (Y := op ta.left) ta.hom.op
  let ι : FibredSite.objRing B S hS 𝒴.val.val.p ta.left →+*
      FibredSite.objRing B S hS 𝒳.val.val.p y :=
    baseRingHom (eqToHom (Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p a.hom)
      ta.left))
  have hι : ∀ r : FibredSite.objRing B S hS 𝒳.val.val.p x,
      ι (legRingHom a jA r) = algebraMap _ (FibredSite.objRing B S hS 𝒳.val.val.p y) r := by
    intro r
    refine (congrArg ι (legRingHom_apply a jA r)).trans ?_
    refine (baseRingHom_eqToHom_eqToHom _ _ _).trans ?_
    simp only [eqToHom_refl]
    rfl
  let τl : (pushUnit a).val.obj (op x) →ₗ[FibredSite.objRing B S hS 𝒳.val.val.p x]
      FibredSite.objRing B S hS 𝒳.val.val.p y :=
    { toFun := fun s => ι (unitLeg a jA s)
      map_add' := fun s s' => by rw [map_add, map_add]
      map_smul' := fun r s => by
        change ι (unitLeg a jA (r • s)) = algebraMap (FibredSite.objRing B S hS 𝒳.val.val.p x)
          (FibredSite.objRing B S hS 𝒳.val.val.p y) r * ι (unitLeg a jA s)
        exact (congrArg ι (unitLeg_smul a jA r s)).trans ((map_mul _ _ _).trans
          (congrArg (· * ι (unitLeg a jA s)) (hι r))) }
  have hτ : Function.Bijective τl :=
    (bijective_baseRingHom_eqToHom _).comp (bijective_unitLeg_of_isTerminal a hta)
  let ψx : QB.val.obj (op x) →ₗ[FibredSite.objRing B S hS 𝒳.val.val.p x]
      (pushUnit b).val.obj (op x) :=
    { toFun := fun q => ψB.val.app (op x) q
      map_add' := map_add (ψB.val.app (op x)).hom
      map_smul' := (ψB.val.app (op x)).hom.map_smul }
  let eψ := LinearEquiv.ofBijective ψx (hψB x hx)
  let L := (FibredSite.restrictionLinear QB α).liftBaseChange
    (FibredSite.objRing B S hS 𝒳.val.val.p y)
  have hL : Function.Bijective L :=
    FibredSite.bijective_liftBaseChange_of_eq_restriction QB (pushforwardUnit b).property α hxa hya
      (FibredSite.restrictionLinear QB α) (fun _ => rfl)
  let jB' : StructuredArrow (op y) (CatFiberedInGroupoids.homFunctor b.hom).op :=
    StructuredArrow.mk (Y := op tb.left) tb.hom.op
  let pe := baseRingHom (𝒵.val.val.p.map (eqToHom hPy))
  have hpe : Function.Bijective pe := by
    have : 𝒵.val.val.p.map (eqToHom hPy) = eqToHom (congrArg 𝒵.val.val.p.obj hPy) :=
      eqToHom_map _ _
    simp only [pe, this]
    exact bijective_baseRingHom_eqToHom _
  let Φ : TensorProduct (FibredSite.objRing B S hS 𝒳.val.val.p x)
      (FibredSite.objRing B S hS 𝒳.val.val.p y) (QB.val.obj (op x)) →+
      FibredSite.objRing B S hS (tensorApex a b).val.val.p P :=
    ((sndRingHom P).toAddMonoidHom.comp pe.toAddMonoidHom).comp
      ((unitLeg b jB').comp ((ψB.val.app (op y)).hom.toAddMonoidHom.comp L.toAddMonoidHom))
  have hΦ : Function.Bijective Φ :=
    ((bijective_baseRingHom_eqToHom _).comp hpe).comp
      ((bijective_unitLeg_of_isTerminal b htb).comp ((hψB y hyf).comp hL))
  have hring : ∀ z : FibredSite.objRing B S hS 𝒴.val.val.p ta.left,
      fstRingHom P (baseRingHom (𝒴.val.val.p.map k) z) =
        sndRingHom P (pe (legRingHom b jB' (ι z))) := fun z =>
    (baseRingHom_fst_eq_snd (CatFiberedInGroupoids.homFunctor_comp_p a.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p b.hom) P k tb.hom hPy hk z).trans
      (congrArg (fun w => sndRingHom P (pe w)) (legRingHom_apply b jB' (ι z)).symm)
  have H : ∀ s q, tensorLeg jF (s ⊗ₜ ψx q) = Φ (τl s ⊗ₜ q) := by
    intro s q
    have e1 : unitLeg a (legFst jF) s = baseRingHom (𝒴.val.val.p.map k) (unitLeg a jA s) :=
      (unitLeg_naturality a (StructuredArrow.homMk k.op rfl : jA ⟶ legFst jF) s).symm
    have e2 : unitLeg b (legSnd jF) (ψx q) =
        pe (unitLeg b jB' (ψB.val.app (op y) (QB.val.map α.op q))) :=
      (unitLeg_naturality b (StructuredArrow.homMk (eqToHom hPy).op
        (op_comp_map_eqToHom_op_eq k tb.hom hPy hk α) :
          (StructuredArrow.map α.op).obj jB' ⟶ legSnd jF) (ψx q)).symm.trans
        (congrArg pe ((unitLeg_map b α.op jB' (ψx q)).symm.trans (congrArg (unitLeg b jB')
          (PresheafOfModules.naturality_apply ψB.val α.op q).symm)))
    have e3 : Φ (τl s ⊗ₜ q) = sndRingHom P (pe (legRingHom b jB' (τl s))) *
        sndRingHom P (pe (unitLeg b jB' (ψB.val.app (op y) (QB.val.map α.op q)))) :=
      (congrArg (fun w => sndRingHom P (pe (unitLeg b jB' w)))
        ((ψB.val.app (op y)).hom.map_smul (τl s) (QB.val.map α.op q))).trans
        ((congrArg (fun w => sndRingHom P (pe w)) (unitLeg_smul b jB' (τl s) _)).trans
          ((congrArg (sndRingHom P) (map_mul pe _ _)).trans (map_mul _ _ _)))
    exact (tensorLeg_tmul jF s (ψx q)).trans ((congrArg₂ (· * ·) ((congrArg (fstRingHom P) e1).trans
      (hring _)) (congrArg (sndRingHom P) e2)).trans e3.symm)
  exact Function.Bijective.of_tmul_eq (LinearEquiv.ofBijective τl hτ) eψ.symm (tensorLeg jF) Φ hΦ
    (fun s t => (congrArg (fun t' => tensorLeg jF (s ⊗ₜ t')) (eψ.apply_symm_apply t).symm).trans
      (H s (eψ.symm t)))

/-- **A morphism of quasi-coherent modules on an algebraic stack which is bijective on the
sections over every flat object lying over an affine scheme is an isomorphism.** This is
`AlgebraicGeometry.Stack.isIso_of_flatObject` with the hypothesis restricted to affine flat
objects. -/
theorem isIso_of_flatObject_of_isAffine
    {T P : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .fppf)} (hT : T.IsQuasicoherentOnSite)
    (hP : P.IsQuasicoherentOnSite) (ψ : T ⟶ P)
    (h : ∀ x : 𝒳.val.val.obj, flatObject B S hS 𝒳.val x →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x)) →
        Function.Bijective (ψ.val.app (op x))) : IsIso ψ := by
  have hloc : ∀ ⦃z Y : 𝒳.val.val.obj⦄ (f : Y ⟶ z), affineFlatFactorization B S hS 𝒳 z f →
      Function.Bijective (ψ.val.app (op Y)) := by
    rintro z Y f ⟨hY, x, hx, hxa, ⟨n⟩⟩
    exact bijective_app_of_bijective_app hT hP ψ n hxa hY (h x hx hxa)
  have hinj : ∀ z : 𝒳.val.val.obj, Function.Injective (ψ.val.app (op z)) := by
    intro z a b hab
    refine sections_ext_of_affineFlatFactorization T (fun Y f hf => ?_)
    apply (hloc f hf).1
    rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply, hab]
  have hbij : ∀ y : 𝒳.val.val.obj, Function.Bijective (ψ.val.app (op y)) := by
    intro y
    refine ⟨hinj y, fun s => ?_⟩
    let R := affineFlatFactorization B S hS 𝒳 y
    have hsh : Presieve.IsSheafFor (T.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u})
        R := by
      rw [Presieve.isSheafFor_iff_generate]
      exact T.isSheaf_sections.isSheafFor _ (affineFlatFactorization_mem B S hS 𝒳 y)
    let pre : ∀ ⦃Y : 𝒳.val.val.obj⦄ (f : Y ⟶ y), R f → T.val.obj (op Y) := fun Y f hf =>
      (Equiv.ofBijective _ (hloc f hf)).symm (P.val.map f.op s)
    have ht : ∀ ⦃Y : 𝒳.val.val.obj⦄ (f : Y ⟶ y) (hf : R f),
        ψ.val.app (op Y) (pre f hf) = P.val.map f.op s := fun Y f hf =>
      (Equiv.ofBijective _ (hloc f hf)).apply_symm_apply _
    let t : Presieve.FamilyOfElements
        (T.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u}) R :=
      fun Y f hf => pre f hf
    have hcompat : t.Compatible := by
      intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ hcomm
      apply hinj Z
      change ψ.val.app (op Z) (T.val.map g₁.op (pre f₁ hf₁)) =
        ψ.val.app (op Z) (T.val.map g₂.op (pre f₂ hf₂))
      rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply, ht f₁ hf₁,
        ht f₂ hf₂, ← P.val.map_comp_apply, ← P.val.map_comp_apply, ← op_comp, ← op_comp, hcomm]
    have ha : ∀ ⦃Y : 𝒳.val.val.obj⦄ (f : Y ⟶ y) (hf : R f),
        T.val.map f.op (hsh.amalgamate t hcompat) = pre f hf :=
      fun Y f hf => hsh.valid_glue hcompat f hf
    refine ⟨hsh.amalgamate t hcompat, sections_ext_of_affineFlatFactorization P
      (fun Y f hf => ?_)⟩
    exact (PresheafOfModules.naturality_apply ψ.val f.op _).symm.trans
      ((congrArg (ψ.val.app (op Y)) (ha f hf)).trans (ht f hf))
  have : IsIso ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map ψ) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro y
    rw [ConcreteCategory.isIso_iff_bijective]
    exact hbij y.unop
  exact isIso_of_reflects_iso ψ (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _)

/-- The objectwise tensor product of two morphisms of presheaves of modules which are bijective
at `X` is bijective at `X`. -/
lemma bijective_tensorHom_app {C : Type*} [Category C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
    {M₁ M₂ M₃ M₄ : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (f : M₁ ⟶ M₂) (g : M₃ ⟶ M₄)
    (X : Cᵒᵖ) (hf : Function.Bijective (f.app X)) (hg : Function.Bijective (g.app X)) :
    Function.Bijective ((PresheafOfModulesOfCommRing.Monoidal.tensorHom f g).app X) := by
  rw [PresheafOfModulesOfCommRing.Monoidal.tensorHom_app]
  exact (TensorProduct.congr (LinearEquiv.ofBijective (f.app X).hom hf)
    (LinearEquiv.ofBijective (g.app X).hom hg)).bijective

/-- The component of `tensorPushforwardPresheafMap a b` at `x` is
`tensorPushforwardMapApp a b x`. -/
lemma tensorPushforwardPresheafMap_app_apply {x : 𝒳.val.val.obj}
    (m : tensorPushforwardSections a b x) :
    (tensorPushforwardPresheafMap a b).app (op x) m = tensorPushforwardMapApp a b x m :=
  rfl

/-- For `a` affine and flat and `b` representable, quasi-compact and quasi-separated, the map
`tensorPushforwardPresheafMap a b` is bijective at a flat object lying over an affine scheme. -/
lemma bijective_tensorPushforwardPresheafMap_app (ha : AlgebraicStacks.IsAffineHom B S hS a)
    (haf : AlgebraicStacks.IsFlat B S hS a)
    (hbr : Stacks.RepresentableMorphism.IsRepresentableMorphism 𝒵.val.val.p 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor b.hom))
    (hbqc : IsQuasiCompactMorphism B S hS b) (hbqs : AlgebraicStacks.IsQuasiSeparated B S hS b)
    {x : 𝒳.val.val.obj} (hx : flatObject B S hS 𝒳.val x)
    (hxa : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x))) :
    Function.Bijective ((tensorPushforwardPresheafMap a b).app (op x)) := by
  have h : ⇑((tensorPushforwardPresheafMap a b).app (op x)) = ⇑(tensorPushforwardMapApp a b x) :=
    funext (tensorPushforwardPresheafMap_app_apply a b)
  rw [h]
  exact bijective_tensorPushforwardMapApp a b ha haf hbr hbqc hbqs hx hxa

attribute [local instance] fppfModulesMonoidal fppfModulesBraided fppfModulesSymmetric in
/-- Under the hypotheses of `isIso_tensorPushforwardMap`, the map
`tensorPushforwardPresheafComp a b` is bijective at a flat object lying over an affine scheme. -/
lemma bijective_tensorPushforwardPresheafComp_app (ha : AlgebraicStacks.IsAffineHom B S hS a)
    (haqc : IsQuasiCompactMorphism B S hS a) (haqs : AlgebraicStacks.IsQuasiSeparated B S hS a)
    (haf : AlgebraicStacks.IsFlat B S hS a)
    (hbr : Stacks.RepresentableMorphism.IsRepresentableMorphism 𝒵.val.val.p 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor b.hom))
    (hbqc : IsQuasiCompactMorphism B S hS b) (hbqs : AlgebraicStacks.IsQuasiSeparated B S hS b)
    {x : 𝒳.val.val.obj} (hx : flatObject B S hS 𝒳.val x)
    (hxa : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x))) :
    Function.Bijective ((tensorPushforwardPresheafComp a b).app (op x)) := by
  have h1 : Function.Bijective ((tensorPushforwardCounitTensor a b).app (op x)) :=
    bijective_tensorHom_app _ _ (op x)
      (bijective_counit_comp_pushforwardIso_app a haqc haqs (qcUnit 𝒴) hx)
      (bijective_counit_comp_pushforwardIso_app b hbqc hbqs (qcUnit 𝒵) hx)
  have h2 := bijective_tensorPushforwardPresheafMap_app a b ha haf hbr hbqc hbqs hx hxa
  have h3 : Function.Bijective ((tensorPushforwardIsoInv a b).app (op x)) :=
    bijective_natIso_inv_val_app (fppfModulesPushforwardIsoModuleDirectImage B S hS
      (tensorProj a b)) _ (op x)
  exact bijective_comp_app (tensorPushforwardCounitTensor a b) _ (op x) h1
    (bijective_comp_app (tensorPushforwardPresheafMap a b) (tensorPushforwardIsoInv a b) (op x)
      h2 h3)

set_option maxHeartbeats 2000000 in
-- long proof through the sheafification and coherator adjunctions of fppf module sheaves
attribute [local instance] fppfModulesMonoidal fppfModulesBraided fppfModulesSymmetric in
/-- **Stacks 0GRN, corrected: one leg affine.** Let `a : 𝒴 ⟶ 𝒳` be an affine (Stacks 0CHQ),
quasi-compact, quasi-separated and flat 1-morphism of algebraic stacks and `b : 𝒵 ⟶ 𝒳` one which
is representable (by schemes), quasi-compact and quasi-separated. For the projection
`f = pr₁ ≫ a : 𝒴 ×_𝒳 𝒵 ⟶ 𝒳` of the canonical 2-fibre product, the canonical map
`μ : a_{QCoh,*}𝒪_𝒴 ⊗_{𝒪_𝒳} b_{QCoh,*}𝒪_𝒵 ⟶ f_{QCoh,*}𝒪_{𝒴 ×_𝒳 𝒵}`
(`AlgebraicGeometry.Stack.AlgebraicStacks.tensorPushforwardMap`, `s ⊗ t ↦ pr₁^*s · pr₂^*t`) is an
isomorphism in `QCoh(𝒪_𝒳)`; here `g_{QCoh,*} = quasicoherentDirectImage g`, `⊗` is the tensor
product sheaf of Stacks 0GQM and `𝒪 = 𝟙_`.

Relative to the source: `a` is in addition affine. Without it the statement is false
(`AlgebraicGeometry.Stack.AlgebraicStacks.not_forall_nonempty_tensorPushforwardUnits_iso`: for the
two disjoint punctured planes `V`, `W` of `Spec k[x,y,z,w]/(xz,xw,yz,yw)` the right hand side is
`0` and the left hand side has global sections `Γ(V, 𝒪) ⊗ Γ(W, 𝒪) = k`); the source's proof
breaks at reading off `H⁰` of the derived tensor product, which needs `H¹(V, 𝒪) = 0` and
flatness of `Γ(V, 𝒪)` over the base. With `a` affine, `a_*𝒪` is computed by `Γ(V, 𝒪)` with `V`
affine and flat over the base, and the last step is flat base change of `H⁰`. Flatness of `b`,
and representability of `a` beyond what affineness gives, are not needed and are dropped. -/
@[stacks 0GRN "corrected (one leg affine): for a : 𝒴 ⟶ 𝒳 affine, quasi-compact, \
  quasi-separated and flat and b : 𝒵 ⟶ 𝒳 representable, quasi-compact and quasi-separated, the \
  canonical map a_{QCoh,*}O_𝒴 ⊗ b_{QCoh,*}O_𝒵 ⟶ f_{QCoh,*}O_{𝒴 ×_𝒳 𝒵} is an isomorphism. Added \
  relative to the source: a affine (as printed the tag is false, \
  not_forall_nonempty_tensorPushforwardUnits_iso: two disjoint punctured planes, where \
  H¹(V,O) ≠ 0 and Γ(V,O) is not flat over the base, so H⁰ of the derived tensor product is not \
  the tensor product). Affineness makes a_*O be Γ(V,O) with V affine and flat over the base, so \
  the last step is flat base change of H⁰. Dropped: flatness of b (not needed)",
  sga "3 VIB 11.1" "more general"]
theorem isIso_tensorPushforwardMap (ha : AlgebraicStacks.IsAffineHom B S hS a)
    (haqc : IsQuasiCompactMorphism B S hS a) (haqs : AlgebraicStacks.IsQuasiSeparated B S hS a)
    (haf : AlgebraicStacks.IsFlat B S hS a)
    (hbr : Stacks.RepresentableMorphism.IsRepresentableMorphism 𝒵.val.val.p 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor b.hom))
    (hbqc : IsQuasiCompactMorphism B S hS b) (hbqs : AlgebraicStacks.IsQuasiSeparated B S hS b) :
    IsIso (tensorPushforwardMap a b) := by
  suffices IsIso ((quasicoherentInclusion B S hS 𝒳).map (tensorPushforwardMap a b)) from
    isIso_of_reflects_iso _ (quasicoherentInclusion B S hS 𝒳)
  refine isIso_of_flatObject_of_isAffine (tensorPushforwardUnits a b).property
    (pushforwardUnit (tensorProj a b)).property _ (fun x hx hxa => ?_)
  have hP := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS a b
  have hfqc := isQuasiCompactMorphism_fst_comp B S hS a b _ hP haqc hbqc
  have hfqs := isQuasiSeparated_fst_comp B S hS a b _ hP haqs hbqs
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf).obj)
  let g := (adj.homEquiv _ _).symm (tensorPushforwardPresheafComp a b)
  have h1 : (quasicoherentInclusion B S hS 𝒳).map (tensorPushforwardMap a b) ≫
      (coheratorAdjunction B S hS 𝒳).counit.app _ = g :=
    ((coheratorAdjunction B S hS 𝒳).homEquiv_counit (g := tensorPushforwardMap a b)).symm.trans
      (Equiv.symm_apply_apply _ _)
  have h2 : adj.unit.app _ ≫ (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars _).map g =
      tensorPushforwardPresheafComp a b :=
    (adj.homEquiv_unit (f := g)).symm.trans (Equiv.apply_symm_apply _ _)
  have hψ := bijective_tensorPushforwardPresheafComp_app a b ha haqc haqs haf hbr hbqc hbqs hx hxa
  let E := associatedBigEtaleSite B
  have hE : E.cutoff = B.cutoff := rfl
  have hFc := lqcohSheafFbcFppfModules_quasicoherentInclusion B E hE S hS 𝒳 (pushforwardUnit a)
  have hGc := lqcohSheafFbcFppfModules_quasicoherentInclusion B E hE S hS 𝒳 (pushforwardUnit b)
  have hu := FibredSite.bijective_sheafTensor_unit_app_of_isAffine B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids (pushforwardUnit a).obj (pushforwardUnit b).obj
    (fun ψ hz hx hψ => isIso_restrictionBaseChange_of_flat B E hE S hS _ _
      (pushforwardUnit a).obj.val hFc ψ hψ hz hx)
    (fun ψ hz hx hψ => isIso_restrictionBaseChange_of_flat B E hE S hS _ _
      (pushforwardUnit b).obj.val hGc ψ hψ hz hx) hxa
  have hg : Function.Bijective (g.val.app (op x)) := by
    have e : ⇑(g.val.app (op x)) ∘ ⇑((adj.unit.app (PresheafOfModulesOfCommRing.Monoidal.tensorObj
        (R := (FibredSite.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf).obj)
        ((quasicoherentInclusion B S hS 𝒳).obj (pushforwardUnit a)).val
        ((quasicoherentInclusion B S hS 𝒳).obj (pushforwardUnit b)).val)).app (op x)) =
        ⇑((tensorPushforwardPresheafComp a b).app (op x)) :=
      congrArg DFunLike.coe (congrArg ModuleCat.Hom.hom (presheafOfModules_congr_app h2 (op x)))
    exact (Function.Bijective.of_comp_iff _ hu).1 ((congrArg Function.Bijective e).mpr hψ)
  have hc := (bijective_coheratorAdjunction_counit_directImage B S hS (tensorProj a b) hfqc hfqs
    (qcUnit _) x hx).1
  have e : ⇑(((coheratorAdjunction B S hS 𝒳).counit.app
      ((fppfModulesPushforward B S hS (tensorProj a b)).obj
        ((quasicoherentInclusion B S hS (tensorApex a b)).obj (qcUnit (tensorApex a b))))).val.app
          (op x)) ∘
      ⇑(((quasicoherentInclusion B S hS 𝒳).map (tensorPushforwardMap a b)).val.app (op x)) =
        ⇑(g.val.app (op x)) :=
    congrArg DFunLike.coe (congrArg ModuleCat.Hom.hom
      (presheafOfModules_congr_app (congrArg SheafOfModules.Hom.val h1) (op x)))
  exact (Function.Bijective.of_comp_iff' hc _).1 ((congrArg Function.Bijective e).mpr hg)

attribute [local instance] fppfModulesMonoidal fppfModulesBraided fppfModulesSymmetric in
/-- **Stacks 0GRN, corrected (one leg affine), the asserted isomorphism**
`a_{QCoh,*}𝒪_𝒴 ⊗ b_{QCoh,*}𝒪_𝒵 ≅ f_{QCoh,*}𝒪_{𝒴 ×_𝒳 𝒵}`, under the hypotheses of
`AlgebraicGeometry.Stack.AlgebraicStacks.isIso_tensorPushforwardMap`. -/
@[stacks 0GRN "corrected (one leg affine), the asserted isomorphism \
  a_{QCoh,*}O_𝒴 ⊗ b_{QCoh,*}O_𝒵 ≅ f_{QCoh,*}O_{𝒴 ×_𝒳 𝒵}, for a affine, quasi-compact, \
  quasi-separated and flat and b representable, quasi-compact and quasi-separated; see \
  isIso_tensorPushforwardMap for the added hypothesis (a affine) and why it is needed"]
theorem nonempty_iso_tensorPushforward (ha : AlgebraicStacks.IsAffineHom B S hS a)
    (haqc : IsQuasiCompactMorphism B S hS a) (haqs : AlgebraicStacks.IsQuasiSeparated B S hS a)
    (haf : AlgebraicStacks.IsFlat B S hS a)
    (hbr : Stacks.RepresentableMorphism.IsRepresentableMorphism 𝒵.val.val.p 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor b.hom))
    (hbqc : IsQuasiCompactMorphism B S hS b) (hbqs : AlgebraicStacks.IsQuasiSeparated B S hS b) :
    Nonempty ((quasicoherentDirectImage B S hS a).obj (𝟙_ _) ⊗
        (quasicoherentDirectImage B S hS b).obj (𝟙_ _) ≅
      (quasicoherentDirectImage B S hS
        ((twoFibreProductSquareAlgebraicStacks B S hS a b).fst ≫ a)).obj (𝟙_ _)) :=
  have := isIso_tensorPushforwardMap a b ha haqc haqs haf hbr hbqc hbqs
  ⟨asIso (tensorPushforwardMap a b)⟩

end Bijective

end AlgebraicGeometry.Stack.AlgebraicStacks
