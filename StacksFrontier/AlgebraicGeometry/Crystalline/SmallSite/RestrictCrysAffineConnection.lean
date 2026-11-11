module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalDeRhamDifferentials
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.RestrictFirstOrderThickening
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.RestrictQuasiCoherent

/-!
# The canonical connection of a crystal and of its restriction to an open pair

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF], opens `W ⊆ S` and
`V ⊆ X` with `V` mapping into `W`, a sheaf of `𝒪_{X/S}`-modules `F` on `Cris(X/S)`, its
restriction `F'` to `Cris(V/S|_W)` (`...SmallSite.smallExtendSheafRestriction`), and an object `B`
of `Cris(V/S|_W)` with affine ambient scheme lying over an affine open of `S|_W`; write `Bₓ` for
its extension to `Cris(X/S)`.  Then `F'(B) = F(Bₓ)`, the two section rings are both `Γ(T, 𝒪_T)`,
and `Ω_{X/S}(Bₓ) ≅ Ω_{V/S|_W}(B)` (`...SmallSite.smallExtendCrysDifferentialsObjIso`, `d b ↦ d b`).

This module proves that, under these identifications, **the ring-level canonical connection of
[Stacks, Tag 07J6] of `F` at `Bₓ` is that of `F'` at `B`, and so are all its extensions
`d(m ⊗ ω) = ∇ m ∧ ω + m ⊗ d ω` of [Stacks, Tag 07I0]**, including the de Rham differential of
`Ω^*` of [Stacks, Tag 07J4].

## The argument

Both connections are read back, injectively, to `p₁^* s - p₀^* s` on the first-order universal
thickenings (`...SmallSite.AffineConnection.readBack_ringConnection`).  The morphism
`...SmallSite.firstOrderThickeningCrysExtendHom` from the extension of the first-order thickening
of `B` to the first-order thickening of `Bₓ` commutes with `p₀` and `p₁`, and the read-back maps
are compatible with it (`readBack_smallExtendTensorMap`), which gives the connection.  The de
Rham differentials of `Ω^*` of the two situations are compared through their values on the
standard generators `b₀ d b₁ ∧ ⋯ ∧ d bᵢ`, which span over the global sections of `S`.  Neither the
choice of the affine opens of the bases over which the objects lie nor the choice of the de Rham
complexes matters.

## Main results

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `smallExtendTensorMap_ringConnection` — the connections agree.
* `smallExtendFormsMap_differential` — the de Rham differentials of `Ω^*` agree.
* `smallExtendTensorMap_extDiff` — **the extensions of the connections agree in every degree.**

## References

* [Stacks Project, Lemma 60.15.1, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07I0](https://stacks.math.columbia.edu/tag/07I0)
* [Stacks Project, Tag 07J4](https://stacks.math.columbia.edu/tag/07J4)
* [Stacks Project, Tag 07KL](https://stacks.math.columbia.edu/tag/07KL)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped AlgebraicGeometry TensorProduct
open Stacks.DeRham.DifferentialDescent

universe u


noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open AffineConnection

variable {S : GlobalCrystallineSituation.{u}} (W : S.S.scheme.Opens) (V : S.X.Opens)
  (hVW : V ≤ sourceToBase S ⁻¹ᵁ W) (F : SheafOfModules.{u} (structureSheaf S))
  (B : CrystallineThickening (restrict S W V hVW))

/-- The ambient scheme of the extension of an object of `Cris(V/S|_W)` is that of the object. -/
instance isAffine_smallExtend_target [h : IsAffine B.obj.thickening.target.scheme] :
    IsAffine ((smallExtend S W V hVW).obj B).obj.thickening.target.scheme := h

/-! ### The identifications of sections -/

/-- **The section ring of the extension `Aₓ` of an object `A` of `Cris(V/S|_W)` is that of `A`**,
both being `Γ(T, 𝒪_T)`; the identity, as a ring isomorphism between the two spellings. -/
def smallExtendRingEquiv (A : CrystallineThickening (restrict S W V hVW)) :
    GlobalCrystallineSituation.crysFormRing S ((smallExtend S W V hVW).obj A).obj ≃+*
      GlobalCrystallineSituation.crysFormRing (restrict S W V hVW) A.obj :=
  RingEquiv.refl _

/-- **The sections of `F'` over an object `A` of `Cris(V/S|_W)` are those of `F` over its
extension**; the identity, as an additive equivalence between the two spellings. -/
def smallExtendSectionsEquiv (A : CrystallineThickening (restrict S W V hVW)) :
    F.val.obj (op ((smallExtend S W V hVW).obj A)) ≃+
      (smallExtendSheafRestriction S W V hVW F).val.obj (op A) :=
  AddEquiv.refl _

/-- The identification of sections is semilinear over the identification of section rings. -/
theorem smallExtendSectionsEquiv_smul (A : CrystallineThickening (restrict S W V hVW))
    (c : GlobalCrystallineSituation.crysFormRing S ((smallExtend S W V hVW).obj A).obj)
    (m : F.val.obj (op ((smallExtend S W V hVW).obj A))) :
    smallExtendSectionsEquiv W V hVW F A (c • m) =
      smallExtendRingEquiv W V hVW A c • smallExtendSectionsEquiv W V hVW F A m := rfl

/-- **The comparison `Ω_{X/S}(Bₓ) ⟶ Ω_{V/S|_W}(B)`**, `d b ↦ d b`
(`...SmallSite.smallExtendCrysDifferentialsIso`), as a semilinear map over the identification
of section rings. -/
def smallExtendOmegaMap :
    ↥((GlobalCrystallineSituation.crysDifferentials S).obj
        (op ((smallExtend S W V hVW).obj B).obj)) →ₛₗ[(smallExtendRingEquiv W V hVW B).toRingHom]
      ↥((GlobalCrystallineSituation.crysDifferentials (restrict S W V hVW)).obj (op B.obj)) where
  toFun η := ((smallExtendCrysDifferentialsIso S W V hVW).hom.app (op B)).hom η
  map_add' := ((smallExtendCrysDifferentialsIso S W V hVW).hom.app (op B)).hom.map_add'
  map_smul' := ((smallExtendCrysDifferentialsIso S W V hVW).hom.app (op B)).hom.map_smul'

/-- The comparison of differentials carries `d b` to `d b`. -/
theorem smallExtendOmegaMap_crysD
    (b : GlobalCrystallineSituation.crysFormRing S ((smallExtend S W V hVW).obj B).obj) :
    smallExtendOmegaMap W V hVW B
        (GlobalCrystallineSituation.crysD S ((smallExtend S W V hVW).obj B).obj b) =
      GlobalCrystallineSituation.crysD (restrict S W V hVW) B.obj
        (smallExtendRingEquiv W V hVW B b) :=
  dpConstDifferentialsCongrHom_d _ _ _ _ _ (le_of_eq (crysBaseSections_extend S W V hVW B.obj))
    (crysBaseAppLE_mem_crysBaseSections_extend S W V hVW B) b

section TensorMap

variable {M N : Type u} [AddCommGroup M]
  [Module (GlobalCrystallineSituation.crysFormRing S ((smallExtend S W V hVW).obj B).obj) M]
  [AddCommGroup N] [Module (GlobalCrystallineSituation.crysFormRing (restrict S W V hVW) B.obj) N]
  (e : M →ₛₗ[(smallExtendRingEquiv W V hVW B).toRingHom] N)

/-- The bilinear datum of `smallExtendTensorMap`. -/
def smallExtendTensorMapAux :
    F.val.obj (op ((smallExtend S W V hVW).obj B)) →+
      (M →+ (smallExtendSheafRestriction S W V hVW F).val.obj (op B) ⊗[
        GlobalCrystallineSituation.crysFormRing (restrict S W V hVW) B.obj] N) :=
  AddMonoidHom.mk'
    (fun m ↦ (TensorProduct.mk (GlobalCrystallineSituation.crysFormRing (restrict S W V hVW) B.obj)
      _ N (smallExtendSectionsEquiv W V hVW F B m)).toAddMonoidHom.comp e.toAddMonoidHom)
    (fun m m' ↦ AddMonoidHom.ext fun x ↦ by
      change TensorProduct.tmul _ (smallExtendSectionsEquiv W V hVW F B (m + m')) (e x) =
        TensorProduct.tmul _ (smallExtendSectionsEquiv W V hVW F B m) (e x) +
          TensorProduct.tmul _ (smallExtendSectionsEquiv W V hVW F B m') (e x)
      rw [map_add, TensorProduct.add_tmul])

/-- **The comparison `F(Bₓ) ⊗ M ⟶ F'(B) ⊗ N` induced by a semilinear map `M ⟶ N`** over the
identification of section rings, `m ⊗ x ↦ m ⊗ e x`. -/
def smallExtendTensorMap :
    F.val.obj (op ((smallExtend S W V hVW).obj B)) ⊗[GlobalCrystallineSituation.crysFormRing S
        ((smallExtend S W V hVW).obj B).obj] M →+
      (smallExtendSheafRestriction S W V hVW F).val.obj (op B) ⊗[
        GlobalCrystallineSituation.crysFormRing (restrict S W V hVW) B.obj] N :=
  TensorProduct.liftAddHom (smallExtendTensorMapAux W V hVW F B e) fun c m x ↦ by
    change TensorProduct.tmul _ (smallExtendSectionsEquiv W V hVW F B (c • m)) (e x) =
      TensorProduct.tmul _ (smallExtendSectionsEquiv W V hVW F B m) (e (c • x))
    rw [smallExtendSectionsEquiv_smul, map_smulₛₗ, TensorProduct.smul_tmul]
    rfl

/-- The comparison `F(Bₓ) ⊗ M ⟶ F'(B) ⊗ N` on a pure tensor. -/
theorem smallExtendTensorMap_tmul (m : F.val.obj (op ((smallExtend S W V hVW).obj B))) (x : M) :
    smallExtendTensorMap W V hVW F B e
        (m ⊗ₜ[GlobalCrystallineSituation.crysFormRing S ((smallExtend S W V hVW).obj B).obj] x) =
      smallExtendSectionsEquiv W V hVW F B m ⊗ₜ[
        GlobalCrystallineSituation.crysFormRing (restrict S W V hVW) B.obj] e x :=
  TensorProduct.liftAddHom_tmul _ _ m x

end TensorMap

/-- `m ⊗ c d b ↦ m ⊗ c d b` under the comparison of `F ⊗ Ω`. -/
theorem smallExtendTensorMap_tmul_smul_crysD
    (m : F.val.obj (op ((smallExtend S W V hVW).obj B)))
    (c b : GlobalCrystallineSituation.crysFormRing S ((smallExtend S W V hVW).obj B).obj) :
    smallExtendTensorMap W V hVW F B (smallExtendOmegaMap W V hVW B)
        (m ⊗ₜ[GlobalCrystallineSituation.crysFormRing S ((smallExtend S W V hVW).obj B).obj]
          (c • GlobalCrystallineSituation.crysD S ((smallExtend S W V hVW).obj B).obj b)) =
      smallExtendSectionsEquiv W V hVW F B m ⊗ₜ[
        GlobalCrystallineSituation.crysFormRing (restrict S W V hVW) B.obj]
        (smallExtendRingEquiv W V hVW B c • GlobalCrystallineSituation.crysD (restrict S W V hVW)
          B.obj (smallExtendRingEquiv W V hVW B b)) := by
  rw [smallExtendTensorMap_tmul, map_smulₛₗ, smallExtendOmegaMap_crysD]
  rfl

/-! ### The connection -/

/-- The identification of sections carries the difference of the restrictions of `F` along the
extensions of two morphisms to the difference of the restrictions of `F'`. -/
theorem smallExtendSectionsEquiv_sub {C : CrystallineThickening (restrict S W V hVW)}
    (p₀ p₁ : C ⟶ B) (m : F.val.obj (op ((smallExtend S W V hVW).obj B))) :
    smallExtendSectionsEquiv W V hVW F C
        (crysSiteRestrict F ((smallExtend S W V hVW).map p₁) m -
          crysSiteRestrict F ((smallExtend S W V hVW).map p₀) m) =
      crysSiteRestrict (smallExtendSheafRestriction S W V hVW F) p₁
          (smallExtendSectionsEquiv W V hVW F B m) -
        crysSiteRestrict (smallExtendSheafRestriction S W V hVW F) p₀
          (smallExtendSectionsEquiv W V hVW F B m) := rfl

/-- **The value of the read-back maps on a generator, compared**: for morphisms `p₀, p₁` of
`Cris(V/S|_W)` and `q₀, q₁` of `Cris(X/S)` with `g ≫ qᵢ` the extension of `pᵢ`, the expression
`(p₀(c) (p₁(b) - p₀(b))) · p₀^* m` for `F'` is `g^*` of the one for `F` along `q₀, q₁`. -/
theorem smallExtendSectionsEquiv_readBack_aux {C : CrystallineThickening (restrict S W V hVW)}
    {D : CrystallineThickening S} (p₀ p₁ : C ⟶ B) (g : (smallExtend S W V hVW).obj C ⟶ D)
    (q₀ q₁ : D ⟶ (smallExtend S W V hVW).obj B)
    (h₀ : g ≫ q₀ = (smallExtend S W V hVW).map p₀) (h₁ : g ≫ q₁ = (smallExtend S W V hVW).map p₁)
    (c b : GlobalCrystallineSituation.crysFormRing S ((smallExtend S W V hVW).obj B).obj)
    (m : F.val.obj (op ((smallExtend S W V hVW).obj B))) :
    (crysSheafRingMap p₀.hom (smallExtendRingEquiv W V hVW B c) *
        (crysSheafRingMap p₁.hom (smallExtendRingEquiv W V hVW B b) -
          crysSheafRingMap p₀.hom (smallExtendRingEquiv W V hVW B b))) •
        crysSiteRestrict (smallExtendSheafRestriction S W V hVW F) p₀
          (smallExtendSectionsEquiv W V hVW F B m) =
      smallExtendSectionsEquiv W V hVW F C (crysSiteRestrict F g
        ((crysSheafRingMap q₀.hom c * (crysSheafRingMap q₁.hom b - crysSheafRingMap q₀.hom b)) •
          crysSiteRestrict F q₀ m)) := by
  have e₀ : ∀ x : GlobalCrystallineSituation.crysFormRing S ((smallExtend S W V hVW).obj B).obj,
      crysSheafRingMap g.hom (crysSheafRingMap q₀.hom x) =
        crysSheafRingMap ((smallExtend S W V hVW).map p₀).hom x := fun x ↦
    (crysSheafRingMap_comp g.hom q₀.hom x).trans
      (congrArg (fun k ↦ crysSheafRingMap k x) (congrArg (·.hom) h₀))
  have e₁ : ∀ x : GlobalCrystallineSituation.crysFormRing S ((smallExtend S W V hVW).obj B).obj,
      crysSheafRingMap g.hom (crysSheafRingMap q₁.hom x) =
        crysSheafRingMap ((smallExtend S W V hVW).map p₁).hom x := fun x ↦
    (crysSheafRingMap_comp g.hom q₁.hom x).trans
      (congrArg (fun k ↦ crysSheafRingMap k x) (congrArg (·.hom) h₁))
  have hm : crysSiteRestrict F g (crysSiteRestrict F q₀ m) =
      crysSiteRestrict F ((smallExtend S W V hVW).map p₀) m := by
    rw [crysSiteRestrict_comp, h₀]
  rw [crysSiteRestrict_smul, map_mul, map_sub, e₀, e₁, e₀, hm]
  rfl

section Connection

variable [IsAffine B.obj.thickening.target.scheme]
  {V' : (restrict S W V hVW).S.scheme.Opens}
  (hVB : (⊤ : B.obj.thickening.target.scheme.Opens) ≤ B.obj.toBase.hom ⁻¹ᵁ V')
  (hV' : IsAffineOpen V') {Vₓ : S.S.scheme.Opens}
  (hVBₓ : (⊤ : ((smallExtend S W V hVW).obj B).obj.thickening.target.scheme.Opens) ≤
    ((smallExtend S W V hVW).obj B).obj.toBase.hom ⁻¹ᵁ Vₓ)
  (hVₓ : IsAffineOpen Vₓ)

/-- **The read-back maps of `F` at `Bₓ` and of `F'` at `B` agree on `m ⊗ c d b`**, under the
comparison of the first-order thickenings. -/
theorem readBack_smallExtendTensorMap_tmul_smul_crysD
    (m : F.val.obj (op ((smallExtend S W V hVW).obj B)))
    (c b : GlobalCrystallineSituation.crysFormRing S ((smallExtend S W V hVW).obj B).obj) :
    readBack (smallExtendSheafRestriction S W V hVW F) hVB hV'
        (smallExtendTensorMap W V hVW F B (smallExtendOmegaMap W V hVW B)
          (m ⊗ₜ[GlobalCrystallineSituation.crysFormRing S ((smallExtend S W V hVW).obj B).obj]
            (c • GlobalCrystallineSituation.crysD S ((smallExtend S W V hVW).obj B).obj b))) =
      smallExtendSectionsEquiv W V hVW F (firstOrderThickeningCrysObject (restrict S W V hVW) B)
        (crysSiteRestrict F (firstOrderThickeningCrysExtendHom S W V hVW B)
          (readBack F hVBₓ hVₓ
            (m ⊗ₜ[GlobalCrystallineSituation.crysFormRing S ((smallExtend S W V hVW).obj B).obj]
              (c • GlobalCrystallineSituation.crysD S ((smallExtend S W V hVW).obj B).obj b)))) :=
  (congrArg (readBack (smallExtendSheafRestriction S W V hVW F) hVB hV')
      (smallExtendTensorMap_tmul_smul_crysD W V hVW F B m c b)).trans
    ((readBack_tmul_smul_crysD hVB hV' (smallExtendSectionsEquiv W V hVW F B m)
        (smallExtendRingEquiv W V hVW B c) (smallExtendRingEquiv W V hVW B b)).trans
      ((smallExtendSectionsEquiv_readBack_aux W V hVW F B
        (firstOrderThickeningCrysP₀ (restrict S W V hVW) B)
        (firstOrderThickeningCrysP₁ (restrict S W V hVW) B)
        (firstOrderThickeningCrysExtendHom S W V hVW B)
        (firstOrderThickeningCrysP₀ S ((smallExtend S W V hVW).obj B))
        (firstOrderThickeningCrysP₁ S ((smallExtend S W V hVW).obj B))
        (firstOrderThickeningCrysExtendHom_comp_P₀ S W V hVW B)
        (firstOrderThickeningCrysExtendHom_comp_P₁ S W V hVW B) c b m).trans
        (congrArg (fun x ↦ smallExtendSectionsEquiv W V hVW F
            (firstOrderThickeningCrysObject (restrict S W V hVW) B)
          (crysSiteRestrict F (firstOrderThickeningCrysExtendHom S W V hVW B) x))
          (readBack_tmul_smul_crysD hVBₓ hVₓ m c b).symm)))

/-- **The read-back maps of `F` at `Bₓ` and of `F'` at `B` are compatible** with the comparison of
the first-order thickenings: both are `m ⊗ c d b ↦ (p₀(c) (p₁(b) - p₀(b))) · p₀^* m`. -/
theorem readBack_smallExtendTensorMap
    (z : F.val.obj (op ((smallExtend S W V hVW).obj B)) ⊗[GlobalCrystallineSituation.crysFormRing
        S ((smallExtend S W V hVW).obj B).obj]
      ↥((GlobalCrystallineSituation.crysDifferentials S).obj
        (op ((smallExtend S W V hVW).obj B).obj))) :
    readBack (smallExtendSheafRestriction S W V hVW F) hVB hV'
        (smallExtendTensorMap W V hVW F B (smallExtendOmegaMap W V hVW B) z) =
      smallExtendSectionsEquiv W V hVW F (firstOrderThickeningCrysObject (restrict S W V hVW) B)
        (crysSiteRestrict F (firstOrderThickeningCrysExtendHom S W V hVW B)
          (readBack F hVBₓ hVₓ z)) := by
  let L := (readBack (smallExtendSheafRestriction S W V hVW F) hVB hV').comp
    (smallExtendTensorMap W V hVW F B (smallExtendOmegaMap W V hVW B))
  let R := ((smallExtendSectionsEquiv W V hVW F
      (firstOrderThickeningCrysObject (restrict S W V hVW) B)).toAddMonoidHom.comp
    (F.val.map (firstOrderThickeningCrysExtendHom S W V hVW B).op).hom.toAddMonoidHom).comp
      (readBack F hVBₓ hVₓ)
  change L z = R z
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero L).trans (map_zero R).symm
  | add x y hx hy =>
      exact ((map_add L x y).trans (congrArg₂ (· + ·) hx hy)).trans (map_add R x y).symm
  | tmul m η =>
      have key : ∀ η ∈ Submodule.span (GlobalCrystallineSituation.crysFormRing S
          ((smallExtend S W V hVW).obj B).obj)
          (Set.range (GlobalCrystallineSituation.crysD S ((smallExtend S W V hVW).obj B).obj)),
          ∀ c : GlobalCrystallineSituation.crysFormRing S ((smallExtend S W V hVW).obj B).obj,
            L (m ⊗ₜ[GlobalCrystallineSituation.crysFormRing S ((smallExtend S W V hVW).obj B).obj]
              (c • η)) =
            R (m ⊗ₜ[GlobalCrystallineSituation.crysFormRing S ((smallExtend S W V hVW).obj B).obj]
              (c • η)) := by
        intro η hη
        induction hη using Submodule.span_induction with
        | mem z hz =>
            obtain ⟨b, rfl⟩ := hz
            intro c
            exact readBack_smallExtendTensorMap_tmul_smul_crysD W V hVW F B hVB hV' hVBₓ hVₓ
              m c b
        | zero =>
            intro c
            rw [smul_zero, TensorProduct.tmul_zero]
            exact (map_zero L).trans (map_zero R).symm
        | add x y _ _ hx hy =>
            intro c
            rw [smul_add, TensorProduct.tmul_add]
            exact ((map_add L _ _).trans (congrArg₂ (· + ·) (hx c) (hy c))).trans
              (map_add R _ _).symm
        | smul a x _ hx =>
            intro c
            rw [smul_smul]
            exact hx (c * a)
      have h := key η (by rw [crysD_span]; exact Submodule.mem_top) 1
      rwa [one_smul] at h

/-- **The canonical connection of [Stacks, Tag 07J6] of `F` at `Bₓ` is that of its restriction
`F'` at `B`**: both are read back to `p₁^* s - p₀^* s`, and the comparison of first-order
thickenings commutes with `p₀` and `p₁`. -/
theorem smallExtendTensorMap_ringConnection
    (he : Function.Bijective (crysExtensionSectionsMap F ((smallExtend S W V hVW).obj B)))
    (he' : Function.Bijective
      (crysExtensionSectionsMap (smallExtendSheafRestriction S W V hVW F) B))
    (m : F.val.obj (op ((smallExtend S W V hVW).obj B))) :
    smallExtendTensorMap W V hVW F B (smallExtendOmegaMap W V hVW B)
        (ringConnection (B := (smallExtend S W V hVW).obj B) hVBₓ hVₓ he m) =
      ringConnection hVB hV' he' (smallExtendSectionsEquiv W V hVW F B m) := by
  refine injective_readBack hVB hV' he' ?_
  refine (readBack_smallExtendTensorMap W V hVW F B hVB hV' hVBₓ hVₓ _).trans ?_
  refine (congrArg (fun x ↦ smallExtendSectionsEquiv W V hVW F
    (firstOrderThickeningCrysObject (restrict S W V hVW) B)
    (crysSiteRestrict F (firstOrderThickeningCrysExtendHom S W V hVW B) x))
    (readBack_ringConnection (B := (smallExtend S W V hVW).obj B) hVBₓ hVₓ he m)).trans ?_
  refine (congrArg (smallExtendSectionsEquiv W V hVW F
      (firstOrderThickeningCrysObject (restrict S W V hVW) B))
    (restrict_connectionDifference F _ _ _ _
      (firstOrderThickeningCrysExtendHom_comp_P₀ S W V hVW B)
      (firstOrderThickeningCrysExtendHom_comp_P₁ S W V hVW B) m)).trans ?_
  refine (smallExtendSectionsEquiv_sub W V hVW F B _ _ m).trans ?_
  exact ((connectionDifference_apply (smallExtendSheafRestriction S W V hVW F) B
    (smallExtendSectionsEquiv W V hVW F B m)).symm).trans
    (readBack_ringConnection hVB hV' he' (smallExtendSectionsEquiv W V hVW F B m)).symm

end Connection

/-! ### The forms -/

/-- **The comparison `Ω^i_{X/S}(Bₓ) ⟶ Ω^i_{V/S|_W}(B)`**, the `i`-th exterior power of the
comparison of differentials. -/
def smallExtendFormsMap (i : ℕ) :
    ⋀[GlobalCrystallineSituation.crysFormRing S ((smallExtend S W V hVW).obj B).obj]^i
        ↥((GlobalCrystallineSituation.crysDifferentials S).obj
          (op ((smallExtend S W V hVW).obj B).obj)) →ₛₗ[(smallExtendRingEquiv W V hVW B).toRingHom]
      ⋀[GlobalCrystallineSituation.crysFormRing (restrict S W V hVW) B.obj]^i
        ↥((GlobalCrystallineSituation.crysDifferentials (restrict S W V hVW)).obj (op B.obj)) :=
  ExteriorAlgebra.powMapₛₗ i _ (smallExtendOmegaMap W V hVW B)

/-- The comparison of forms carries a wedge to the wedge of the images. -/
theorem smallExtendFormsMap_ιMulti (i : ℕ)
    (v : Fin i → ↥((GlobalCrystallineSituation.crysDifferentials S).obj
      (op ((smallExtend S W V hVW).obj B).obj))) :
    smallExtendFormsMap W V hVW B i (exteriorPower.ιMulti _ i v) =
      exteriorPower.ιMulti _ i (fun j ↦ smallExtendOmegaMap W V hVW B (v j)) :=
  ExteriorAlgebra.powMapₛₗ_ιMulti i _ _ v

/-- The comparison of forms is multiplicative: it carries `η ∧ ω` to the wedge of the images. -/
theorem smallExtendFormsMap_leftWedge (i : ℕ)
    (η : ↥((GlobalCrystallineSituation.crysDifferentials S).obj
      (op ((smallExtend S W V hVW).obj B).obj)))
    (ω : ⋀[GlobalCrystallineSituation.crysFormRing S ((smallExtend S W V hVW).obj B).obj]^i
        ↥((GlobalCrystallineSituation.crysDifferentials S).obj
          (op ((smallExtend S W V hVW).obj B).obj))) :
    smallExtendFormsMap W V hVW B (i + 1) (leftWedge i η ω) =
      leftWedge i (smallExtendOmegaMap W V hVW B η) (smallExtendFormsMap W V hVW B i ω) := by
  refine Subtype.ext ?_
  change ExteriorAlgebra.mapₛₗ _ _ (ExteriorAlgebra.ι _ η * ω.1) =
    ExteriorAlgebra.ι _ (smallExtendOmegaMap W V hVW B η) * ExteriorAlgebra.mapₛₗ _ _ ω.1
  rw [map_mul, ExteriorAlgebra.mapₛₗ_ι]

/-- A section of `S` read over `Bₓ` is its restriction to `W` read over `B`. -/
theorem smallExtendRingEquiv_crysBase (a : Γ(S.S.scheme, ⊤)) :
    smallExtendRingEquiv W V hVW B
        (GlobalCrystallineSituation.crysBase S ((smallExtend S W V hVW).obj B).obj a) =
      GlobalCrystallineSituation.crysBase (restrict S W V hVW) B.obj
        ((restrictSι S W V hVW).hom.appTop a) := by
  change (B.obj.toBase.hom ≫ (restrictSι S W V hVW).hom).appLE ⊤ ⊤
      (le_preimage_top (B.obj.toBase.hom ≫ (restrictSι S W V hVW).hom) ⊤) a =
    B.obj.toBase.hom.appLE ⊤ ⊤ (le_preimage_top B.obj.toBase.hom ⊤)
      ((restrictSι S W V hVW).hom.appTop a)
  rw [appLE_top_top, appLE_top_top, Scheme.Hom.comp_appTop]
  rfl

/-- **The de Rham differentials of `Ω^*` of the two situations agree** under the comparison of
forms: both sides are additive, linear over the global sections of `S`, and agree on the standard
generators `b₀ d b₁ ∧ ⋯ ∧ d bᵢ`, which span. -/
theorem smallExtendFormsMap_differential (i : ℕ)
    (ω : ⋀[GlobalCrystallineSituation.crysFormRing S ((smallExtend S W V hVW).obj B).obj]^i
        ↥((GlobalCrystallineSituation.crysDifferentials S).obj
          (op ((smallExtend S W V hVW).obj B).obj))) :
    smallExtendFormsMap W V hVW B (i + 1)
        ((crysDeRhamComplex S).differential i ((smallExtend S W V hVW).obj B).obj ω) =
      (crysDeRhamComplex (restrict S W V hVW)).differential i B.obj
        (smallExtendFormsMap W V hVW B i ω) := by
  have hω : ω ∈ Submodule.span ↥Γ(S.S.scheme, ⊤)
      (Set.range (crysGen S ((smallExtend S W V hVW).obj B).obj i)) := by
    rw [crysGen_span]
    exact Submodule.mem_top
  let L := (smallExtendFormsMap W V hVW B (i + 1)).toAddMonoidHom.comp
    ((crysDeRhamComplex S).differential i ((smallExtend S W V hVW).obj B).obj)
  let R := ((crysDeRhamComplex (restrict S W V hVW)).differential i B.obj).comp
    (smallExtendFormsMap W V hVW B i).toAddMonoidHom
  change L ω = R ω
  induction hω using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      change smallExtendFormsMap W V hVW B (i + 1)
          ((crysDeRhamComplex S).differential i ((smallExtend S W V hVW).obj B).obj
            (crysGen S ((smallExtend S W V hVW).obj B).obj i b)) =
        (crysDeRhamComplex (restrict S W V hVW)).differential i B.obj
          (smallExtendFormsMap W V hVW B i (crysGen S ((smallExtend S W V hVW).obj B).obj i b))
      rw [(crysDeRhamComplex S).differential_generator, smallExtendFormsMap_ιMulti, crysGen,
        map_smulₛₗ, smallExtendFormsMap_ιMulti]
      simp only [smallExtendOmegaMap_crysD]
      exact ((crysDeRhamComplex (restrict S W V hVW)).differential_generator i B.obj
        (fun j ↦ smallExtendRingEquiv W V hVW B (b j))).symm
  | zero => exact (map_zero L).trans (map_zero R).symm
  | add x y _ _ hx hy =>
      exact ((map_add L x y).trans (congrArg₂ (· + ·) hx hy)).trans (map_add R x y).symm
  | smul a x _ hx =>
      have hx' : smallExtendFormsMap W V hVW B (i + 1)
          ((crysDeRhamComplex S).differential i ((smallExtend S W V hVW).obj B).obj x) =
        (crysDeRhamComplex (restrict S W V hVW)).differential i B.obj
          (smallExtendFormsMap W V hVW B i x) := hx
      have hc : (a • x : ⋀[GlobalCrystallineSituation.crysFormRing S
          ((smallExtend S W V hVW).obj B).obj]^i
            ↥((GlobalCrystallineSituation.crysDifferentials S).obj
              (op ((smallExtend S W V hVW).obj B).obj))) =
          GlobalCrystallineSituation.crysBase S ((smallExtend S W V hVW).obj B).obj a • x :=
        (algebraMap_smul (GlobalCrystallineSituation.crysFormRing S
          ((smallExtend S W V hVW).obj B).obj) a x).symm
      change smallExtendFormsMap W V hVW B (i + 1)
          ((crysDeRhamComplex S).differential i ((smallExtend S W V hVW).obj B).obj (a • x)) =
        (crysDeRhamComplex (restrict S W V hVW)).differential i B.obj
          (smallExtendFormsMap W V hVW B i (a • x))
      rw [hc, (crysDeRhamComplex S).differential_base_smul, map_smulₛₗ, map_smulₛₗ, hx']
      change smallExtendRingEquiv W V hVW B
          (GlobalCrystallineSituation.crysBase S ((smallExtend S W V hVW).obj B).obj a) • _ =
        (crysDeRhamComplex (restrict S W V hVW)).differential i B.obj
          (smallExtendRingEquiv W V hVW B
            (GlobalCrystallineSituation.crysBase S ((smallExtend S W V hVW).obj B).obj a) • _)
      rw [smallExtendRingEquiv_crysBase]
      exact ((crysDeRhamComplex (restrict S W V hVW)).differential_base_smul i B.obj _ _).symm

/-- The comparisons of `F ⊗ Ω` and of `F ⊗ Ω^*` are compatible with the left exterior
multiplication by a form. -/
theorem smallExtendTensorMap_map_leftWedge (i : ℕ)
    (ω : ⋀[GlobalCrystallineSituation.crysFormRing S ((smallExtend S W V hVW).obj B).obj]^i
        ↥((GlobalCrystallineSituation.crysDifferentials S).obj
          (op ((smallExtend S W V hVW).obj B).obj)))
    (z : F.val.obj (op ((smallExtend S W V hVW).obj B)) ⊗[GlobalCrystallineSituation.crysFormRing
        S ((smallExtend S W V hVW).obj B).obj]
      ↥((GlobalCrystallineSituation.crysDifferentials S).obj
        (op ((smallExtend S W V hVW).obj B).obj))) :
    smallExtendTensorMap W V hVW F B (smallExtendFormsMap W V hVW B (i + 1))
        (TensorProduct.map LinearMap.id ((leftWedge i).flip ω) z) =
      TensorProduct.map LinearMap.id ((leftWedge i).flip (smallExtendFormsMap W V hVW B i ω))
        (smallExtendTensorMap W V hVW F B (smallExtendOmegaMap W V hVW B) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul m η =>
      simp only [TensorProduct.map_tmul, smallExtendTensorMap_tmul, LinearMap.id_apply,
        LinearMap.flip_apply, smallExtendFormsMap_leftWedge]

section Extension

variable [IsAffine B.obj.thickening.target.scheme]
  {V' : (restrict S W V hVW).S.scheme.Opens}
  (hVB : (⊤ : B.obj.thickening.target.scheme.Opens) ≤ B.obj.toBase.hom ⁻¹ᵁ V')
  (hV' : IsAffineOpen V') {Vₓ : S.S.scheme.Opens}
  (hVBₓ : (⊤ : ((smallExtend S W V hVW).obj B).obj.thickening.target.scheme.Opens) ≤
    ((smallExtend S W V hVW).obj B).obj.toBase.hom ⁻¹ᵁ Vₓ)
  (hVₓ : IsAffineOpen Vₓ)
  (he : Function.Bijective (crysExtensionSectionsMap F ((smallExtend S W V hVW).obj B)))
  (he' : Function.Bijective
    (crysExtensionSectionsMap (smallExtendSheafRestriction S W V hVW F) B))

/-- **The extensions `d(m ⊗ ω) = ∇ m ∧ ω + m ⊗ d ω` of the canonical connections of `F` at `Bₓ`
and of `F'` at `B` agree in every degree** under the comparison of `F ⊗ Ω^*`. -/
theorem smallExtendTensorMap_extDiff (i : ℕ)
    (x : F.val.obj (op ((smallExtend S W V hVW).obj B)) ⊗[GlobalCrystallineSituation.crysFormRing
        S ((smallExtend S W V hVW).obj B).obj]
        ⋀[GlobalCrystallineSituation.crysFormRing S ((smallExtend S W V hVW).obj B).obj]^i
          ↥((GlobalCrystallineSituation.crysDifferentials S).obj
            (op ((smallExtend S W V hVW).obj B).obj))) :
    smallExtendTensorMap W V hVW F B (smallExtendFormsMap W V hVW B (i + 1))
        (extDiff (B := (smallExtend S W V hVW).obj B) hVBₓ hVₓ he i x) =
      extDiff hVB hV' he' i
        (smallExtendTensorMap W V hVW F B (smallExtendFormsMap W V hVW B i) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul m ω =>
      refine (congrArg (smallExtendTensorMap W V hVW F B (smallExtendFormsMap W V hVW B (i + 1)))
        (extDiff_tmul (B := (smallExtend S W V hVW).obj B) hVBₓ hVₓ he i m ω)).trans ?_
      refine (map_add _ _ _).trans ?_
      refine (congrArg₂ (· + ·) (smallExtendTensorMap_map_leftWedge W V hVW F B i ω _)
        (smallExtendTensorMap_tmul W V hVW F B _ m _)).trans ?_
      refine (congrArg₂ (· + ·)
        (congrArg (TensorProduct.map LinearMap.id
            ((leftWedge i).flip (smallExtendFormsMap W V hVW B i ω)))
          (smallExtendTensorMap_ringConnection W V hVW F B hVB hV' hVBₓ hVₓ he he' m))
        (congrArg (TensorProduct.tmul _ (smallExtendSectionsEquiv W V hVW F B m))
          (smallExtendFormsMap_differential W V hVW B i ω))).trans ?_
      refine (extDiff_tmul hVB hV' he' i (smallExtendSectionsEquiv W V hVW F B m)
        (smallExtendFormsMap W V hVW B i ω)).symm.trans ?_
      exact congrArg (extDiff hVB hV' he' i) (smallExtendTensorMap_tmul W V hVW F B _ m ω).symm

end Extension

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
