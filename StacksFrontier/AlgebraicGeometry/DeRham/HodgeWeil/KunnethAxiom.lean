module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.KunnethCechCup
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.KunnethCechPullback
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.KunnethCechChain
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.KunnethReduction
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilThreeAxioms

/-!
# The Künneth formula for Hodge cohomology, and axiom (A5)

Let `k` be a field and `X`, `Y` quasi-compact schemes over `k` with affine diagonal, and let
`W = X ×_k Y` with projections `pr₁`, `pr₂`. In every bidegree `(r, s)` the Künneth map

`⨁_{a + c = r, b + d = s} H^b(X, Ω^a_{X/k}) ⊗_k H^d(Y, Ω^c_{Y/k}) ⟶ H^s(W, Ω^r_{W/k})`,
`ξ ⊗ ζ ↦ pr₁^*ξ ∪ pr₂^*ζ`,

is bijective. Choose finite affine open coverings `𝒰` of `X` and `𝒱` of `Y`; the opens
`pr₁⁻¹U_i ∩ pr₂⁻¹V_j` cover `W`, and all finite intersections of the three coverings are affine.
For Čech cocycles `γ` of `Ω^a_{X/k}` on `𝒰` in degree `b` and `ε` of `Ω^c_{Y/k}` on `𝒱` in
degree `d`:

* the pullback `pr₁^*[γ]` is the class of the pulled back cocycle on `pr₁⁻¹𝒰` ([Stacks, Tag 0FM4]),
  which is the class of its refinement to `𝒰 × 𝒱` ([Stacks, Tag 01FD]); likewise for `pr₂^*[ε]`;
* the cup product of these two classes is `(-1)^{b c}` times the class of the Alexander–Whitney
  wedge product of the two refined cocycles ([Stacks, Tag 0FKV]);
* that wedge product is the Čech cocycle `σ ↦ (pr₁^*γ_{σ₀ … σ_b})| ∧ (pr₂^*ε_{σ_b … σ_{b + d}})|`
  whose class the Čech Künneth map `Stacks.HodgeWeil.hodgeCechKunnethMap` assigns to `[γ] ⊗ [ε]`.

So the Künneth map, composed with the class maps of `𝒰` and `𝒱` (bijective, [Stacks, Tag 01XD]),
is the Čech Künneth map composed with the sign `(-1)^{b c}` on each summand. The Čech Künneth map
is bijective, hence so is the Künneth map. For smooth projective `X` and `Y` this gives the
Künneth formula for every fibre product of `X` and `Y` over `k`, and with
`H^*_{Hodge}(Spec(k)/k) = k` it is axiom (A5) of Section 0FID for Hodge cohomology, as asserted
in [Stacks, Remark 0FWE].

## Main results

* `Stacks.HodgeWeil.hodgeSchemeKunnethMap_lof_hodgeCechMap`: on the classes of two Čech cocycles
  the Künneth map is `(-1)^{b c}` times the Čech Künneth map.
* `Stacks.HodgeWeil.bijective_hodgeSchemeKunnethMap_pullback`: **the Hodge Künneth formula** for
  `X ×_k Y`, in every bidegree.
* `Stacks.HodgeWeil.bijective_hodgeKunnethBidegreeMap`: the Künneth formula in every bidegree for
  every fibre product of smooth projective schemes over `k`.
* `Stacks.HodgeWeil.bijective_hodgeKunnethMap`: the Künneth map
  `H^*_{Hodge}(X/k) ⊗_k H^*_{Hodge}(Y/k) ⟶ H^*_{Hodge}(P/k)` is bijective.
* `Stacks.HodgeWeil.hodge_kunnethAxiom`: **axiom (A5) for Hodge cohomology.**

## Implementation notes

The Hodge cup product carries the Koszul sign `(-1)^{b c}` of the bidegrees `(a, b)` and
`(c, d)`, while the Čech Künneth map is built from the Alexander–Whitney product without sign.
The comparison is therefore stated with the automorphism `Stacks.HodgeWeil.hodgeKunnethSign`
of the source, multiplication by `(-1)^{b c}` on each summand, which is its own inverse.

## References

* [Stacks Project, Remark 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
* [Stacks Project, Section 0FID](https://stacks.math.columbia.edu/tag/0FID)
* [Stacks Project, Tag 0FKV](https://stacks.math.columbia.edu/tag/0FKV)
* [Stacks Project, Tag 0FM4](https://stacks.math.columbia.edu/tag/0FM4)
* [Stacks Project, Tag 01FD](https://stacks.math.columbia.edu/tag/01FD)
* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme
open scoped TensorProduct
open AlgebraicGeometry.SheafOfModules (hodgeCohomologyComponent deRhamTerm hodgeCohomologyCup
  reindexHodgeDeg)
open Stacks.Cohomology.CechSheaf (abSections)
open Stacks.CechKunneth (Cochain H Hmk prodCover boxOpen FiniteAffineCover finiteAffineCover
  refCochain)

universe u

namespace Stacks.HodgeWeil

attribute [local instance] HasDerivedCategory.standard

section Signs

/-- **Multiplying each summand of a direct sum by a sign is bijective**: for units `u i` of `ℤ`,
the map `⨁ᵢ Mᵢ ⟶ ⨁ᵢ Mᵢ` which is multiplication by `u i` on `Mᵢ` is its own inverse. -/
theorem bijective_lmap_zsmul_units {R ι : Type*} [Semiring R] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (u : ι → ℤˣ) :
    Function.Bijective (DirectSum.lmap fun i => ((u i : ℤ) • LinearMap.id : M i →ₗ[R] M i)) := by
  have h : ∀ i, Function.Involutive ((u i : ℤ) • LinearMap.id : M i →ₗ[R] M i) := fun i v => by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.id_apply, LinearMap.id_apply,
      smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]
  exact ⟨(DirectSum.lmap_injective _).2 fun i => (h i).injective,
    (DirectSum.lmap_surjective _).2 fun i => (h i).surjective⟩

end Signs

section Restriction

variable {X' X S S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
  (w : g' ≫ f = f' ≫ g) {I J : Type u} (U : I → X.Opens) (V : J → X'.Opens) (r : J → I)
  (hr : ∀ j, V j ≤ g' ⁻¹ᵁ U (r j)) {k : Type u} [CommRing k] (φ : k →+* hodgeBaseRing f')

/-- **A pulled back and refined Čech cochain of differential forms, restricted to an open, is
the restriction of the pulled back form**: for a commutative square `g' ≫ f = f' ≫ g`, a Čech
cochain `c` of `Ω^n_{X/S}` on `𝒰` and a refinement `r` of `g'⁻¹𝒰` by `𝒱`, the value of the
refinement of `pullbackCochain c` on `t`, restricted to `W`, is `(g'^* c_{r ∘ t})|_W`. -/
theorem basisRes_refCochain_pullbackCochain (n : ℕ) {m : ℕ}
    (c : CechCochains.Cochain U (abSections (deRhamTerm (formsAlgebras f) n)) m)
    (t : Fin (m + 1) → J) {W : X'.Opens} (h : W ≤ CechCochains.inter V t)
    (h' : W ≤ g' ⁻¹ᵁ CechCochains.inter U (r ∘ t)) :
    Stacks.Cohomology.Basis.res (abSections (deRhamTerm (formsAlgebras f') n)) h
        (refCochain (hodgeSectionsK f' φ n) (fun i => g' ⁻¹ᵁ U i) V r hr m
          (pullbackCochain g' f' f g w U n c) t) =
      (Scheme.Hom.relativeDifferentialForms f' (n : ℤ)).presheaf.map (homOfLE h').op
        (Scheme.Hom.relativeDifferentialFormsPullback g' f f' g w (n : ℤ)
          (CechCochains.inter U (r ∘ t)) (c (r ∘ t))) := by
  change CechCochains.restr (abSections (deRhamTerm (formsAlgebras f') n)) h
      (CechCochains.restr (abSections (deRhamTerm (formsAlgebras f') n))
        (Stacks.CechKunneth.inter_le_inter_refine (fun i => g' ⁻¹ᵁ U i) V r hr t)
        (CechCochains.restr (abSections (deRhamTerm (formsAlgebras f') n))
          (cechInter_map_le g'.base U (r ∘ t))
          (Scheme.Hom.relativeDifferentialFormsPullback g' f f' g w (n : ℤ)
            (CechCochains.inter U (r ∘ t)) (c (r ∘ t))))) =
    CechCochains.restr (abSections (deRhamTerm (formsAlgebras f') n)) h'
      (Scheme.Hom.relativeDifferentialFormsPullback g' f f' g w (n : ℤ)
        (CechCochains.inter U (r ∘ t)) (c (r ∘ t)))
  exact (congrArg _ (CechCochains.restr_restr _ _ _ _)).trans (CechCochains.restr_restr _ _ _ _)

end Restriction

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))

section Cochain

variable {I J : Type u} (U : I → X.Opens) (V : J → Y.Opens)

/-- **The wedge product of the pulled back cocycles is the Künneth cochain**: refining the
pullbacks of `γ` along `pr₁` and of `ε` along `pr₂` to the covering `U × V` of `X ×_k Y`, their
Alexander–Whitney wedge product is `Stacks.HodgeWeil.hodgeKunnethCochain`, the cochain
`σ ↦ (pr₁^*γ_{σ₀ … σ_b})| ∧ (pr₂^*ε_{σ_b … σ_{b + d}})|`. -/
theorem wedgeCup_refCochain_pullbackCochain {a b c d : ℕ}
    (γ : Cochain (hodgeSectionsK f (hodgeScalarsOverField f) a) U b)
    (ε : Cochain (hodgeSectionsK g (hodgeScalarsOverField g) c) V d) :
    wedgeCup (formsAlgebras (pullback.fst f g ≫ f)) ((boxOpen f g).obj ∘ prodCover U V)
        (refCochain (hodgeSectionsK (pullback.fst f g ≫ f)
            (hodgeScalarsOverField (pullback.fst f g ≫ f)) a)
          (fun i => pullback.fst f g ⁻¹ᵁ U i) ((boxOpen f g).obj ∘ prodCover U V) Prod.fst
          (fun _ => Stacks.CechKunneth.boxOpen_le_fst f g _) b
          (pullbackCochain (pullback.fst f g) (pullback.fst f g ≫ f) f (𝟙 _)
            (Category.comp_id _).symm U a γ))
        (refCochain (hodgeSectionsK (pullback.fst f g ≫ f)
            (hodgeScalarsOverField (pullback.fst f g ≫ f)) c)
          (fun j => pullback.snd f g ⁻¹ᵁ V j) ((boxOpen f g).obj ∘ prodCover U V) Prod.snd
          (fun _ => Stacks.CechKunneth.boxOpen_le_snd f g _) d
          (pullbackCochain (pullback.snd f g) (pullback.fst f g ≫ f) g (𝟙 _)
            (hodgeSchemeSquare_snd pullback.condition) V c ε)) =
      hodgeKunnethCochain f g U V γ ε := by
  funext σ
  dsimp only [wedgeCup, Stacks.Cech.Hypercohomology.cechAWCochain, hodgeKunnethCochain_apply]
  rw [basisRes_refCochain_pullbackCochain (pullback.fst f g) (pullback.fst f g ≫ f) f (𝟙 _)
      (Category.comp_id _).symm U ((boxOpen f g).obj ∘ prodCover U V) Prod.fst
      (fun ij => Stacks.CechKunneth.boxOpen_le_fst f g _)
      (hodgeScalarsOverField (pullback.fst f g ≫ f)) a γ
      (σ ∘ Stacks.Cech.LinearCupProduct.frontIdx b (b + d) (Nat.le_add_right b d))
      (W := CechCochains.inter ((boxOpen f g).obj ∘ prodCover U V) σ)
      (Stacks.Cech.Hypercohomology.cechInter_le_reindex _ σ _)
      ((Stacks.CechKunneth.boxOpen_inter_prodCover f g U V σ).ge.trans
        ((Stacks.CechKunneth.boxOpen_le_fst f g _).trans (Scheme.Hom.preimage_mono _
          (Stacks.CechKunneth.fst_inter_prodCover_le U V σ
            (Stacks.Cech.LinearCupProduct.frontIdx b (b + d) (Nat.le_add_right b d)))))),
    basisRes_refCochain_pullbackCochain (pullback.snd f g) (pullback.fst f g ≫ f) g (𝟙 _)
      (hodgeSchemeSquare_snd pullback.condition) V ((boxOpen f g).obj ∘ prodCover U V) Prod.snd
      (fun ij => Stacks.CechKunneth.boxOpen_le_snd f g _)
      (hodgeScalarsOverField (pullback.fst f g ≫ f)) c ε
      (σ ∘ Stacks.Cech.LinearCupProduct.backIdx b d (b + d) le_rfl)
      (W := CechCochains.inter ((boxOpen f g).obj ∘ prodCover U V) σ)
      (Stacks.Cech.Hypercohomology.cechInter_le_reindex _ σ _)
      ((Stacks.CechKunneth.boxOpen_inter_prodCover f g U V σ).ge.trans
        ((Stacks.CechKunneth.boxOpen_le_snd f g _).trans (Scheme.Hom.preimage_mono _
          (Stacks.CechKunneth.snd_inter_prodCover_le U V σ
            (Stacks.Cech.LinearCupProduct.backIdx b d (b + d) le_rfl)))))]
  rfl

end Cochain

section Classes

variable (CX : FiniteAffineCover X) (CY : FiniteAffineCover Y)

/-- **The Künneth map on the classes of two Čech cocycles** ([Stacks, Remark 0FWE]): for Čech
cocycles `γ` of `Ω^a_{X/k}` on `𝒰` in degree `b` and `ε` of `Ω^c_{Y/k}` on `𝒱` in degree `d`,
the Künneth map carries `[γ] ⊗ [ε]` to `(-1)^{b c}` times the image of `[γ] ⊗ [ε]` under the
Čech Künneth map `Stacks.HodgeWeil.hodgeCechKunnethMap`. -/
theorem hodgeSchemeKunnethMap_lof_hodgeCechMap {a b c d : ℕ}
    (γ : Cochain (hodgeSectionsK f (hodgeScalarsOverField f) a) CX.U b)
    (hγ : Stacks.CechKunneth.d _ CX.U b γ = 0)
    (ε : Cochain (hodgeSectionsK g (hodgeScalarsOverField g) c) CY.U d)
    (hε : Stacks.CechKunneth.d _ CY.U d ε = 0) :
    hodgeSchemeKunnethMap f g (pullback.fst f g) (pullback.snd f g) pullback.condition
        (hodgeBidegreeAdd ((a, b), (c, d)))
        (DirectSum.lof k
          {x : (ℕ × ℕ) × (ℕ × ℕ) // hodgeBidegreeAdd x = hodgeBidegreeAdd ((a, b), (c, d))}
          (fun x => hodgeCohomologyComponent (formsAlgebras f) x.1.1.1 (x.1.1.2 : ℤ) ⊗[k]
            hodgeCohomologyComponent (formsAlgebras g) x.1.2.1 (x.1.2.2 : ℤ))
          ⟨((a, b), (c, d)), rfl⟩
          (hodgeCechMap f a CX.U CX.iSup_eq b (Hmk _ _ γ hγ) ⊗ₜ
            hodgeCechMap g c CY.U CY.iSup_eq d (Hmk _ _ ε hε))) =
      (((b : ℤ) * c).negOnePow : ℤ) • hodgeCechKunnethMap f g CX CY
        (hodgeBidegreeAdd ((a, b), (c, d)))
        (DirectSum.lof k
          {x : (ℕ × ℕ) × (ℕ × ℕ) // hodgeBidegreeAdd x = hodgeBidegreeAdd ((a, b), (c, d))}
          (fun x => H (hodgeSectionsK f (hodgeScalarsOverField f) x.1.1.1) CX.U x.1.1.2 ⊗[k]
            H (hodgeSectionsK g (hodgeScalarsOverField g) x.1.2.1) CY.U x.1.2.2)
          ⟨((a, b), (c, d)), rfl⟩ (Hmk _ _ γ hγ ⊗ₜ Hmk _ _ ε hε)) := by
  have hU' : (⊤ : (pullback f g).Opens) = ⨆ i, pullback.fst f g ⁻¹ᵁ CX.U i := by
    rw [← Scheme.Hom.preimage_iSup, ← CX.iSup_eq, Scheme.Hom.preimage_top]
  have hV' : (⊤ : (pullback f g).Opens) = ⨆ j, pullback.snd f g ⁻¹ᵁ CY.U j := by
    rw [← Scheme.Hom.preimage_iSup, ← CY.iSup_eq, Scheme.Hom.preimage_top]
  have hW := Stacks.CechKunneth.iSup_boxOpen_prodCover f g CX.U CY.U CX.iSup_eq CY.iSup_eq
  have hγ' := (d_hodgeSectionsK f a CX.U _ γ).symm.trans hγ
  have hε' := (d_hodgeSectionsK g c CY.U _ ε).symm.trans hε
  have hcls : ∀ {n m : ℕ} (z w : CechCochains.Cochain ((boxOpen f g).obj ∘ prodCover CX.U CY.U)
      (abSections (deRhamTerm (formsAlgebras (pullback.fst f g ≫ f)) n)) m) (_ : z = w) hz hw,
      hodgeCechClass (pullback.fst f g ≫ f) _ hW n z hz =
        hodgeCechClass (pullback.fst f g ≫ f) _ hW n w hw := by
    rintro n m z w rfl _ _
    rfl
  have hreindex : ∀ {n : ℕ} {q q' : ℤ} (e : q = q')
      (x : hodgeCohomologyComponent (formsAlgebras (pullback.fst f g ≫ f)) n q),
      reindexHodgeDeg (formsAlgebras (pullback.fst f g ≫ f)) e.symm
        (reindexHodgeDeg (formsAlgebras (pullback.fst f g ≫ f)) e x) = x := by
    rintro n q q' rfl x
    rfl
  have e₁ := (hodgePullback_hodgeCechClass (pullback.fst f g) (pullback.fst f g ≫ f) f (𝟙 _)
      (Category.comp_id _).symm CX.U CX.iSup_eq hU' a γ hγ').trans
    (hodgeCechClass_refCochain (pullback.fst f g ≫ f) a (fun i => pullback.fst f g ⁻¹ᵁ CX.U i)
      hU' (hodgeScalarsOverField (pullback.fst f g ≫ f)) ((boxOpen f g).obj ∘ prodCover CX.U CY.U)
      hW Prod.fst (fun ij => Stacks.CechKunneth.boxOpen_le_fst f g _)
      (pullbackCochain (pullback.fst f g) (pullback.fst f g ≫ f) f (𝟙 _)
        (Category.comp_id _).symm CX.U a γ)
      ((d_hodgeSectionsK _ _ _ _ _).trans
        (cechD_pullbackCochain_eq_zero _ _ _ _ _ _ _ _ hγ'))).symm
  have e₂ := (hodgePullback_hodgeCechClass (pullback.snd f g) (pullback.fst f g ≫ f) g (𝟙 _)
      (hodgeSchemeSquare_snd pullback.condition) CY.U CY.iSup_eq hV' c ε hε').trans
    (hodgeCechClass_refCochain (pullback.fst f g ≫ f) c (fun j => pullback.snd f g ⁻¹ᵁ CY.U j)
      hV' (hodgeScalarsOverField (pullback.fst f g ≫ f)) ((boxOpen f g).obj ∘ prodCover CX.U CY.U)
      hW Prod.snd (fun ij => Stacks.CechKunneth.boxOpen_le_snd f g _)
      (pullbackCochain (pullback.snd f g) (pullback.fst f g ≫ f) g (𝟙 _)
        (hodgeSchemeSquare_snd pullback.condition) CY.U c ε)
      ((d_hodgeSectionsK _ _ _ _ _).trans
        (cechD_pullbackCochain_eq_zero _ _ _ _ _ _ _ _ hε'))).symm
  refine (hodgeSchemeKunnethMap_lof_tmul f g (pullback.fst f g) (pullback.snd f g)
    pullback.condition (a, b) (c, d) (hodgeCechMap f a CX.U CX.iSup_eq b (Hmk _ _ γ hγ))
    (hodgeCechMap g c CY.U CY.iSup_eq d (Hmk _ _ ε hε))).trans ?_
  refine Eq.trans ?_ (congrArg _ (hodgeCechKunnethMap_lof_tmul_Hmk f g CX CY γ hγ ε hε)).symm
  refine (congrArg₂ (fun x y => reindexHodgeDeg (formsAlgebras (pullback.fst f g ≫ f))
    (Nat.cast_add b d).symm (hodgeCohomologyCup (formsAlgebras (pullback.fst f g ≫ f)) a c
      (b : ℤ) (d : ℤ) x y)) e₁ e₂).trans ?_
  refine (congrArg (reindexHodgeDeg (formsAlgebras (pullback.fst f g ≫ f)) (Nat.cast_add b d).symm)
    (hodgeCohomologyCup_hodgeCechClass (pullback.fst f g ≫ f)
      ((boxOpen f g).obj ∘ prodCover CX.U CY.U) hW a c _ _ _ _)).trans ?_
  rw [AlgebraicGeometry.SheafOfModules.reindexHodgeDeg_zsmul, hreindex]
  exact congrArg _ (hcls _ _ (wedgeCup_refCochain_pullbackCochain f g CX.U CY.U γ ε) _ _)

/-- **The sign of the Künneth map**: the endomorphism of
`⨁_{a + c = r, b + d = s} Ȟ^b(𝒰, Ω^a_{X/k}) ⊗_k Ȟ^d(𝒱, Ω^c_{Y/k})` which is multiplication by
`(-1)^{b c}` on the summand of bidegrees `((a, b), (c, d))`. -/
abbrev hodgeKunnethSign (rs : ℕ × ℕ) :
    (DirectSum {x : (ℕ × ℕ) × (ℕ × ℕ) // hodgeBidegreeAdd x = rs} fun x =>
      H (hodgeSectionsK f (hodgeScalarsOverField f) x.1.1.1) CX.U x.1.1.2 ⊗[k]
        H (hodgeSectionsK g (hodgeScalarsOverField g) x.1.2.1) CY.U x.1.2.2) →ₗ[k]
      (DirectSum {x : (ℕ × ℕ) × (ℕ × ℕ) // hodgeBidegreeAdd x = rs} fun x =>
        H (hodgeSectionsK f (hodgeScalarsOverField f) x.1.1.1) CX.U x.1.1.2 ⊗[k]
          H (hodgeSectionsK g (hodgeScalarsOverField g) x.1.2.1) CY.U x.1.2.2) :=
  DirectSum.lmap fun x => (((x.1.1.2 : ℤ) * x.1.2.1).negOnePow : ℤ) • LinearMap.id

/-- **The Künneth map read on Čech classes**: the Künneth map composed with the class maps of `𝒰`
and `𝒱` is the Čech Künneth map composed with the sign `Stacks.HodgeWeil.hodgeKunnethSign`. -/
theorem hodgeSchemeKunnethMap_comp_lmap_hodgeCechMap (rs : ℕ × ℕ) :
    hodgeSchemeKunnethMap f g (pullback.fst f g) (pullback.snd f g) pullback.condition rs ∘ₗ
        DirectSum.lmap (fun x => TensorProduct.map
          (hodgeCechMap f x.1.1.1 CX.U CX.iSup_eq x.1.1.2)
          (hodgeCechMap g x.1.2.1 CY.U CY.iSup_eq x.1.2.2)) =
      hodgeCechKunnethMap f g CX CY rs ∘ₗ hodgeKunnethSign f g CX CY rs := by
  refine DirectSum.linearMap_ext k fun x => TensorProduct.ext' fun ξ ζ => ?_
  obtain ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, hx⟩ := x
  subst hx
  obtain ⟨γ, hγ, rfl⟩ := Stacks.CechKunneth.Hmk_surjective _ _ ξ
  obtain ⟨ε, hε, rfl⟩ := Stacks.CechKunneth.Hmk_surjective _ _ ζ
  simp only [LinearMap.comp_apply, DirectSum.lmap_lof, TensorProduct.map_tmul,
    LinearMap.smul_apply, LinearMap.id_apply, map_zsmul]
  exact hodgeSchemeKunnethMap_lof_hodgeCechMap f g CX CY (a := a) (b := b) (c := c) (d := d)
    γ hγ ε hε

/-- The sign of the Künneth map is bijective, being its own inverse. -/
theorem bijective_hodgeKunnethSign (rs : ℕ × ℕ) :
    Function.Bijective (hodgeKunnethSign f g CX CY rs) :=
  bijective_lmap_zsmul_units _

end Classes

/-- **The Hodge Künneth formula** ([Stacks, Remark 0FWE]): for quasi-compact schemes `X` and `Y`
over a field `k` with affine diagonal, in every bidegree `(r, s)` the Künneth map
`⨁_{a + c = r, b + d = s} H^b(X, Ω^a_{X/k}) ⊗_k H^d(Y, Ω^c_{Y/k}) ⟶ H^s(X ×_k Y, Ω^r)`,
`ξ ⊗ ζ ↦ pr₁^*ξ ∪ pr₂^*ζ`, is bijective. -/
theorem bijective_hodgeSchemeKunnethMap_pullback [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsAffineHom (pullback.diagonal (terminal.from Y))] (rs : ℕ × ℕ) :
    Function.Bijective
      (hodgeSchemeKunnethMap f g (pullback.fst f g) (pullback.snd f g) pullback.condition rs) := by
  have h := congrArg DFunLike.coe (hodgeSchemeKunnethMap_comp_lmap_hodgeCechMap f g
    (finiteAffineCover X) (finiteAffineCover Y) rs)
  rw [LinearMap.coe_comp, LinearMap.coe_comp] at h
  have hK := bijective_hodgeCechKunnethMap f g (finiteAffineCover X) (finiteAffineCover Y) rs
  have hD := bijective_hodgeKunnethSign f g (finiteAffineCover X) (finiteAffineCover Y) rs
  refine (Function.Bijective.of_comp_iff _ ?_).1 (by rw [h]; exact hK.comp hD)
  exact ⟨(DirectSum.lmap_injective _).2 fun x => (TensorProduct.map_bijective
      (bijective_hodgeCechMap _ _ _ _ (fun _ s => (finiteAffineCover X).isAffineOpen_inter X s) _)
      (bijective_hodgeCechMap _ _ _ _ (fun _ s => (finiteAffineCover Y).isAffineOpen_inter Y s)
        _)).1,
    (DirectSum.lmap_surjective _).2 fun x => (TensorProduct.map_bijective
      (bijective_hodgeCechMap _ _ _ _ (fun _ s => (finiteAffineCover X).isAffineOpen_inter X s) _)
      (bijective_hodgeCechMap _ _ _ _ (fun _ s => (finiteAffineCover Y).isAffineOpen_inter Y s)
        _)).2⟩

/-- **The Hodge Künneth formula in every bidegree** ([Stacks, Remark 0FWE]): for a fibre product
`P` of smooth projective schemes `X` and `Y` over `k`, with projections `p` and `q`, and every
bidegree `(r, s)`, the map
`⨁_{a + c = r, b + d = s} H^b(X, Ω^a_{X/k}) ⊗_k H^d(Y, Ω^c_{Y/k}) ⟶ H^s(P, Ω^r_{P/k})`,
`ξ ⊗ ζ ↦ p^*ξ ∪ q^*ζ`, is bijective. -/
theorem bijective_hodgeKunnethBidegreeMap {X Y P : (SmoothProjectiveScheme k).FullSubcategory}
    (p : P ⟶ X) (q : P ⟶ Y)
    (hP : IsPullback ((toScheme k).map p) ((toScheme k).map q) X.obj.hom Y.obj.hom)
    (rs : ℕ × ℕ) :
    Function.Bijective (hodgeKunnethBidegreeMap p q rs) := by
  -- A smooth projective scheme over `k` is separated, so its diagonal is a closed immersion.
  have hdiag : ∀ Z : (SmoothProjectiveScheme k).FullSubcategory,
      IsAffineHom (pullback.diagonal (terminal.from Z.obj.left)) := fun Z => by
    have := (SmoothProjectiveScheme.isProjective Z).isProper
    have h : IsSeparated (Z.obj.hom ≫ terminal.from (Spec (.of k))) := inferInstance
    rw [show Z.obj.hom ≫ terminal.from (Spec (.of k)) = terminal.from Z.obj.left from
      terminal.hom_ext _ _] at h
    infer_instance
  have := hdiag X
  have := hdiag Y
  have : CompactSpace X.obj.left := SmoothProjectiveScheme.compactSpace X
  have : CompactSpace Y.obj.left := SmoothProjectiveScheme.compactSpace Y
  exact bijective_hodgeKunnethBidegreeMap_of_pullback p q hP rs
    (bijective_hodgeSchemeKunnethMap_pullback X.obj.hom Y.obj.hom rs)

/-- **The Hodge Künneth map is bijective** ([Stacks, Remark 0FWE]): for a fibre product `P` of
smooth projective schemes `X` and `Y` over `k` with projections `p` and `q`, the map
`H^*_{Hodge}(X/k) ⊗_k H^*_{Hodge}(Y/k) ⟶ H^*_{Hodge}(P/k)`, `ξ ⊗ ζ ↦ p^*ξ ∪ q^*ζ`, is
bijective. -/
theorem bijective_hodgeKunnethMap {X Y P : (SmoothProjectiveScheme k).FullSubcategory}
    (p : P ⟶ X) (q : P ⟶ Y)
    (hP : IsPullback ((toScheme k).map p) ((toScheme k).map q) X.obj.hom Y.obj.hom) :
    Function.Bijective (hodgeKunnethMap p q) :=
  (bijective_hodgeKunnethMap_iff p q).2 fun rs => bijective_hodgeKunnethBidegreeMap p q hP rs

variable (k) in
/-- **Hodge cohomology satisfies (A5)** of Section 0FID ([Stacks, Remark 0FWE]):
`H^*_{Hodge}(Spec(k)/k) = k`, and for smooth projective `X` and `Y` over `k` the Künneth map
`H^*_{Hodge}(X/k) ⊗_k H^*_{Hodge}(Y/k) ⟶ H^*_{Hodge}(X × Y/k)`, `a ⊗ b ↦ pr₁^*a ∪ pr₂^*b`, is
bijective. -/
theorem hodge_kunnethAxiom : (hodgeFirstChernClassData k).KunnethAxiom :=
  ⟨bijective_algebraMap_hodgeAlgebraOf_point k, fun X Y =>
    bijective_hodgeKunnethMap (SmoothProjectiveScheme.fst X Y) (SmoothProjectiveScheme.snd X Y)
      (IsPullback.of_hasPullback X.obj.hom Y.obj.hom)⟩

end Stacks.HodgeWeil

end
