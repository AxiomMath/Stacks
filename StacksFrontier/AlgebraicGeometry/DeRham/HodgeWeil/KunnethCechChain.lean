module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.KunnethCechModel
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.KunnethCechSum
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.KunnethSections
public import StacksFrontier.AlgebraicGeometry.Cohomology.CechKunneth.KunnethFormula
public import StacksFrontier.Topology.Sheaves.Cohomology.CechKunneth.Kunneth

/-!
# The Künneth isomorphism for Hodge cohomology, computed on Čech cocycles

Let `k` be a field, `f : X ⟶ Spec k` and `g : Y ⟶ Spec k` schemes over `k` with affine diagonal,
`W = X ×_k Y`, and `𝒰`, `𝒱` finite affine open coverings of `X` and `Y`. The opens
`U_i × V_j = pr₁⁻¹U_i ∩ pr₂⁻¹V_j` cover `W`, and all finite intersections of the three coverings
are affine. This file assembles, in every bidegree `(r, s)`, the `k`-linear map

`⨁_{a + c = r, b + d = s} Ȟ^b(𝒰, Ω^a_{X/k}) ⊗_k Ȟ^d(𝒱, Ω^c_{Y/k}) ⟶ H^s(W, Ω^r_{W/k})`

and proves that it is bijective. It is the composite of

* the regrouping of the pairs of bidegrees `((a, b), (c, d))` by the form degrees `(a, c)`;
* for each `(a, c)`, the Künneth isomorphism of Čech cohomology
  `⨁_{b + d = s} Ȟ^b(𝒰, Ω^a) ⊗_k Ȟ^d(𝒱, Ω^c) ≅ Ȟ^s(𝒰 × 𝒱, Ω^a ⊠ Ω^c)` of [Stacks, Tag 0BED],
  `Stacks.CechKunneth.kunnethEquiv`, for the presheaves `(U, V) ↦ Γ(U, Ω^a) ⊗_k Γ(V, Ω^c)` on
  pairs of opens;
* the identification of the product of these Čech cohomologies with the Čech cohomology of
  their sectionwise direct sum `(U, V) ↦ ⨁_{a + c = r} Γ(U, Ω^a) ⊗_k Γ(V, Ω^c)`;
* the map induced by the morphism of presheaves from that direct sum to
  `(U, V) ↦ Γ(U × V, Ω^r_{W/k})`, `ω ⊗ η ↦ pr₁^*ω ∧ pr₂^*η` (`kunnethSectionsMap`), which is
  bijective on pairs of affine opens ([Stacks, Tag 0FMA]) and hence on the nerve;
* the passage from pairs of opens to the opens `U × V` of `W`;
* the class map `Ȟ^s(𝒰 × 𝒱, Ω^r_{W/k}) ⟶ H^s(W, Ω^r_{W/k})`, bijective because the nerve
  consists of affine opens ([Stacks, Tag 01XD]).

On the classes of two Čech cocycles `γ` and `ε` the map is the class of the Čech cocycle
`σ ↦ (pr₁^*γ_{σ₀ … σ_b})| ∧ (pr₂^*ε_{σ_b … σ_{b + d}})|`, the Alexander–Whitney product of the
pulled back cocycles; this is the Čech form of `pr₁^*ξ ∪ pr₂^*ζ` used in [Stacks, Remark 0FWE].

## Main definitions

* `Stacks.HodgeWeil.presheafDirectSum`: the sectionwise direct sum of a family of functors to
  modules, with its inclusions and projections.
* `Stacks.HodgeWeil.hodgeKunnethSumMap`: the morphism of presheaves on pairs of opens
  `⨁_{a + c = r} Γ(U, Ω^a_{X/k}) ⊗_k Γ(V, Ω^c_{Y/k}) ⟶ Γ(U × V, Ω^r_{W/k})`.
* `Stacks.HodgeWeil.hodgeCechKunnethMap`: the Čech Künneth map in bidegree `(r, s)`.
* `Stacks.HodgeWeil.hodgeKunnethCochain`: the Čech cochain `pr₁^*γ ∧ pr₂^*ε` on `𝒰 × 𝒱`.

## Main results

* `Stacks.HodgeWeil.bijective_hodgeCechKunnethMap`: the Čech Künneth map is bijective.
* `Stacks.HodgeWeil.hodgeCechKunnethMap_lof_tmul_Hmk`: on `[γ] ⊗ [ε]` it is the class
  `Stacks.HodgeWeil.hodgeCechClass` of `Stacks.HodgeWeil.hodgeKunnethCochain`.
* `Stacks.HodgeWeil.hodgeKunnethCochain_eq`: that cochain is the Alexander–Whitney product
  `Stacks.CechKunneth.cup` carried by `Stacks.HodgeWeil.hodgeKunnethSumMap`.

## References

* [Stacks Project, Remark 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
* [Stacks Project, Tag 0BED](https://stacks.math.columbia.edu/tag/0BED)
* [Stacks Project, Tag 0FMA](https://stacks.math.columbia.edu/tag/0FMA)
* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open scoped TensorProduct
open AlgebraicGeometry.SheafOfModules (hodgeCohomologyComponent)
open Stacks.CechKunneth (Cochain H Hmk Hmap Idx Src LatProd extTensor prodCover cup boxOpen
  FiniteAffineCover kunnethMap kunnethEquiv transportEquiv transportCochain mapCochain inter res
  HcupT)

universe u

namespace Stacks.HodgeWeil

attribute [local instance] HasDerivedCategory.standard

/-! ### Sectionwise direct sums of presheaves of modules -/

section DirectSumPresheaf

variable {k : Type u} [CommRing k] {C : Type*} [Category C] {ι : Type u}
  (F : ι → C ⥤ ModuleCat.{u} k)

/-- **The sectionwise direct sum** `Z ↦ ⨁_i F_i(Z)` of a family of functors to `k`-modules. -/
def presheafDirectSum : C ⥤ ModuleCat.{u} k where
  obj Z := ModuleCat.of k (DirectSum ι fun i => (F i).obj Z)
  map h := ModuleCat.ofHom (DirectSum.lmap fun i => ((F i).map h).hom)
  map_id Z := ModuleCat.hom_ext (LinearMap.ext fun x => DFinsupp.ext fun i => by
    change ((F i).map (𝟙 Z)).hom (x i) = x i
    rw [(F i).map_id]
    rfl)
  map_comp h h' := ModuleCat.hom_ext (LinearMap.ext fun x => DFinsupp.ext fun i => by
    change ((F i).map (h ≫ h')).hom (x i) = ((F i).map h').hom (((F i).map h).hom (x i))
    rw [(F i).map_comp]
    rfl)

variable [DecidableEq ι]

/-- The restriction maps of `presheafDirectSum F` act summandwise. -/
theorem presheafDirectSum_map_lof {Z Z' : C} (h : Z ⟶ Z') (i : ι) (x : (F i).obj Z) :
    ((presheafDirectSum F).map h).hom (DirectSum.lof k ι (fun j => (F j).obj Z) i x) =
      DirectSum.lof k ι (fun j => (F j).obj Z') i (((F i).map h).hom x) :=
  DirectSum.lmap_lof (fun i => ((F i).map h).hom) i x

/-- The inclusion of a summand into the sectionwise direct sum. -/
def presheafDirectSumInc (i : ι) : F i ⟶ presheafDirectSum F where
  app Z := ModuleCat.ofHom (DirectSum.lof k ι (fun j => (F j).obj Z) i)
  naturality _Z _Z' h := ModuleCat.hom_ext (LinearMap.ext fun x =>
    (presheafDirectSum_map_lof F h i x).symm)

/-- The projection of the sectionwise direct sum to a summand. -/
def presheafDirectSumProj (i : ι) : presheafDirectSum F ⟶ F i where
  app Z := ModuleCat.ofHom (DirectSum.component k ι (fun j => (F j).obj Z) i)
  naturality _Z _Z' _h := ModuleCat.hom_ext (LinearMap.ext fun _x => rfl)

/-- On sections, `presheafDirectSumInc F i` is the inclusion `DirectSum.lof` of the `i`-th
summand. -/
theorem presheafDirectSumInc_app_apply (i : ι) (Z : C) (x : (F i).obj Z) :
    ((presheafDirectSumInc F i).app Z).hom x = DirectSum.lof k ι (fun j => (F j).obj Z) i x :=
  rfl

/-- The projection to a summand is a retraction of the inclusion of that summand. -/
theorem presheafDirectSumInc_proj (i : ι) :
    presheafDirectSumInc F i ≫ presheafDirectSumProj F i = 𝟙 (F i) :=
  NatTrans.ext (funext fun Z => ModuleCat.hom_ext (LinearMap.ext fun x =>
    DirectSum.component.lof_self k (M := fun j => ((F j).obj Z : Type u)) i x))

/-- The inclusion of one summand followed by the projection to a different summand is zero. -/
theorem presheafDirectSumInc_proj_of_ne {i j : ι} (h : i ≠ j) :
    presheafDirectSumInc F i ≫ presheafDirectSumProj F j = 0 := by
  refine NatTrans.ext (funext fun Z => ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  rw [NatTrans.app_zero, ModuleCat.hom_zero, LinearMap.zero_apply]
  change DirectSum.component k ι (fun j => (F j).obj Z) j
    (DirectSum.lof k ι (fun j => (F j).obj Z) i x) = 0
  rw [DirectSum.component.of, dite_eq_right h]

/-- The sum over all summands of projection followed by inclusion is the identity of
`presheafDirectSum F`. -/
theorem sum_presheafDirectSumProj_inc [Fintype ι] :
    ∑ i, presheafDirectSumProj F i ≫ presheafDirectSumInc F i = 𝟙 (presheafDirectSum F) := by
  refine NatTrans.ext (funext fun Z => ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  rw [NatTrans.app_sum, ModuleCat.hom_sum, LinearMap.sum_apply]
  exact (Finset.sum_congr rfl fun i _ => rfl).trans (DirectSum.sum_univ_of x)

end DirectSumPresheaf

/-! ### Bidegrees -/

section Bidegree

/-- **Splitting a pair of bidegrees** `((a, b), (c, d))` of sum `(r, s)` into the pair of form
degrees `(a, c)`, of sum `r`, and the pair of cohomological degrees `(b, d)`, of sum `s`. -/
def hodgeBidegreeSplit (rs : ℕ × ℕ) :
    {x : (ℕ × ℕ) × (ℕ × ℕ) // hodgeBidegreeAdd x = rs} ≃ Idx rs.1 × Idx rs.2 where
  toFun x := (⟨(x.1.1.1, x.1.2.1), congrArg Prod.fst x.2⟩,
    ⟨(x.1.1.2, x.1.2.2), congrArg Prod.snd x.2⟩)
  invFun y := ⟨((y.1.1.1, y.2.1.1), (y.1.1.2, y.2.1.2)), Prod.ext y.1.2 y.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- There are finitely many pairs of bidegrees of a given sum. -/
instance (rs : ℕ × ℕ) : Fintype {x : (ℕ × ℕ) × (ℕ × ℕ) // hodgeBidegreeAdd x = rs} :=
  Fintype.ofEquiv _ (hodgeBidegreeSplit rs).symm

variable (R : Type*) [Semiring R] (N : ℕ → ℕ → ℕ → ℕ → Type u)
  [∀ a b c d, AddCommMonoid (N a b c d)] [∀ a b c d, Module R (N a b c d)]

/-- **Regrouping a product indexed by pairs of bidegrees**: a family indexed by the pairs
`((a, b), (c, d))` of sum `(r, s)` is a family indexed first by the pairs `(a, c)` of sum `r` and
then by the pairs `(b, d)` of sum `s`. -/
def hodgeBidegreePiEquiv (rs : ℕ × ℕ) :
    (∀ x : {x : (ℕ × ℕ) × (ℕ × ℕ) // hodgeBidegreeAdd x = rs}, N x.1.1.1 x.1.1.2 x.1.2.1 x.1.2.2)
      ≃ₗ[R] ∀ (ac : ULift.{u} (Idx rs.1)) (bd : Idx rs.2),
        N ac.down.1.1 bd.1.1 ac.down.1.2 bd.1.2 where
  toFun F ac bd := F ⟨((ac.down.1.1, bd.1.1), (ac.down.1.2, bd.1.2)), Prod.ext ac.down.2 bd.2⟩
  invFun G x := G ⟨⟨(x.1.1.1, x.1.2.1), congrArg Prod.fst x.2⟩⟩
    ⟨(x.1.1.2, x.1.2.2), congrArg Prod.snd x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- `hodgeBidegreePiEquiv` carries the family supported at `((a, b), (c, d))` to the family
supported at `(a, c)` and then at `(b, d)`. -/
theorem hodgeBidegreePiEquiv_single (rs : ℕ × ℕ)
    (x : {x : (ℕ × ℕ) × (ℕ × ℕ) // hodgeBidegreeAdd x = rs})
    (v : N x.1.1.1 x.1.1.2 x.1.2.1 x.1.2.2) :
    hodgeBidegreePiEquiv R N rs (Pi.single x v) =
      Pi.single (⟨⟨(x.1.1.1, x.1.2.1), congrArg Prod.fst x.2⟩⟩ : ULift.{u} (Idx rs.1))
        (Pi.single (⟨(x.1.1.2, x.1.2.2), congrArg Prod.snd x.2⟩ : Idx rs.2) v) := by
  let M : {x : (ℕ × ℕ) × (ℕ × ℕ) // hodgeBidegreeAdd x = rs} → Type u := fun x =>
    N x.1.1.1 x.1.1.2 x.1.2.1 x.1.2.2
  funext ac bd
  by_cases hac : ac = ⟨⟨(x.1.1.1, x.1.2.1), congrArg Prod.fst x.2⟩⟩
  · subst hac
    by_cases hbd : bd = ⟨(x.1.1.2, x.1.2.2), congrArg Prod.snd x.2⟩
    · subst hbd
      rw [Pi.single_eq_same, Pi.single_eq_same]
      exact Pi.single_eq_same (M := M) x v
    · rw [Pi.single_eq_same, Pi.single_eq_of_ne hbd]
      refine Pi.single_eq_of_ne (M := M) (fun h => hbd (Subtype.ext (Prod.ext ?_ ?_))) v
      · exact congrArg (fun y : {x : (ℕ × ℕ) × (ℕ × ℕ) // hodgeBidegreeAdd x = rs} => y.1.1.2) h
      · exact congrArg (fun y : {x : (ℕ × ℕ) × (ℕ × ℕ) // hodgeBidegreeAdd x = rs} => y.1.2.2) h
  · rw [Pi.single_eq_of_ne hac]
    refine Pi.single_eq_of_ne (M := M)
      (fun h => hac (ULift.ext _ _ (Subtype.ext (Prod.ext ?_ ?_)))) v
    · exact congrArg (fun y : {x : (ℕ × ℕ) × (ℕ × ℕ) // hodgeBidegreeAdd x = rs} => y.1.1.1) h
    · exact congrArg (fun y : {x : (ℕ × ℕ) × (ℕ × ℕ) // hodgeBidegreeAdd x = rs} => y.1.2.1) h

end Bidegree

/-! ### The Künneth presheaf on pairs of opens -/

section Kunneth

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (g : Y ⟶ Spec (.of k))

/-- The summands `(U, V) ↦ Γ(U, Ω^a_{X/k}) ⊗_k Γ(V, Ω^c_{Y/k})`, for `a + c = r`, indexed by
`ULift (Idx r)`. -/
abbrev hodgeKunnethSummand (r : ℕ) (ac : ULift.{u} (Idx r)) :
    (LatProd X.Opens Y.Opens)ᵒᵖ ⥤ ModuleCat.{u} k :=
  extTensor (hodgeSectionsK f (hodgeScalarsOverField f) ac.down.1.1)
    (hodgeSectionsK g (hodgeScalarsOverField g) ac.down.1.2)

/-- **The presheaf `(U, V) ↦ ⨁_{a + c = r} Γ(U, Ω^a_{X/k}) ⊗_k Γ(V, Ω^c_{Y/k})`** on pairs of
opens of `X` and `Y`, the sectionwise direct sum of the external tensor products. -/
abbrev hodgeKunnethSumPresheaf (r : ℕ) : (LatProd X.Opens Y.Opens)ᵒᵖ ⥤ ModuleCat.{u} k :=
  presheafDirectSum (hodgeKunnethSummand f g r)

/-- The Künneth map on sections over `(U, V)`: `kunnethSectionsMap` after re-indexing the direct
sum along `ULift`. -/
def hodgeKunnethSumMapApp (r : ℕ) (Z : LatProd X.Opens Y.Opens) :
    (hodgeKunnethSumPresheaf f g r).obj (op Z) →ₗ[k]
      ((boxOpen f g).op ⋙ hodgeSectionsK (pullback.fst f g ≫ f)
        (hodgeScalarsOverField (pullback.fst f g ≫ f)) r).obj (op Z) :=
  kunnethSectionsMap f g r Z.fst Z.snd ∘ₗ
    (DirectSum.lequivCongrLeft k (Equiv.ulift.{u, 0} (α := Idx r))).toLinearMap

/-- On the summand of index `ac`, `hodgeKunnethSumMapApp` is `kunnethSectionsMap` on the summand
of index `ac.down`. -/
theorem hodgeKunnethSumMapApp_lof (r : ℕ) (Z : LatProd X.Opens Y.Opens) (ac : ULift.{u} (Idx r))
    (t : (hodgeSectionsK f (hodgeScalarsOverField f) ac.down.1.1).obj (op Z.fst) ⊗[k]
      (hodgeSectionsK g (hodgeScalarsOverField g) ac.down.1.2).obj (op Z.snd)) :
    hodgeKunnethSumMapApp f g r Z (DirectSum.lof k _ _ ac t) =
      kunnethSectionsMap f g r Z.fst Z.snd (DirectSum.lof k _ _ ac.down t) :=
  congrArg (kunnethSectionsMap f g r Z.fst Z.snd)
    (DirectSum.lequivCongrLeft_lof k (e := Equiv.ulift.{u, 0} (α := Idx r))
      (M := fun ac : ULift.{u} (Idx r) =>
        (hodgeSectionsK f (hodgeScalarsOverField f) ac.down.1.1).obj (op Z.fst) ⊗[k]
          (hodgeSectionsK g (hodgeScalarsOverField g) ac.down.1.2).obj (op Z.snd))
      (i := ac) (k := ac.down) rfl t t rfl)

/-- `hodgeKunnethSumMapApp` commutes with restriction to smaller opens. -/
theorem hodgeKunnethSumMapApp_naturality (r : ℕ) {Z Z' : LatProd X.Opens Y.Opens} (h : Z' ≤ Z) :
    ((hodgeSectionsK (pullback.fst f g ≫ f) (hodgeScalarsOverField (pullback.fst f g ≫ f)) r).map
        ((boxOpen f g).map (homOfLE h)).op).hom ∘ₗ hodgeKunnethSumMapApp f g r Z =
      hodgeKunnethSumMapApp f g r Z' ∘ₗ
        ((hodgeKunnethSumPresheaf f g r).map (homOfLE h).op).hom := by
  refine DirectSum.linearMap_ext k fun ac => TensorProduct.ext' fun ω η => ?_
  have e := LinearMap.congr_fun (kunnethSectionsMap_naturality f g r
    (LatProd.fst_mono h) (LatProd.snd_mono h)) (DirectSum.lof k _ _ ac.down (ω ⊗ₜ η))
  rw [LinearMap.comp_apply, LinearMap.comp_apply, DirectSum.lmap_lof] at e
  change ((hodgeSectionsK (pullback.fst f g ≫ f) (hodgeScalarsOverField (pullback.fst f g ≫ f))
      r).map ((boxOpen f g).map (homOfLE h)).op).hom
      (hodgeKunnethSumMapApp f g r Z (DirectSum.lof k _ _ ac (ω ⊗ₜ η))) =
    hodgeKunnethSumMapApp f g r Z' (((hodgeKunnethSumPresheaf f g r).map (homOfLE h).op).hom
      (DirectSum.lof k _ _ ac (ω ⊗ₜ η)))
  exact (congrArg _ (hodgeKunnethSumMapApp_lof f g r Z ac (ω ⊗ₜ η))).trans (e.trans
    ((hodgeKunnethSumMapApp_lof f g r Z' ac _).symm.trans
      (congrArg _ (presheafDirectSum_map_lof (hodgeKunnethSummand f g r) (homOfLE h).op ac
        (ω ⊗ₜ η)).symm)))

/-- **The Künneth map of presheaves** from `hodgeKunnethSumPresheaf` to
`(U, V) ↦ Γ(U × V, Ω^r_{X ×_k Y/k})`, given on `(U, V)` by `kunnethSectionsMap`. -/
def hodgeKunnethSumMap (r : ℕ) :
    hodgeKunnethSumPresheaf f g r ⟶ (boxOpen f g).op ⋙
      hodgeSectionsK (pullback.fst f g ≫ f) (hodgeScalarsOverField (pullback.fst f g ≫ f)) r where
  app Z := ModuleCat.ofHom (X := (hodgeKunnethSumPresheaf f g r).obj Z)
    (Y := ((boxOpen f g).op ⋙ hodgeSectionsK (pullback.fst f g ≫ f)
      (hodgeScalarsOverField (pullback.fst f g ≫ f)) r).obj Z)
    (hodgeKunnethSumMapApp f g r Z.unop)
  naturality _Z _Z' h :=
    ModuleCat.hom_ext (hodgeKunnethSumMapApp_naturality f g r (leOfHom h.unop)).symm

/-- The component of `hodgeKunnethSumMap` at `(U, V)` is `hodgeKunnethSumMapApp`. -/
theorem hodgeKunnethSumMap_app_apply (r : ℕ) (Z : LatProd X.Opens Y.Opens)
    (x : (hodgeKunnethSumPresheaf f g r).obj (op Z)) :
    ((hodgeKunnethSumMap f g r).app (op Z)).hom x = hodgeKunnethSumMapApp f g r Z x :=
  rfl

/-- **The Künneth map of presheaves is bijective on a pair of affine opens.** -/
theorem bijective_hodgeKunnethSumMap_app (r : ℕ) (Z : LatProd X.Opens Y.Opens)
    (hU : IsAffineOpen Z.fst) (hV : IsAffineOpen Z.snd) :
    Function.Bijective ((hodgeKunnethSumMap f g r).app (op Z)).hom :=
  (bijective_kunnethSectionsMap f g r hU hV).comp (DirectSum.lequivCongrLeft k _).bijective

/-! ### The Čech Künneth map -/

variable (CX : FiniteAffineCover X) (CY : FiniteAffineCover Y)

/-- **Regrouping the source of the Künneth map**: the classes indexed by pairs of bidegrees
`((a, b), (c, d))` of sum `(r, s)` are the classes indexed first by the pair of form degrees
`(a, c)` and then by the pair of cohomological degrees `(b, d)`. -/
abbrev hodgeCechKunnethSourceEquiv (rs : ℕ × ℕ) :
    (∀ x : {x : (ℕ × ℕ) × (ℕ × ℕ) // hodgeBidegreeAdd x = rs},
      H (hodgeSectionsK f (hodgeScalarsOverField f) x.1.1.1) CX.U x.1.1.2 ⊗[k]
        H (hodgeSectionsK g (hodgeScalarsOverField g) x.1.2.1) CY.U x.1.2.2) ≃ₗ[k]
      ∀ ac : ULift.{u} (Idx rs.1), Src CX.U CY.U
        (hodgeSectionsK f (hodgeScalarsOverField f) ac.down.1.1)
        (hodgeSectionsK g (hodgeScalarsOverField g) ac.down.1.2) rs.2 :=
  hodgeBidegreePiEquiv k (fun a b c d => H (hodgeSectionsK f (hodgeScalarsOverField f) a) CX.U b
    ⊗[k] H (hodgeSectionsK g (hodgeScalarsOverField g) c) CY.U d) rs

/-- The Čech cohomology of `hodgeKunnethSumPresheaf` for the product family is the product of
the Čech cohomologies of the summands (`cechSumEquiv`). -/
def hodgeKunnethSumEquiv (r s : ℕ) :
    H (hodgeKunnethSumPresheaf f g r) (prodCover CX.U CY.U) s ≃ₗ[k]
      ∀ ac : ULift.{u} (Idx r), H (hodgeKunnethSummand f g r ac) (prodCover CX.U CY.U) s :=
  cechSumEquiv (prodCover CX.U CY.U) (presheafDirectSumInc (hodgeKunnethSummand f g r))
    (presheafDirectSumProj (hodgeKunnethSummand f g r))
    (presheafDirectSumInc_proj (hodgeKunnethSummand f g r))
    (fun _ _ => presheafDirectSumInc_proj_of_ne (hodgeKunnethSummand f g r))
    (sum_presheafDirectSumProj_inc (hodgeKunnethSummand f g r)) s

/-- **The Künneth map for Hodge cohomology, computed on Čech classes**: in bidegree `(r, s)`,
`⨁_{a + c = r, b + d = s} Ȟ^b(𝒰, Ω^a_{X/k}) ⊗_k Ȟ^d(𝒱, Ω^c_{Y/k}) ⟶ H^s(X ×_k Y, Ω^r_{X ×_k Y/k})`,
for finite affine coverings `𝒰` of `X` and `𝒱` of `Y`. -/
def hodgeCechKunnethMap (rs : ℕ × ℕ) :
    (DirectSum {x : (ℕ × ℕ) × (ℕ × ℕ) // hodgeBidegreeAdd x = rs} fun x =>
      H (hodgeSectionsK f (hodgeScalarsOverField f) x.1.1.1) CX.U x.1.1.2 ⊗[k]
        H (hodgeSectionsK g (hodgeScalarsOverField g) x.1.2.1) CY.U x.1.2.2) →ₗ[k]
      hodgeCohomologyComponent (formsAlgebras (pullback.fst f g ≫ f)) rs.1 (rs.2 : ℤ) :=
  hodgeCechMap (pullback.fst f g ≫ f) rs.1 ((boxOpen f g).obj ∘ prodCover CX.U CY.U)
      (Stacks.CechKunneth.iSup_boxOpen_prodCover f g CX.U CY.U CX.iSup_eq CY.iSup_eq) rs.2 ∘ₗ
    (transportEquiv (boxOpen f g) (hodgeSectionsK (pullback.fst f g ≫ f)
      (hodgeScalarsOverField (pullback.fst f g ≫ f)) rs.1) (prodCover CX.U CY.U)
      (fun σ => Stacks.CechKunneth.boxOpen_inter_prodCover f g CX.U CY.U σ) rs.2).toLinearMap ∘ₗ
    Hmap (prodCover CX.U CY.U) (hodgeKunnethSumMap f g rs.1) rs.2 ∘ₗ
    (hodgeKunnethSumEquiv f g CX CY rs.1 rs.2).symm.toLinearMap ∘ₗ
    (LinearEquiv.piCongrRight fun ac : ULift.{u} (Idx rs.1) =>
      kunnethEquiv CX.U CY.U (hodgeSectionsK f (hodgeScalarsOverField f) ac.down.1.1)
        (hodgeSectionsK g (hodgeScalarsOverField g) ac.down.1.2) rs.2).toLinearMap ∘ₗ
    (hodgeCechKunnethSourceEquiv f g CX CY rs).toLinearMap ∘ₗ
    (DirectSum.linearEquivFunOnFintype k _ _).toLinearMap

/-- **The Čech Künneth map for Hodge cohomology is bijective** when `X` and `Y` have affine
diagonal: each of its factors is. -/
theorem bijective_hodgeCechKunnethMap [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsAffineHom (pullback.diagonal (terminal.from Y))] (rs : ℕ × ℕ) :
    Function.Bijective (hodgeCechKunnethMap f g CX CY rs) := by
  simp only [hodgeCechKunnethMap, LinearMap.coe_comp, LinearEquiv.coe_coe]
  refine (bijective_hodgeCechMap _ _ _ _
    (fun _ σ => Stacks.CechKunneth.isAffineOpen_inter_boxOpen_prodCover f g CX CY σ) _).comp
    ((LinearEquiv.bijective _).comp ((Stacks.CechKunneth.bijective_Hmap_of_bijective _ _
      (fun σ => bijective_hodgeKunnethSumMap_app f g _ _
        ((Stacks.CechKunneth.fst_inter_prodCover CX.U CY.U σ).symm ▸ CX.isAffineOpen_inter X _)
        ((Stacks.CechKunneth.snd_inter_prodCover CX.U CY.U σ).symm ▸ CY.isAffineOpen_inter Y _))
      _).comp ((LinearEquiv.bijective _).comp ((LinearEquiv.bijective _).comp
        ((LinearEquiv.bijective _).comp (LinearEquiv.bijective _))))))

/-! ### The cochain of a pair of cocycles -/

section Cochain

attribute [local instance] hasColimits_sheafOfModules_toRingCat
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

open Stacks.Cech.LinearCupProduct (frontIdx backIdx)

variable {I J : Type u} (U : I → X.Opens) (V : J → Y.Opens)

/-- **The Čech cochain of `Ω^{a + c}_{X ×_k Y/k}` attached to Čech cochains `γ` of `Ω^a_{X/k}` and
`ε` of `Ω^c_{Y/k}`**, on the covering `U × V` of `X ×_k Y` by the opens `pr₁⁻¹U_i ∩ pr₂⁻¹V_j`: its
value on the member selected by `σ : Fin (b + d + 1) → I × J` is
`(pr₁^*γ_{σ₀ … σ_b})| ∧ (pr₂^*ε_{σ_b … σ_{b + d}})|`, the wedge product of the pullbacks of the
front `b`-face of `γ` and of the back `d`-face of `ε`, restricted to that member. -/
def hodgeKunnethCochain {a b c d : ℕ}
    (γ : Cochain (hodgeSectionsK f (hodgeScalarsOverField f) a) U b)
    (ε : Cochain (hodgeSectionsK g (hodgeScalarsOverField g) c) V d) :
    Cochain (hodgeSectionsK (pullback.fst f g ≫ f) (hodgeScalarsOverField (pullback.fst f g ≫ f))
      (a + c)) ((boxOpen f g).obj ∘ prodCover U V) (b + d) := fun σ =>
  AlgebraicGeometry.SheafOfModules.formProduct
    (Scheme.Hom.deRhamAlgebras (pullback.fst f g ≫ f)) a c
    (op (inter ((boxOpen f g).obj ∘ prodCover U V) σ))
    ((Scheme.Hom.relativeDifferentialForms (pullback.fst f g ≫ f) (a : ℤ)).presheaf.map
      (homOfLE ((Stacks.CechKunneth.boxOpen_inter_prodCover f g U V σ).ge.trans
        ((Stacks.CechKunneth.boxOpen_le_fst f g _).trans (Scheme.Hom.preimage_mono _
          (Stacks.CechKunneth.fst_inter_prodCover_le U V σ
            (frontIdx b (b + d) (Nat.le_add_right b d))))))).op
      (Scheme.Hom.deRhamBoxLeftPullback f g (a : ℤ) _
        (γ (Prod.fst ∘ σ ∘ frontIdx b (b + d) (Nat.le_add_right b d)))))
    ((Scheme.Hom.relativeDifferentialForms (pullback.fst f g ≫ f) (c : ℤ)).presheaf.map
      (homOfLE ((Stacks.CechKunneth.boxOpen_inter_prodCover f g U V σ).ge.trans
        ((Stacks.CechKunneth.boxOpen_le_snd f g _).trans (Scheme.Hom.preimage_mono _
          (Stacks.CechKunneth.snd_inter_prodCover_le U V σ (backIdx b d (b + d) le_rfl)))))).op
      (Scheme.Hom.deRhamBoxRightPullback f g (c : ℤ) _
        (ε (Prod.snd ∘ σ ∘ backIdx b d (b + d) le_rfl))))

/-- The value of `hodgeKunnethCochain` on `σ`: the wedge product of the restricted pullbacks of
the front face of `γ` and the back face of `ε`. -/
theorem hodgeKunnethCochain_apply {a b c d : ℕ}
    (γ : Cochain (hodgeSectionsK f (hodgeScalarsOverField f) a) U b)
    (ε : Cochain (hodgeSectionsK g (hodgeScalarsOverField g) c) V d)
    (σ : Fin (b + d + 1) → I × J) :
    hodgeKunnethCochain f g U V γ ε σ =
      AlgebraicGeometry.SheafOfModules.formProduct
        (Scheme.Hom.deRhamAlgebras (pullback.fst f g ≫ f)) a c
        (op (inter ((boxOpen f g).obj ∘ prodCover U V) σ))
        ((Scheme.Hom.relativeDifferentialForms (pullback.fst f g ≫ f) (a : ℤ)).presheaf.map
          (homOfLE ((Stacks.CechKunneth.boxOpen_inter_prodCover f g U V σ).ge.trans
            ((Stacks.CechKunneth.boxOpen_le_fst f g _).trans (Scheme.Hom.preimage_mono _
              (Stacks.CechKunneth.fst_inter_prodCover_le U V σ
                (frontIdx b (b + d) (Nat.le_add_right b d))))))).op
          (Scheme.Hom.deRhamBoxLeftPullback f g (a : ℤ) _
            (γ (Prod.fst ∘ σ ∘ frontIdx b (b + d) (Nat.le_add_right b d)))))
        ((Scheme.Hom.relativeDifferentialForms (pullback.fst f g ≫ f) (c : ℤ)).presheaf.map
          (homOfLE ((Stacks.CechKunneth.boxOpen_inter_prodCover f g U V σ).ge.trans
            ((Stacks.CechKunneth.boxOpen_le_snd f g _).trans (Scheme.Hom.preimage_mono _
              (Stacks.CechKunneth.snd_inter_prodCover_le U V σ
                (backIdx b d (b + d) le_rfl)))))).op
          (Scheme.Hom.deRhamBoxRightPullback f g (c : ℤ) _
            (ε (Prod.snd ∘ σ ∘ backIdx b d (b + d) le_rfl)))) :=
  rfl

/-- `hodgeKunnethCochain` is the Alexander–Whitney product `Stacks.CechKunneth.cup` of the two
cochains, included in the summand of index `(a, c)` of `hodgeKunnethSumPresheaf`, carried by the
Künneth map of presheaves `hodgeKunnethSumMap` and transported to the covering
`(boxOpen f g).obj ∘ prodCover U V` along `Stacks.CechKunneth.boxOpen_inter_prodCover`. -/
theorem hodgeKunnethCochain_eq {a b c d : ℕ}
    (γ : Cochain (hodgeSectionsK f (hodgeScalarsOverField f) a) U b)
    (ε : Cochain (hodgeSectionsK g (hodgeScalarsOverField g) c) V d) :
    hodgeKunnethCochain f g U V γ ε =
      transportCochain (boxOpen f g) (hodgeSectionsK (pullback.fst f g ≫ f)
        (hodgeScalarsOverField (pullback.fst f g ≫ f)) (a + c)) (prodCover U V)
        (fun σ => Stacks.CechKunneth.boxOpen_inter_prodCover f g U V σ) (b + d)
        (mapCochain (prodCover U V) (hodgeKunnethSumMap f g (a + c)) (b + d)
          (mapCochain (prodCover U V)
            (presheafDirectSumInc (hodgeKunnethSummand f g (a + c)) ⟨⟨(a, c), rfl⟩⟩) (b + d)
            (cup rfl γ ε))) := by
  funext σ
  have hge := (Stacks.CechKunneth.boxOpen_inter_prodCover f g U V σ).ge
  refine Eq.symm ?_
  refine (congrArg (res (hodgeSectionsK (pullback.fst f g ≫ f)
    (hodgeScalarsOverField (pullback.fst f g ≫ f)) (a + c)) hge)
    (hodgeKunnethSumMapApp_lof f g (a + c) _ ⟨⟨(a, c), rfl⟩⟩
    (cup rfl γ ε σ))).trans ?_
  refine (congrArg (res (hodgeSectionsK (pullback.fst f g ≫ f)
    (hodgeScalarsOverField (pullback.fst f g ≫ f)) (a + c)) hge)
    (kunnethSectionsMap_lof_tmul_eq_app f g (a + c) a c rfl _ _ _
    _)).trans ?_
  refine (Stacks.Tag01VSPullbackTensor.homApp_presheaf_map
    (biproduct.ι (fun i => (Scheme.Hom.deRhamBoxSummand f g (a + c) i).module) ⟨(a, c), rfl⟩ ≫
      (Scheme.Hom.deRhamBoxModuleIso f g (a + c)).hom) (homOfLE hge) _).symm.trans ?_
  refine (congrArg _ ((Stacks.Tag01VSPullbackTensor.externalTensorSection_presheaf_map f g _ _
    _ _ _ _ (hge.trans (Stacks.CechKunneth.boxOpen_le_fst f g _))
    (hge.trans (Stacks.CechKunneth.boxOpen_le_snd f g _)) (homOfLE hge)).trans
    (Stacks.CechKunneth.externalTensorSection_res f g _ _ _ _ _ _ _ _ _))).trans ?_
  have hU := hge.trans ((Stacks.CechKunneth.boxOpen_le_fst f g _).trans
    (Scheme.Hom.preimage_mono _ (Stacks.CechKunneth.fst_inter_prodCover_le U V σ
      (frontIdx b (b + d) (Nat.le_add_right b d)))))
  have hV := hge.trans ((Stacks.CechKunneth.boxOpen_le_snd f g _).trans
    (Scheme.Hom.preimage_mono _ (Stacks.CechKunneth.snd_inter_prodCover_le U V σ
      (backIdx b d (b + d) le_rfl))))
  have e₄ := ConcreteCategory.congr_hom (congrArg (fun ψ => Scheme.Modules.Hom.app ψ
      (inter ((boxOpen f g).obj ∘ prodCover U V) σ))
      (Scheme.Hom.biproduct_ι_comp_deRhamBoxModuleIso_hom f g (a + c) ⟨(a, c), rfl⟩))
    (Stacks.Tag01VSPullbackTensor.externalTensorSection f g
      (Scheme.Hom.relativeDifferentialForms f (a : ℤ))
      (Scheme.Hom.relativeDifferentialForms g (c : ℤ))
      (γ (Prod.fst ∘ σ ∘ frontIdx b (b + d) (Nat.le_add_right b d)))
      (ε (Prod.snd ∘ σ ∘ backIdx b d (b + d) le_rfl))
      (inter ((boxOpen f g).obj ∘ prodCover U V) σ) hU hV)
  have e₅ := congrArg ((eqToHom (congrArg (fun m : ℕ =>
      (Scheme.Hom.deRhamAlgebras (pullback.fst f g ≫ f)).exteriorPower m)
      (rfl : a + c = a + c))).val.app (op (inter ((boxOpen f g).obj ∘ prodCover U V) σ))).hom
    (Scheme.Hom.prodWedgeHom_deRhamBoxSummandIso_inv_externalTensorSection f g (a + c)
      ⟨(a, c), rfl⟩ (γ (Prod.fst ∘ σ ∘ frontIdx b (b + d) (Nat.le_add_right b d)))
      (ε (Prod.snd ∘ σ ∘ backIdx b d (b + d) le_rfl))
      (inter ((boxOpen f g).obj ∘ prodCover U V) σ) hU hV)
  exact e₄.trans e₅

/-- **`hodgeKunnethCochain` of two cocycles is a cocycle.** -/
theorem d_hodgeKunnethCochain {a b c d : ℕ}
    {γ : Cochain (hodgeSectionsK f (hodgeScalarsOverField f) a) U b}
    {ε : Cochain (hodgeSectionsK g (hodgeScalarsOverField g) c) V d}
    (hγ : Stacks.CechKunneth.d _ U b γ = 0) (hε : Stacks.CechKunneth.d _ V d ε = 0) :
    Stacks.CechKunneth.d _ _ (b + d) (hodgeKunnethCochain f g U V γ ε) = 0 := by
  rw [hodgeKunnethCochain_eq, Stacks.CechKunneth.transportCochain_d,
    ← Stacks.CechKunneth.mapCochain_d, ← Stacks.CechKunneth.mapCochain_d,
    Stacks.CechKunneth.d_cup_eq_zero rfl hγ hε, map_zero, map_zero, map_zero]

end Cochain

/-! ### The Čech Künneth map on classes of cocycles -/

/-- `hodgeCechKunnethMap` as the composite of its factors. -/
theorem hodgeCechKunnethMap_apply (rs : ℕ × ℕ)
    (y : DirectSum {x : (ℕ × ℕ) × (ℕ × ℕ) // hodgeBidegreeAdd x = rs} fun x =>
      H (hodgeSectionsK f (hodgeScalarsOverField f) x.1.1.1) CX.U x.1.1.2 ⊗[k]
        H (hodgeSectionsK g (hodgeScalarsOverField g) x.1.2.1) CY.U x.1.2.2) :
    hodgeCechKunnethMap f g CX CY rs y =
      hodgeCechMap (pullback.fst f g ≫ f) rs.1 ((boxOpen f g).obj ∘ prodCover CX.U CY.U)
        (Stacks.CechKunneth.iSup_boxOpen_prodCover f g CX.U CY.U CX.iSup_eq CY.iSup_eq) rs.2
        (transportEquiv (boxOpen f g) (hodgeSectionsK (pullback.fst f g ≫ f)
          (hodgeScalarsOverField (pullback.fst f g ≫ f)) rs.1) (prodCover CX.U CY.U)
          (fun σ => Stacks.CechKunneth.boxOpen_inter_prodCover f g CX.U CY.U σ) rs.2
          (Hmap (prodCover CX.U CY.U) (hodgeKunnethSumMap f g rs.1) rs.2
            ((hodgeKunnethSumEquiv f g CX CY rs.1 rs.2).symm
              (LinearEquiv.piCongrRight (fun ac : ULift.{u} (Idx rs.1) =>
                kunnethEquiv CX.U CY.U (hodgeSectionsK f (hodgeScalarsOverField f) ac.down.1.1)
                  (hodgeSectionsK g (hodgeScalarsOverField g) ac.down.1.2) rs.2)
                (hodgeCechKunnethSourceEquiv f g CX CY rs
                  (DirectSum.linearEquivFunOnFintype k _ _ y)))))) :=
  rfl

/-- The inverse of `hodgeKunnethSumEquiv` is the sum of the maps on Čech cohomology induced by the
inclusions of the summands. -/
theorem hodgeKunnethSumEquiv_symm_apply (r s : ℕ)
    (y : ∀ ac : ULift.{u} (Idx r), H (hodgeKunnethSummand f g r ac) (prodCover CX.U CY.U) s) :
    (hodgeKunnethSumEquiv f g CX CY r s).symm y =
      ∑ ac, Hmap (prodCover CX.U CY.U) (presheafDirectSumInc (hodgeKunnethSummand f g r) ac) s
        (y ac) :=
  rfl

/-- **The middle of the Čech Künneth map on a single summand**: the summand of index
`((a, b), (c, d))` goes to the Alexander–Whitney product `Stacks.CechKunneth.HcupT`, included in
the summand of index `(a, c)` of `hodgeKunnethSumPresheaf`. -/
theorem hodgeKunnethSumEquiv_symm_lof (rs : ℕ × ℕ)
    (x : {x : (ℕ × ℕ) × (ℕ × ℕ) // hodgeBidegreeAdd x = rs})
    (v : H (hodgeSectionsK f (hodgeScalarsOverField f) x.1.1.1) CX.U x.1.1.2 ⊗[k]
      H (hodgeSectionsK g (hodgeScalarsOverField g) x.1.2.1) CY.U x.1.2.2) :
    (hodgeKunnethSumEquiv f g CX CY rs.1 rs.2).symm
        (LinearEquiv.piCongrRight (fun ac : ULift.{u} (Idx rs.1) =>
          kunnethEquiv CX.U CY.U (hodgeSectionsK f (hodgeScalarsOverField f) ac.down.1.1)
            (hodgeSectionsK g (hodgeScalarsOverField g) ac.down.1.2) rs.2)
          (hodgeCechKunnethSourceEquiv f g CX CY rs
            (DirectSum.linearEquivFunOnFintype k _ _ (DirectSum.lof k _ _ x v)))) =
      Hmap (prodCover CX.U CY.U) (presheafDirectSumInc (hodgeKunnethSummand f g rs.1)
          ⟨⟨(x.1.1.1, x.1.2.1), congrArg Prod.fst x.2⟩⟩) rs.2
        (HcupT (congrArg Prod.snd x.2 : x.1.1.2 + x.1.2.2 = rs.2) v) := by
  have h₁ : hodgeCechKunnethSourceEquiv f g CX CY rs
      (DirectSum.linearEquivFunOnFintype k _ _ (DirectSum.lof k _ _ x v)) =
      Pi.single (⟨⟨(x.1.1.1, x.1.2.1), congrArg Prod.fst x.2⟩⟩ : ULift.{u} (Idx rs.1))
        (Pi.single (⟨(x.1.1.2, x.1.2.2), congrArg Prod.snd x.2⟩ : Idx rs.2) v) :=
    hodgeBidegreePiEquiv_single k (fun a b c d => H (hodgeSectionsK f (hodgeScalarsOverField f) a)
      CX.U b ⊗[k] H (hodgeSectionsK g (hodgeScalarsOverField g) c) CY.U d) rs x v
  have h₂ := (Pi.single_op (fun ac : ULift.{u} (Idx rs.1) =>
      ⇑(kunnethEquiv CX.U CY.U (hodgeSectionsK f (hodgeScalarsOverField f) ac.down.1.1)
        (hodgeSectionsK g (hodgeScalarsOverField g) ac.down.1.2) rs.2))
    (fun _ => map_zero _) (⟨⟨(x.1.1.1, x.1.2.1), congrArg Prod.fst x.2⟩⟩ : ULift.{u} (Idx rs.1))
    (Pi.single (⟨(x.1.1.2, x.1.2.2), congrArg Prod.snd x.2⟩ : Idx rs.2) v)).symm
  have h₃ : kunnethEquiv CX.U CY.U (hodgeSectionsK f (hodgeScalarsOverField f) x.1.1.1)
      (hodgeSectionsK g (hodgeScalarsOverField g) x.1.2.1) rs.2
      (Pi.single (⟨(x.1.1.2, x.1.2.2), congrArg Prod.snd x.2⟩ : Idx rs.2) v) =
      HcupT (congrArg Prod.snd x.2 : x.1.1.2 + x.1.2.2 = rs.2) v := by
    change kunnethMap _ _ _ _ rs.2 _ = _
    rw [Stacks.CechKunneth.kunnethMap_apply, Fintype.sum_eq_single
      (⟨(x.1.1.2, x.1.2.2), congrArg Prod.snd x.2⟩ : Idx rs.2) (fun q hq => by
        rw [Pi.single_eq_of_ne hq, map_zero]), Pi.single_eq_same]
  rw [h₁]
  refine (congrArg (hodgeKunnethSumEquiv f g CX CY rs.1 rs.2).symm h₂).trans ?_
  rw [hodgeKunnethSumEquiv_symm_apply, Finset.sum_eq_single
    (⟨⟨(x.1.1.1, x.1.2.1), congrArg Prod.fst x.2⟩⟩ : ULift.{u} (Idx rs.1))
    (fun ac _ hac => by rw [Pi.single_eq_of_ne hac, map_zero])
    (fun h => absurd (Finset.mem_univ _) h), Pi.single_eq_same]
  exact congrArg _ h₃

/-- **The Čech Künneth map on classes of cocycles is the class of the wedge product of the pulled
back cocycles** ([Stacks, Remark 0FWE]): for Čech cocycles `γ` of `Ω^a_{X/k}` on `𝒰` in degree
`b` and `ε` of `Ω^c_{Y/k}` on `𝒱` in degree `d`, the map carries `[γ] ⊗ [ε]`, in the summand of
index `((a, b), (c, d))`, to the class in `H^{b + d}(X ×_k Y, Ω^{a + c})` of the Čech cocycle
`hodgeKunnethCochain`, whose value on `σ` is
`(pr₁^*γ_{σ₀ … σ_b})| ∧ (pr₂^*ε_{σ_b … σ_{b + d}})|`. -/
theorem hodgeCechKunnethMap_lof_tmul_Hmk {a b c d : ℕ}
    (γ : Cochain (hodgeSectionsK f (hodgeScalarsOverField f) a) CX.U b)
    (hγ : Stacks.CechKunneth.d _ CX.U b γ = 0)
    (ε : Cochain (hodgeSectionsK g (hodgeScalarsOverField g) c) CY.U d)
    (hε : Stacks.CechKunneth.d _ CY.U d ε = 0) :
    hodgeCechKunnethMap f g CX CY (hodgeBidegreeAdd ((a, b), (c, d)))
        (DirectSum.lof k
          {x : (ℕ × ℕ) × (ℕ × ℕ) // hodgeBidegreeAdd x = hodgeBidegreeAdd ((a, b), (c, d))}
          (fun x => H (hodgeSectionsK f (hodgeScalarsOverField f) x.1.1.1) CX.U x.1.1.2 ⊗[k]
            H (hodgeSectionsK g (hodgeScalarsOverField g) x.1.2.1) CY.U x.1.2.2)
          ⟨((a, b), (c, d)), rfl⟩ (Hmk _ _ γ hγ ⊗ₜ Hmk _ _ ε hε)) =
      hodgeCechClass (pullback.fst f g ≫ f) ((boxOpen f g).obj ∘ prodCover CX.U CY.U)
        (Stacks.CechKunneth.iSup_boxOpen_prodCover f g CX.U CY.U CX.iSup_eq CY.iSup_eq) (a + c)
        (hodgeKunnethCochain f g CX.U CY.U γ ε)
        ((d_hodgeSectionsK _ _ _ _ _).symm.trans (d_hodgeKunnethCochain f g CX.U CY.U hγ hε)) := by
  have key : ∀ (w z : Cochain (hodgeSectionsK (pullback.fst f g ≫ f)
      (hodgeScalarsOverField (pullback.fst f g ≫ f)) (a + c))
      ((boxOpen f g).obj ∘ prodCover CX.U CY.U) (b + d)) (e : z = w) hw,
      hodgeCechClass (pullback.fst f g ≫ f) ((boxOpen f g).obj ∘ prodCover CX.U CY.U)
        (Stacks.CechKunneth.iSup_boxOpen_prodCover f g CX.U CY.U CX.iSup_eq CY.iSup_eq) (a + c)
        z (e ▸ hw) =
      hodgeCechClass (pullback.fst f g ≫ f) ((boxOpen f g).obj ∘ prodCover CX.U CY.U)
        (Stacks.CechKunneth.iSup_boxOpen_prodCover f g CX.U CY.U CX.iSup_eq CY.iSup_eq) (a + c)
        w hw := by
    rintro w z rfl _
    rfl
  rw [hodgeCechKunnethMap_apply, hodgeKunnethSumEquiv_symm_lof]
  exact key _ _ (hodgeKunnethCochain_eq f g CX.U CY.U γ ε).symm _

end Kunneth

end Stacks.HodgeWeil

end
