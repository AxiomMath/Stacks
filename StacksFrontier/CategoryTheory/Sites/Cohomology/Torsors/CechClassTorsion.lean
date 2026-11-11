module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.CechClassFirstCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.UniverseBridge
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.UniverseLiftTorsorClass

/-!
# A torsor whose class has finite order has a torsion Čech cocycle

Let `(C, J)` be a site, `H` an abelian sheaf on `C`, `U` an object and `𝒰 = {U_i → U}` a covering
family of `U`. Let `F` be a torsor under `H|_U` with a section `s_i` over every member. If the
class of `F` in `H¹(U, H)` (Stacks 03AJ) has finite order, then some nonzero multiple of the
transition cocycle of the `s_i` is a Čech coboundary: there are `n ≠ 0` and sections `t_i` of `H`
over the `U_i` with `n · (s_j - s_i) = t_j - t_i` on every `U_i ×_U U_j`.

The proof is Stacks 0A6G: the class of a torsor trivial over the members of `𝒰` is the image of
its Čech class under the injective group homomorphism `Ȟ¹(𝒰, H) → H¹(U, H)`
(`Stacks.CechSite.torsorIsoClassesEquivH1_eq_cechH1ToSliceH_cechClass`,
`Stacks.CechSite.cechH1ToSliceH_injective`). That comparison is formed with coefficients in a
universe containing the site, so the coefficients are first lifted to that universe: the lift of
`H¹` is an isomorphism of groups which carries the class of `F` to the class of `F` with its
sections lifted (`Stacks.Cohomology.Torsors.sheafHOneAddEquiv_torsorClass`), and the transition
cocycle of the lifted torsor is the lift of the transition cocycle of `F`.

## Main definitions

* `Stacks.Cohomology.Torsors.uliftSectionEquiv`: the sections of the universe lift of an abelian
  sheaf, read as a sheaf of groups, are those of the sheaf.
* `Stacks.Cohomology.Torsors.AbelianTorsor.ulift`: a torsor under `H`, read as a torsor under
  the universe lift of `H` with its sections lifted.

## Main results

* `Stacks.Cohomology.Torsors.exists_nsmul_transitionCochain_eq_of_isOfFinAddOrder`: the
  statement above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.CechSite Stacks.Sheaves.UniverseLift
open Stacks.Cohomology.SiteModules

universe h s t w v u

namespace Stacks.Cohomology.Torsors

section ULift

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The sections of the universe lift of an abelian sheaf, read as a sheaf of groups, are the
sections of the sheaf: lowering the universe is multiplicative and natural. -/
def uliftSectionEquiv (H : Sheaf J AddCommGrpCat.{t}) :
    SheafOfGroups.SectionEquiv (abelianSheafAsGroupSheaf ((uliftSheafFunctor.{s, t} J).obj H))
      (abelianSheafAsGroupSheaf H) where
  equiv _ := Equiv.ulift
  map_mul _ _ _ := rfl
  naturality _ _ := rfl

/-- A torsor under an abelian sheaf `H`, read as a torsor under the universe lift of `H`, with
its sections lifted to the larger universe. -/
def AbelianTorsor.ulift {H : Sheaf J AddCommGrpCat.{t}} (F : AbelianTorsor H) :
    AbelianTorsor ((uliftSheafFunctor.{s, t} J).obj H) :=
  ⟨F.1.bridge.{s} (uliftSectionEquiv.{s} H), F.1.bridge_isTorsor (uliftSectionEquiv.{s} H) F.2⟩

/-- The difference of two lifted sections of the lifted torsor is the lift of their
difference. -/
lemma torsorDifference_ulift {H : Sheaf J AddCommGrpCat.{t}} (F : AbelianTorsor H) (V : Cᵒᵖ)
    (x y : F.1.presheaf.obj V) :
    torsorDifference _ (F.ulift.{s}) V (ULift.up x) (ULift.up y) =
      ULift.up (torsorDifference H F V x y) :=
  torsorDifference_eq_of_act _ _ V _ _ _
    (congrArg ULift.up (torsorDifference_act H F V x y))

end ULift

section Torsion

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {U : C}
  (E : PreZeroHypercover.{w} U)
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]
  (H : Sheaf J AddCommGrpCat.{t})
  [HasSheafify (J.over U) AddCommGrpCat.{t}] [HasExt.{h} (Sheaf (J.over U) AddCommGrpCat.{t})]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{t}]

/-- **A torsor whose class has finite order has a torsion Čech cocycle.** Let `F` be a torsor
under `H|_U` with sections `s_i` over the members of a covering family `𝒰` of `U`. If the class
of `F` in `H¹(U, H)` (Stacks 03AJ) has finite order, then there are `n ≠ 0` and sections `t_i`
of `H` over the members such that `n` times the transition cocycle of the `s_i` is the Čech
coboundary of the `t_i`. This is Stacks 0A6G, the injectivity of the group homomorphism
`Ȟ¹(𝒰, H) → H¹(U, H)` through which the class of a torsor trivial on `𝒰` factors, read after
lifting the coefficients to a universe containing the site. -/
theorem exists_nsmul_transitionCochain_eq_of_isOfFinAddOrder (hE : E.sieve₀ ∈ J U)
    (F : AbelianTorsor (H.over U)) (σ : ∀ i, F.1.presheaf.obj (op (Over.mk (E.f i))))
    (hF : IsOfFinAddOrder (torsorIsoClassesEquivH1.{h} (H.over U)
      (Quotient.mk (torsorSetoid (H.over U)) F))) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ τ : ∀ i, H.obj.obj (op (E.X i)), ∀ k : Fin 2 → E.I₀,
      n • transitionCochain E H F σ k =
        H.obj.map (Pi.π (fun j ↦ Over.mk (E.f (k j))) 1).left.op (τ (k 1)) -
          H.obj.map (Pi.π (fun j ↦ Over.mk (E.f (k j))) 0).left.op (τ (k 0)) := by
  let : HasSheafify J AddCommGrpCat.{max t u v w} :=
    site_hasSheafify_addCommGrp.{u, v, max t w}
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max t u v w} :=
    site_wEqualsLocallyBijective_addCommGrp.{u, v, max t w}
  let : EnoughInjectives (Sheaf J AddCommGrpCat.{max t u v w}) :=
    CategoryTheory.Sheaf.enoughInjectives_addCommGrpCat_max.{max t w, v, u} J
  let : HasSheafify (J.over U) AddCommGrpCat.{max t u v w} :=
    site_hasSheafify_addCommGrp.{max u v, v, max t w}
  let : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max t u v w} :=
    site_wEqualsLocallyBijective_addCommGrp.{max u v, v, max t w}
  let : EnoughInjectives (Sheaf (J.over U) AddCommGrpCat.{max t u v w}) :=
    CategoryTheory.Sheaf.enoughInjectives_addCommGrpCat_max.{max t w, v, max u v} (J.over U)
  let : HasExt.{max t u v w} (Sheaf (J.over U) AddCommGrpCat.{max t u v w}) :=
    hasExt_of_enoughInjectives _
  let : HasExt.{max t u v w} (Sheaf J AddCommGrpCat.{max t u v w}) :=
    hasExt_of_enoughInjectives _
  let H' : Sheaf J AddCommGrpCat.{max t u v w} := (uliftSheafFunctor.{max u v w, t} J).obj H
  let F' : AbelianTorsor (H'.over U) := F.ulift.{max u v w}
  let σ' : ∀ i, F'.1.presheaf.obj (op (Over.mk (E.f i))) := fun i ↦ ULift.up (σ i)
  have hσ' : ∀ i, Nonempty (F'.1.presheaf.obj (op (Over.mk (E.f i)))) := fun i ↦ ⟨σ' i⟩
  -- The class of the lifted torsor is the image of the class of `F` under the lift of `H¹`.
  have hlift := sheafHOneAddEquiv_torsorClass.{h, max t u v w, max u v w, t, v, max u v}
    (J.over U) (H.over U) F F' (𝟙 _) (fun _ ↦ Function.bijective_id) (fun _ _ _ ↦ rfl)
  -- It is the image of the Čech class under `Ȟ¹(𝒰, H') → H¹(U, H')`.
  have hcech := torsorIsoClassesEquivH1_eq_cechH1ToSliceH_cechClass.{t} J E hE H'
    ⟨Quotient.mk (torsorSetoid (H'.over U)) F', F', rfl, hσ'⟩
  rw [cechClass_mk E H' F' hσ' σ'] at hcech
  obtain ⟨n, hn, hnF⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 hF
  have hz : n • cls E H'.obj (transitionCocycle E H' F' σ') = 0 := by
    refine cechH1ToSliceH_injective.{t} J E hE H' ?_
    rw [map_nsmul, map_zero, ← hcech]
    change n • torsorIsoClassesEquivH1 (((uliftSheafFunctor.{max u v w, t} (J.over U)).obj
      (H.over U))) (Quotient.mk _ F') = 0
    rw [← hlift, ← map_nsmul, hnF, map_zero]
  rw [cls, ← QuotientAddGroup.mk_nsmul] at hz
  obtain ⟨τ', hτ'⟩ := (cls_eq_zero_iff E H'.obj _).1 hz
  refine ⟨n, hn.ne', fun i ↦ (cochainFam E H'.obj τ' i).down, fun k ↦ ?_⟩
  have hk := congrFun hτ' k
  rw [← famCochain_cochainFam E H'.obj τ', cechDifferential_zero_famCochain] at hk
  have hdown := congrArg ULift.down hk
  refine Eq.trans ?_ hdown.symm
  change n • transitionCochain E H F σ k =
    (n • transitionCochain E H' F' σ' k).down
  rw [show (n • transitionCochain E H' F' σ' k).down =
    n • (transitionCochain E H' F' σ' k).down from rfl]
  congr 1
  exact (congrArg ULift.down (torsorDifference_ulift.{max u v w} F _ _ _)).symm

/-- **A torsor whose class has finite order has torsion differences of local sections**, in the
form valid over every object of `C/U` with two morphisms to members of the covering family: there
are `n ≠ 0` and sections `t_i` of `H` over the members with
`n · (b^* s_j - a^* s_i) = b^* t_j - a^* t_i` for all `a : W ⟶ U_i`, `b : W ⟶ U_j` over `U`. -/
theorem exists_nsmul_torsorDifference_eq_of_isOfFinAddOrder (hE : E.sieve₀ ∈ J U)
    (F : AbelianTorsor (H.over U)) (σ : ∀ i, F.1.presheaf.obj (op (Over.mk (E.f i))))
    (hF : IsOfFinAddOrder (torsorIsoClassesEquivH1.{h} (H.over U)
      (Quotient.mk (torsorSetoid (H.over U)) F))) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ τ : ∀ i, H.obj.obj (op (E.X i)), ∀ ⦃W : Over U⦄ ⦃i j : E.I₀⦄
      (a : W ⟶ Over.mk (E.f i)) (b : W ⟶ Over.mk (E.f j)),
      n • torsorDifference (H.over U) F (op W) (F.1.presheaf.map b.op (σ j))
          (F.1.presheaf.map a.op (σ i)) =
        H.obj.map b.left.op (τ j) - H.obj.map a.left.op (τ i) := by
  obtain ⟨n, hn, τ, hτ⟩ := exists_nsmul_transitionCochain_eq_of_isOfFinAddOrder E H hE F σ hF
  refine ⟨n, hn, τ, fun W i j a b ↦ ?_⟩
  let k : Fin 2 → E.I₀ := ![i, j]
  let u : W ⟶ (∏ᶜ fun m ↦ Over.mk (E.f (k m))) :=
    Pi.lift (fun m ↦ match m with | 0 => a | 1 => b)
  have h0 : u ≫ Pi.π (fun m ↦ Over.mk (E.f (k m))) 0 = a := Pi.lift_comp_π _ _
  have h1 : u ≫ Pi.π (fun m ↦ Over.mk (E.f (k m))) 1 = b := Pi.lift_comp_π _ _
  have e := map_transitionCochain_comp E H F σ k u
  rw [h0, h1] at e
  have e' := congrArg (H.obj.map u.left.op) (hτ k)
  rw [map_nsmul, e, map_sub, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, ← Over.comp_left,
    ← Over.comp_left, h0, h1] at e'
  exact e'

end Torsion

end Stacks.Cohomology.Torsors

end
