module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.AffineLineKummerGenerator
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.StalkwiseCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleZariskiCohomology
public import StacksFrontier.CategoryTheory.Sites.Point.ConstantSheafFiber
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom

/-!
# The Kummer generator property at sheaf level

Let `F` be an abelian sheaf on the small étale site of a scheme `S` and `s` a global section of
`F` killed by `N`. Then `s` is the image of `1` under a unique morphism `σ_s : ℤ/N ⟶ F` out of
the constant sheaf `ℤ/N` (`Stacks.EtaleCohomology.Purity.torsionSectionSheafHom`), and on the
stalk at a geometric point `x` the morphism `σ_s` is `n ↦ n • s_x`
(`Stacks.EtaleCohomology.Purity.stalk_torsionSectionSheafHom_apply`).

So the statement "the germ of `s` generates the stalk of `F` freely over `ℤ/N`" is the statement
that `σ_s` is an isomorphism on that stalk
(`Stacks.EtaleCohomology.Purity.isIso_stalk_torsionSectionSheafHom_iff`). In this sheaf-level form
it is transported along inverse images with no germ computation: the stalk of `f⁻¹ σ` at `x` is
the stalk of `σ` at `f ∘ x`, naturally in `σ`
(`Stacks.EtaleCohomology.smallEtalePullbackStalkAbIso`), so a commutative square
`f⁻¹ σ ≫ β = e ≫ σ'` with `e`, `β` invertible on stalks carries the property from `σ` to `σ'`
(`Stacks.EtaleCohomology.Purity.IsIsoStalksOver.of_pullback`).

The Kummer class `∂ t` of a local equation is killed by `N`
(`Stacks.EtaleCohomology.Purity.nsmul_localKummerClass`), and the germ-form generator property of
the coordinate of `𝔸¹_k` (`Stacks.EtaleCohomology.Purity.AffineLineKummerGenerator`) is the
sheaf-level property of `σ_{∂ t}` over the origin
(`Stacks.EtaleCohomology.Purity.isIsoStalksOver_affineLine_of_affineLineKummerGenerator`).

## Main definitions

* `Stacks.EtaleCohomology.Purity.torsionConstantSheaf`: the constant abelian sheaf `ℤ/N`.
* `Stacks.EtaleCohomology.Purity.torsionSectionSheafHom`: the morphism `σ_s : ℤ/N ⟶ F`.
* `Stacks.EtaleCohomology.Purity.IsIsoStalksOver`: a morphism of abelian sheaves is invertible
  on the stalks at the geometric points over a subset.

## Main results

* `Stacks.EtaleCohomology.Purity.isIso_stalk_torsionSectionSheafHom_iff`.
* `Stacks.EtaleCohomology.Purity.IsIsoStalksOver.of_pullback`.
* `Stacks.EtaleCohomology.Purity.isIsoStalksOver_affineLine_of_affineLineKummerGenerator`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

universe w u

namespace Stacks.EtaleCohomology.Purity

section SectionMap

variable (S : Scheme.{u}) (N : ℕ)

/-- **The constant abelian sheaf `ℤ/N`** on the small étale site of `S`. -/
abbrev torsionConstantSheaf : Sheaf (smallEtaleTopology S) Ab.{u + 1} :=
  (constantSheaf (smallEtaleTopology S) Ab.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod N)))

variable {S N} [NeZero N] {F : Sheaf (smallEtaleTopology S) Ab.{u + 1}}

/-- The additive map `ℤ ⟶ Γ(S, F)`, `n ↦ n • s`, which kills `N` when `N • s = 0`. -/
def torsionSectionLift (s : ToType (F.obj.obj (op ((opensToEtale S).obj ⊤))))
    (hs : N • s = 0) : {f : ℤ →+ ToType (F.obj.obj (op ((opensToEtale S).obj ⊤))) // f N = 0} :=
  ⟨zmultiplesHom _ s, by rw [zmultiplesHom_apply, natCast_zsmul, hs]⟩

/-- The additive map `ℤ/N ⟶ Γ(S, F)`, `n ↦ n • s`, for a global section `s` killed by `N`. -/
def torsionSectionHom (s : ToType (F.obj.obj (op ((opensToEtale S).obj ⊤)))) (hs : N • s = 0) :
    AddCommGrpCat.of (ULift.{u + 1} (ZMod N)) ⟶ F.obj.obj (op ((opensToEtale S).obj ⊤)) :=
  AddCommGrpCat.ofHom ((ZMod.lift N (torsionSectionLift s hs)).comp
    AddEquiv.ulift.toAddMonoidHom)

/-- The map `torsionSectionHom s hs` sends `n : ℤ/N` to `n.val • s`. -/
theorem torsionSectionHom_apply (s : ToType (F.obj.obj (op ((opensToEtale S).obj ⊤))))
    (hs : N • s = 0) (n : ZMod N) :
    torsionSectionHom s hs (ULift.up n) = n.val • s := by
  show ZMod.lift N (torsionSectionLift s hs) n = n.val • s
  have h := (ZMod.lift_coe N (torsionSectionLift s hs) n.val).trans
    (zmultiplesHom_apply _ s n.val)
  rwa [Int.cast_natCast, ZMod.natCast_zmod_val, natCast_zsmul] at h

/-- **The morphism `σ_s : ℤ/N ⟶ F` of a global section `s` killed by `N`**, sending `1` to `s`. -/
def torsionSectionSheafHom (s : ToType (F.obj.obj (op ((opensToEtale S).obj ⊤))))
    (hs : N • s = 0) : torsionConstantSheaf S N ⟶ F :=
  ((constantSheafAdj (smallEtaleTopology S) Ab.{u + 1}
    (isTerminal_opensToEtale_top S)).homEquiv _ _).symm (torsionSectionHom s hs)

omit [NeZero N] in
/-- On global sections, the composite of the sheafification map of the constant presheaf `ℤ/N`
with `torsionSectionSheafHom s hs` is `torsionSectionHom s hs`. -/
theorem toSheafify_app_comp_torsionSectionSheafHom
    (s : ToType (F.obj.obj (op ((opensToEtale S).obj ⊤)))) (hs : N • s = 0) :
    (toSheafify (smallEtaleTopology S)
        ((Functor.const _).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))))).app
        (op ((opensToEtale S).obj ⊤)) ≫
      (torsionSectionSheafHom s hs).hom.app (op ((opensToEtale S).obj ⊤)) =
    torsionSectionHom s hs := by
  rw [← Stacks.ConstantSheaf.constantSheafAdj_homEquiv_apply (smallEtaleTopology S) Ab.{u + 1}
    (isTerminal_opensToEtale_top S), torsionSectionSheafHom, Equiv.apply_symm_apply]

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ S)

/-- **On the stalk at a geometric point, `σ_s` is `n ↦ n • s_x`**, the stalk of `ℤ/N` being
identified with `ℤ/N` (`CategoryTheory.Sites.constantSheafFiberIso`). -/
theorem stalk_torsionSectionSheafHom_apply
    (s : ToType (F.obj.obj (op ((opensToEtale S).obj ⊤)))) (hs : N • s = 0)
    (y : (Scheme.pointSmallEtale x).fiber.obj ((opensToEtale S).obj ⊤)) (n : ZMod N) :
    (smallEtaleStalkAb x).map (torsionSectionSheafHom s hs)
        ((CategoryTheory.Sites.constantSheafFiberIso (Scheme.pointSmallEtale x)
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod N)))).inv (ULift.up n)) =
      n.val • (Scheme.pointSmallEtale x).toPresheafFiber ((opensToEtale S).obj ⊤) y F.obj s := by
  have h1 := CategoryTheory.Sites.constantSheafFiberIso_toSheafify_app
    (J := smallEtaleTopology S) (Scheme.pointSmallEtale x)
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))) ((opensToEtale S).obj ⊤) y (ULift.up n)
  set c := (toSheafify (smallEtaleTopology S)
    ((Functor.const _).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))))).app
    (op ((opensToEtale S).obj ⊤)) (ULift.up n)
  have h2 : (CategoryTheory.Sites.constantSheafFiberIso (Scheme.pointSmallEtale x)
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod N)))).inv (ULift.up n) =
      (Scheme.pointSmallEtale x).toPresheafFiber ((opensToEtale S).obj ⊤) y
        (torsionConstantSheaf S N).obj c := by
    refine (congrArg _ h1.symm).trans ?_
    simp only [Iso.hom_inv_id_apply]
    rfl
  rw [h2]
  refine (ConcreteCategory.congr_hom ((Scheme.pointSmallEtale x).toPresheafFiber_naturality
    (torsionSectionSheafHom s hs).hom ((opensToEtale S).obj ⊤) y) c).trans ?_
  have h5 : (torsionSectionSheafHom s hs).hom.app (op ((opensToEtale S).obj ⊤)) c = n.val • s :=
    (ConcreteCategory.congr_hom (toSheafify_app_comp_torsionSectionSheafHom s hs)
      (ULift.up n)).trans (torsionSectionHom_apply s hs n)
  exact (congrArg (ConcreteCategory.hom ((Scheme.pointSmallEtale x).toPresheafFiber
    ((opensToEtale S).obj ⊤) y F.obj)) h5).trans (map_nsmul _ _ _)

/-- **The germ of `s` generates the stalk freely over `ℤ/N` if and only if `σ_s` is an
isomorphism on that stalk.** -/
theorem isIso_stalk_torsionSectionSheafHom_iff
    (s : ToType (F.obj.obj (op ((opensToEtale S).obj ⊤)))) (hs : N • s = 0)
    (y : (Scheme.pointSmallEtale x).fiber.obj ((opensToEtale S).obj ⊤)) :
    IsIso ((smallEtaleStalkAb x).map (torsionSectionSheafHom s hs)) ↔
      Function.Bijective (fun n : ZMod N => n.val •
        (Scheme.pointSmallEtale x).toPresheafFiber ((opensToEtale S).obj ⊤) y F.obj s) := by
  let e := CategoryTheory.Sites.constantSheafFiberIso (Scheme.pointSmallEtale x)
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod N)))
  have he : Function.Bijective (fun n : ZMod N => e.inv (ULift.up n)) :=
    ((ConcreteCategory.bijective_of_isIso e.inv).comp Equiv.ulift.symm.bijective)
  have hfun : (fun n : ZMod N => n.val •
      (Scheme.pointSmallEtale x).toPresheafFiber ((opensToEtale S).obj ⊤) y F.obj s) =
      (smallEtaleStalkAb x).map (torsionSectionSheafHom s hs) ∘
        (fun n : ZMod N => e.inv (ULift.up n)) :=
    funext fun n => (stalk_torsionSectionSheafHom_apply x s hs y n).symm
  rw [hfun]
  exact (ConcreteCategory.isIso_iff_bijective _).trans (Function.Bijective.of_comp_iff _ he).symm

end SectionMap

section Stalks

/-- **A morphism of abelian étale sheaves is invertible on the stalks over a subset `T`**: its
stalk at every geometric point lying over `T` is an isomorphism. -/
def IsIsoStalksOver {S : Scheme.{u}} (T : Set S) {A B : Sheaf (smallEtaleTopology S) Ab.{u + 1}}
    (σ : A ⟶ B) : Prop :=
  ∀ {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ S), Set.range x.base ⊆ T →
    IsIso ((smallEtaleStalkAb x).map σ)

/-- **The stalk-isomorphism property transports along inverse images.** If
`f⁻¹ σ ≫ β = e ≫ σ'` with `e` and `β` invertible on the stalks over `T'`, and `σ` is invertible
on the stalks over `T ⊇ f(T')`, then `σ'` is invertible on the stalks over `T'`: the stalk of
`f⁻¹ σ` at `x` is the stalk of `σ` at `f ∘ x`, naturally in `σ`. -/
theorem IsIsoStalksOver.of_pullback {X S : Scheme.{u}} (f : X ⟶ S) {T : Set S} {T' : Set X}
    (hT : f.base '' T' ⊆ T) {A B : Sheaf (smallEtaleTopology S) Ab.{u + 1}}
    {A' B' : Sheaf (smallEtaleTopology X) Ab.{u + 1}} {σ : A ⟶ B} {σ' : A' ⟶ B'}
    (e : (smallEtalePullbackAb f).obj A ⟶ A') (β : (smallEtalePullbackAb f).obj B ⟶ B')
    (h : (smallEtalePullbackAb f).map σ ≫ β = e ≫ σ') (hσ : IsIsoStalksOver T σ)
    (he : IsIsoStalksOver T' e) (hβ : IsIsoStalksOver T' β) : IsIsoStalksOver T' σ' := by
  intro Ω _ _ x hx
  have hfx : Set.range (x ≫ f).base ⊆ T := by
    rintro _ ⟨p, rfl⟩
    exact hT ⟨x.base p, hx ⟨p, rfl⟩, rfl⟩
  have := he x hx
  have := hβ x hx
  have : IsIso ((smallEtaleStalkAb x).map ((smallEtalePullbackAb f).map σ)) :=
    (NatIso.isIso_map_iff (smallEtalePullbackStalkAbIso f x) σ).2 (hσ (x ≫ f) hfx)
  have hc := congrArg (smallEtaleStalkAb x).map h
  rw [Functor.map_comp, Functor.map_comp] at hc
  exact IsIso.of_isIso_fac_left hc.symm

end Stalks

section Kummer

open Stacks.Kummer

variable {U₀ U : Scheme.{u}} (j : U₀ ⟶ U)
  [HasDerivedCategory.{w} (Sheaf (smallEtaleTopology U₀) Ab.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallEtaleTopology U) Ab.{u + 1})] {N : ℕ}
  (hN0 : N ≠ 0) (hN : IsUnit ((N : ℕ) : Γ(U₀, ⊤)))

/-- **`N` kills the Kummer coboundary** `∂ : j_* 𝐆_m ⟶ R¹ j_* μ_N`, since `∂` kills the `N`-th
powers. -/
theorem nsmul_kummerDirectImageδ : N • kummerDirectImageδ j hN0 hN = 0 := by
  have h := map_powMap_comp_kummerDirectImageδ j hN0 hN
  rwa [powMap, Functor.map_nsmul, CategoryTheory.Functor.map_id, Preadditive.nsmul_comp,
    Category.id_comp] at h

/-- **`N` kills the local Kummer classes.** -/
theorem nsmul_localKummerClass (V : U.Opens) (t : Γ(U, V))
    (ht : IsUnit (puncturedFunction j V t)) : N • localKummerClass j hN0 hN V t ht = 0 := by
  exact congrArg (fun φ : _ ⟶ kummerTarget j N =>
      ConcreteCategory.hom (φ.hom.app (op ((opensToEtale U).obj V)))
        (ofUnit.{u, 0} (X := U₀) (U := puncturedOpen j V) ht.unit))
    (nsmul_kummerDirectImageδ j hN0 hN)

end Kummer

section AffineLine

attribute [local instance] HasDerivedCategory.standard

/-- **The Kummer generator of `𝔸¹_k`, at sheaf level**: under
`Stacks.EtaleCohomology.Purity.AffineLineKummerGenerator k`, the morphism
`σ_{∂ t} : ℤ/N ⟶ R¹ j_* μ_N` of the Kummer class of the coordinate is invertible on the stalks
over the origin. -/
theorem isIsoStalksOver_affineLine_of_affineLineKummerGenerator (k : Type u) [Field k]
    (hgen : AffineLineKummerGenerator k) (N : ℕ) (hN0 : N ≠ 0)
    (hN : IsUnit ((N : ℕ) : Γ((punctured k).toScheme, ⊤)))
    (ht : IsUnit (puncturedFunction (punctured k).ι ⊤ (coordinate k))) :
    haveI : NeZero N := ⟨hN0⟩
    IsIsoStalksOver ((punctured k : Set (affineLine k)))ᶜ
      (torsionSectionSheafHom (localKummerClass (punctured k).ι hN0 hN ⊤ (coordinate k) ht)
        (nsmul_localKummerClass (punctured k).ι hN0 hN ⊤ (coordinate k) ht)) := by
  have : NeZero N := ⟨hN0⟩
  intro Ω _ _ x hx
  let y : (Scheme.pointSmallEtale x).fiber.obj ((opensToEtale (affineLine k)).obj ⊤) :=
    (Scheme.pointSmallEtale x).fiber.map
      ((isTerminal_opensToEtale_top (affineLine k)).from (Scheme.Etale.mk (𝟙 (affineLine k))))
      (Over.homMk x (by simp))
  exact (isIso_stalk_torsionSectionSheafHom_iff x _ _ y).2 (hgen N hN0 hN ht x hx y)

end AffineLine

end Stacks.EtaleCohomology.Purity

end
