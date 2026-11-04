module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.Sheaves.LocallySurjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZero

/-!
# Covering a sheaf of modules by extensions by zero of the structure sheaf

Let `(X, 𝒪)` be a topological space with a sheaf of rings. Every sheaf of `𝒪`-modules is a
quotient of a direct sum of extensions by zero `j_! (𝒪|_U)` of the structure sheaf along the
inclusions of open subsets.

The cover is explicit: index the sum by all pairs consisting of an open set `U` and a section
of the module over `U`, and let the summand `j_! (𝒪|_U)` map to the module by the adjoint
transpose of the morphism `𝒪|_U ⟶ (F|_U)` picking out that section. The resulting map is
surjective on sections locally, hence an epimorphism.

## Main results

* `Stacks.SheafOfModules.exists_epi_from_coproduct_jShriek_unit`: the explicit form of the
  cover.

## Implementation notes

The direct sum is the categorical coproduct, and surjectivity of the cover is expressed by
`Epi`, which for sheaves of modules is local surjectivity of the underlying morphism of
presheaves of abelian groups. The space, the ring sheaf and the modules share one universe,
as required by the extension-by-zero API.

## References

* [Stacks Project, Tag 05NI](https://stacks.math.columbia.edu/tag/05NI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

attribute [local implicit_reducible] CategoryTheory.Functor.sheafPushforwardContinuous

universe u

namespace Stacks.SheafOfModules

/-- Sheafification of presheaves of abelian groups on the opens of `X` exists. -/
noncomputable local instance (X : TopCat.{u}) :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite _ _

/-- On the opens of `X`, a morphism of presheaves of abelian groups becomes an isomorphism after
sheafification exactly when it is locally bijective. -/
noncomputable local instance (X : TopCat.{u}) :
    (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  (F : _root_.SheafOfModules.{u} O)

/-- **Stacks 05NI, part (1).** Every sheaf of modules is a quotient of a coproduct of extensions
by zero of structure sheaves on open subspaces. -/
@[stacks 05NI "part (1)"]
theorem exists_epi_from_coproduct_jShriek_unit :
    ∃ (I : Type u) (U : I → Opens X),
      ∃ f : (∐ fun i : I =>
        (ExtensionByZeroModules.jShriek (U i) O).obj
          (_root_.SheafOfModules.unit (ExtensionByZeroModules.resRing (U i) O))) ⟶ F,
        Epi f := by
  classical
  let R := O
  let I := Σ U : Opens X, F.val.obj (op U)
  let S : I → _root_.SheafOfModules.{u} R := fun i =>
    (ExtensionByZeroModules.jShriek i.1 R).obj
      (_root_.SheafOfModules.unit (ExtensionByZeroModules.resRing i.1 R))
  let r : (i : I) → ((ExtensionByZeroModules.jStar i.1 R).obj F).sections := fun i => by
    refine ((ExtensionByZeroModules.jStar i.1 R).obj F).val.sectionsMk
      (fun V => ?_) (fun {V W} hVW => ?_)
    · show F.val.obj (op ((TopCat.Presheaf.imF i.1).obj V.unop))
      exact F.val.map (homOfLE (ExtensionByZeroModules.imF_le i.1 V.unop)).op i.2
    · let s : F.val.presheaf.obj (op i.1) := i.2
      show (F.val.presheaf.map ((TopCat.Presheaf.imF i.1).map hVW.unop).op)
        (F.val.presheaf.map
          (homOfLE (ExtensionByZeroModules.imF_le i.1 V.unop)).op s) =
        F.val.presheaf.map
          (homOfLE (ExtensionByZeroModules.imF_le i.1 W.unop)).op s
      rw [← ConcreteCategory.comp_apply, ← F.val.presheaf.map_comp]
      congr 1
  let g : (i : I) → S i ⟶ F := fun i => by
    let adj := ExtensionByZeroModules.jShriekAdjunction i.1 R
    exact (adj.homEquiv
      (_root_.SheafOfModules.unit (ExtensionByZeroModules.resRing i.1 R)) F).symm
      (((ExtensionByZeroModules.jStar i.1 R).obj F).unitHomEquiv.symm (r i))
  let P : _root_.SheafOfModules.{u} R := ∐ S
  let f : P ⟶ F := Cofan.IsColimit.desc (coproductIsCoproduct S) g
  refine ⟨I, fun i => i.1, f, ?_⟩
  have hlocal : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf R.obj).map f.val) := by
    show TopCat.Presheaf.IsLocallySurjective
      ((PresheafOfModules.toPresheaf R.obj).map ((_root_.SheafOfModules.forget R).map f))
    rw [TopCat.Presheaf.isLocallySurjective_iff]
    intro U t x hx
    let tM : F.val.obj (op U) := t
    let i : I := ⟨U, tM⟩
    let adj := ExtensionByZeroModules.jShriekAdjunction U R
    let E := (ExtensionByZeroModules.jShriek U R).obj
      (_root_.SheafOfModules.unit (ExtensionByZeroModules.resRing U R))
    let η := adj.unit.app (_root_.SheafOfModules.unit (ExtensionByZeroModules.resRing U R))
    let V : Opens X := (TopCat.Presheaf.imF U).obj ⊤
    have htop : V = U := by ext x; simp [V]
    let z0 : E.val.obj (op V) := by
      show ((ExtensionByZeroModules.jStar U R).obj E).val.obj (op ⊤)
      exact (η.val.app (op ⊤)).hom
        (1 : (ExtensionByZeroModules.resRing U R).obj.obj (op ⊤))
    have hAdj : η ≫ (ExtensionByZeroModules.jStar U R).map (g i) =
        ((ExtensionByZeroModules.jStar U R).obj F).unitHomEquiv.symm (r i) := by
      calc
        η ≫ (ExtensionByZeroModules.jStar U R).map (g i) =
            adj.homEquiv _ _ (g i) := by
              simpa [i, η] using (adj.homEquiv_unit (f := g i)).symm
        _ = ((ExtensionByZeroModules.jStar U R).obj F).unitHomEquiv.symm (r i) := by
          dsimp [g, i]
          exact Equiv.apply_symm_apply _ _
    let m : F.val.obj (op V) :=
      F.val.map (homOfLE (ExtensionByZeroModules.imF_le U ⊤)).op i.2
    have hgen : ((g i).val.app (op V)).hom z0 =
        TopCat.Presheaf.restrictOpen t V (ExtensionByZeroModules.imF_le U ⊤) := by
      let one : ↑((_root_.SheafOfModules.unit (ExtensionByZeroModules.resRing U R)).val.obj
          (op ⊤)) := (1 : (ExtensionByZeroModules.resRing U R).obj.obj (op ⊤))
      have h := congrArg (fun q => (q.val.app (op ⊤)).hom one) hAdj
      have hunit : ((((ExtensionByZeroModules.jStar U R).obj F).unitHomEquiv.symm
          (r i)).val.app (op ⊤)).hom
          (1 : (ExtensionByZeroModules.resRing U R).obj.obj (op ⊤)) =
          (r i).eval (op ⊤) := by
        rw [← _root_.SheafOfModules.unitHomEquiv_apply_coe]
        exact congrArg
          (fun s : ((ExtensionByZeroModules.jStar U R).obj F).sections => s.eval (op ⊤))
          (Equiv.apply_symm_apply _ _)
      have hr : (r i).eval (op ⊤) = m := by
        dsimp [PresheafOfModules.sections.eval, r, i,
          ExtensionByZeroModules.jStar, _root_.SheafOfModules.pushforward]
        show m = m
        rfl
      have h' := h.trans hunit
      rw [hr] at h'
      change ((η.val.app (op ⊤) ≫
        ((ExtensionByZeroModules.jStar U R).map (g i)).val.app (op ⊤)).hom one =
        m) at h'
      rw [ModuleCat.comp_apply] at h'
      dsimp only [ExtensionByZeroModules.jStar] at h'
      rw [_root_.SheafOfModules.pushforward_map_val] at h'
      dsimp [PresheafOfModules.pushforward, PresheafOfModules.pushforward₀,
        ModuleCat.restrictScalars, ModuleCat.RestrictScalars.map'] at h'
      change ((g i).val.app (op V)).hom
        ((η.val.app (op ⊤)).hom one) = m at h'
      have hzeta : (η.val.app (op ⊤)).hom one = z0 := rfl
      rw [hzeta] at h'
      have hm : m =
          TopCat.Presheaf.restrictOpen t V (ExtensionByZeroModules.imF_le U ⊤) := by
        show (F.val.map (homOfLE (ExtensionByZeroModules.imF_le U ⊤)).op).hom i.2 =
          TopCat.Presheaf.restrictOpen t V (ExtensionByZeroModules.imF_le U ⊤)
        rw [← PresheafOfModules.presheaf_map_apply_coe]
        have hit : (i.2 : F.val.presheaf.obj (op U)) = t := rfl
        simpa [TopCat.Presheaf.restrictOpen, hit]
      exact h'.trans hm
    let ι : E ⟶ P := Sigma.ι S i
    let zG : ToType (((PresheafOfModules.toPresheaf R.obj).obj
        ((_root_.SheafOfModules.forget R).obj E)).obj (op V)) := z0
    let v := ((PresheafOfModules.toPresheaf R.obj).map
      ((_root_.SheafOfModules.forget R).map ι)).app (op V) zG
    have hxV : x ∈ V := by rw [htop]; exact hx
    refine ⟨V, ExtensionByZeroModules.imF_le U ⊤, ⟨v, ?_⟩, hxV⟩
    have hfac : ι ≫ f = g i := Cofan.IsColimit.fac (coproductIsCoproduct S) g i
    show ((PresheafOfModules.toPresheaf R.obj).map
      ((_root_.SheafOfModules.forget R).map f)).app (op V) v =
      TopCat.Presheaf.restrictOpen t V (ExtensionByZeroModules.imF_le U ⊤)
    rw [show v = ((PresheafOfModules.toPresheaf R.obj).map
        ((_root_.SheafOfModules.forget R).map ι)).app (op V) zG from rfl,
      ← ConcreteCategory.comp_apply, ← NatTrans.comp_app, ← Functor.map_comp,
      ← (_root_.SheafOfModules.forget R).map_comp, hfac]
    show (((PresheafOfModules.toPresheaf R.obj).map (g i).val).app (op V)).hom zG =
      TopCat.Presheaf.restrictOpen t V (ExtensionByZeroModules.imF_le U ⊤)
    refine Eq.trans ?_ hgen
    let zs : (S i).val.obj (op V) := by
      show E.val.obj (op V)
      exact z0
    show (((PresheafOfModules.toPresheaf R.obj).map (g i).val).app (op V)).hom zs =
      ((g i).val.app (op V)).hom zs
    exact PresheafOfModules.toPresheaf_map_app_apply (g i).val (op V) zs
  exact EpiMono.epi_of_isLocallySurjective f hlocal

end Stacks.SheafOfModules
