module

public import StacksFrontier.Topology.Sheaves.Functors.Pullback.SheafStalk
public import StacksFrontier.Topology.Sheaves.Stalk.PullbackUnit

/-!
# Maps out of an inverse image, tested on stalks

Let `f : X → Y` be a continuous map, let `H` be a sheaf of sets on `Y` and `T` a sheaf of sets on
`X`. A morphism `ψ : H ⟶ f_* T` induces, at every point `x` of `X`, a map of stalks
`H_{f x} → T_x` sending the germ of a section `s` to the germ of `ψ(s)`; this is
`Stacks.Sheaves.PullbackUnit.stalkComparison`. The adjoint `f⁻¹H ⟶ T` of `ψ` is an isomorphism
exactly when all these maps are bijective.

The reason is that the stalk comparison of the unit `H ⟶ f_* f⁻¹H` is the inverse of the
canonical identification `(f⁻¹H)_x ≅ H_{f x}` of Stacks 008H, so that the stalk comparison of
`ψ` is that identification followed by the stalk at `x` of the adjoint of `ψ`.

## Main results

* `Stacks.Sheaves.PullbackUnit.stalkComparison_unit`: the stalk comparison of the unit of the
  inverse image–direct image adjunction is the inverse of `stalkPullbackSheafIso`.
* `Stacks.Sheaves.PullbackUnit.isIso_homEquiv_symm_iff`: the adjoint of `ψ : H ⟶ f_* T` is an
  isomorphism if and only if every stalk comparison of `ψ` is bijective.
* `Stacks.Sheaves.PullbackUnit.stalkPullbackSheafIso_inv_naturality`: the identification of
  Stacks 008H is natural in the sheaf.
* `Stacks.Sheaves.PullbackUnit.isIso_of_isIso_pullback_map`: inverse image along a surjective
  map reflects isomorphisms.

## References

* [Stacks Project, Tag 008H](https://stacks.math.columbia.edu/tag/008H)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.Sheaves.PullbackUnit

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- The stalk comparison of the unit `H ⟶ f_* f⁻¹H` is the inverse of the identification
`(f⁻¹H)_x ≅ H_{f x}` of Stacks 008H. -/
theorem stalkComparison_unit (H : Y.Sheaf (Type u)) (x : X) :
    stalkComparison f (Type u)
        ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app H).hom x =
      (stalkPullbackSheafIso f H x).inv := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun V hV => ?_
  ext s
  have h1 := ConcreteCategory.congr_hom (germ_stalkComparison f (Type u)
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app H).hom x V hV) s
  exact h1.trans (stalkPullbackSheafIso_inv_germ f H x V hV s).symm

/-- **A map out of an inverse image is an isomorphism exactly when it is so on stalks**, read
through the adjunction: the adjoint `f⁻¹H ⟶ T` of `ψ : H ⟶ f_* T` is an isomorphism if and only
if, at every point `x`, the map `H_{f x} → T_x` sending the germ of `s` to the germ of `ψ(s)` is
bijective. -/
theorem isIso_homEquiv_symm_iff {H : Y.Sheaf (Type u)} {T : X.Sheaf (Type u)}
    (ψ : H ⟶ (TopCat.Sheaf.pushforward (Type u) f).obj T) :
    IsIso (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).homEquiv H T).symm ψ) ↔
      ∀ x, Function.Bijective (stalkComparison f (Type u) ψ.hom x) := by
  set φ := ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).homEquiv H T).symm ψ
  have hψ : ψ = (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app H ≫
      (TopCat.Sheaf.pushforward (Type u) f).map φ :=
    (Equiv.apply_symm_apply _ ψ).symm.trans (Adjunction.homEquiv_unit _ _ _ _)
  have hψ' : ψ.hom = ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app H).hom ≫
      (TopCat.Presheaf.pushforward (Type u) f).map φ.hom :=
    congrArg (fun t => t.hom) hψ
  have hcomp : ∀ x, stalkComparison f (Type u) ψ.hom x =
      (stalkPullbackSheafIso f H x).inv ≫ (TopCat.Presheaf.stalkFunctor (Type u) x).map φ.hom :=
    fun x => ((congrArg (fun t => stalkComparison f (Type u) t x) hψ').trans
      (stalkComparison_comp f (Type u) _ φ.hom x)).trans
        (congrArg (fun t => t ≫ (TopCat.Presheaf.stalkFunctor (Type u) x).map φ.hom)
          (stalkComparison_unit f H x))
  rw [TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso]
  refine forall_congr' fun x => ?_
  have := (stalkPullbackSheafIso f H x).isIso_inv
  rw [hcomp x]
  exact (isIso_comp_left_iff (stalkPullbackSheafIso f H x).inv _).symm.trans
    (isIso_iff_bijective _)

/-- The identification `(f⁻¹H)_x ≅ H_{f x}` of Stacks 008H is natural in `H`. -/
theorem stalkPullbackSheafIso_inv_naturality {H H' : Y.Sheaf (Type u)} (θ : H ⟶ H') (x : X) :
    (TopCat.Presheaf.stalkFunctor (Type u) (f x)).map θ.hom ≫ (stalkPullbackSheafIso f H' x).inv =
      (stalkPullbackSheafIso f H x).inv ≫
        (TopCat.Presheaf.stalkFunctor (Type u) x).map
          ((TopCat.Sheaf.pullback (Type u) f).map θ).hom := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun V hV => ?_
  ext s
  let η := (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit
  have hn : (η.app H').hom.app (op V) (θ.hom.app (op V) s) =
      ((TopCat.Sheaf.pullback (Type u) f).map θ).hom.app (op ((Opens.map f).obj V))
        ((η.app H).hom.app (op V) s) :=
    congrArg (fun (t : H ⟶ (TopCat.Sheaf.pushforward (Type u) f).obj
      ((TopCat.Sheaf.pullback (Type u) f).obj H')) => t.hom.app (op V) s) (η.naturality θ)
  change (stalkPullbackSheafIso f H' x).inv
      ((TopCat.Presheaf.stalkFunctor (Type u) (f x)).map θ.hom (H.presheaf.germ V (f x) hV s)) =
    (TopCat.Presheaf.stalkFunctor (Type u) x).map ((TopCat.Sheaf.pullback (Type u) f).map θ).hom
      ((stalkPullbackSheafIso f H x).inv (H.presheaf.germ V (f x) hV s))
  have hx : x ∈ (Opens.map f).obj V := hV
  refine ((congrArg (stalkPullbackSheafIso f H' x).inv
    (TopCat.Presheaf.stalkFunctor_map_germ_apply V (f x) hV θ.hom s)).trans
      (stalkPullbackSheafIso_inv_germ f H' x V hV _)).trans ?_
  refine Eq.trans ?_ ((congrArg ((TopCat.Presheaf.stalkFunctor (Type u) x).map
    ((TopCat.Sheaf.pullback (Type u) f).map θ).hom)
      (stalkPullbackSheafIso_inv_germ f H x V hV s)).trans
    (TopCat.Presheaf.stalkFunctor_map_germ_apply ((Opens.map f).obj V) x hx
      ((TopCat.Sheaf.pullback (Type u) f).map θ).hom _)).symm
  exact congrArg _ hn

/-- **Inverse image along a surjection reflects isomorphisms.** A morphism of sheaves of sets on
`Y` whose inverse image along a surjective continuous map is an isomorphism is an isomorphism,
the stalks of the inverse image being those of the sheaf. -/
theorem isIso_of_isIso_pullback_map (hf : Function.Surjective f) {H H' : Y.Sheaf (Type u)}
    (θ : H ⟶ H') (h : IsIso ((TopCat.Sheaf.pullback (Type u) f).map θ)) : IsIso θ := by
  rw [TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso]
  intro y
  obtain ⟨x, rfl⟩ := hf y
  have : IsIso ((TopCat.Sheaf.forget (Type u) X).map
      ((TopCat.Sheaf.pullback (Type u) f).map θ)) := Functor.map_isIso _ _
  have hs : IsIso ((TopCat.Presheaf.stalkFunctor (Type u) x).map
      ((TopCat.Sheaf.pullback (Type u) f).map θ).hom) :=
    Functor.map_isIso (TopCat.Presheaf.stalkFunctor (Type u) x)
      ((TopCat.Sheaf.forget (Type u) X).map ((TopCat.Sheaf.pullback (Type u) f).map θ))
  have := (stalkPullbackSheafIso f H x).isIso_inv
  have := (stalkPullbackSheafIso f H' x).isIso_inv
  have : IsIso ((TopCat.Presheaf.stalkFunctor (Type u) (f x)).map θ.hom ≫
      (stalkPullbackSheafIso f H' x).inv) := by
    rw [stalkPullbackSheafIso_inv_naturality]
    exact IsIso.comp_isIso' (stalkPullbackSheafIso f H x).isIso_inv hs
  exact (isIso_comp_right_iff _ (stalkPullbackSheafIso f H' x).inv).1 this

end Stacks.Sheaves.PullbackUnit
