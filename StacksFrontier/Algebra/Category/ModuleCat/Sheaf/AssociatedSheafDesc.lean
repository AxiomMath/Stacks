module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafStalk
public import StacksFrontier.Topology.Sheaves.Modules.Colimits

/-!
# Maps out of the sheaf associated to a module, and their germs

Let `(W, 𝒪_W)` be a ringed space, `α : A → Γ(W, 𝒪_W)` a ring homomorphism and `M` an
`A`-module.  Clause (4) of Stacks 01BH, available as
`Stacks.AssociatedSheaf.associatedSheafAdjunction`, says that a map of sheaves of
`𝒪_W`-modules `ℱ_M ⟶ 𝒢` out of the associated sheaf is the same thing as an `A`-linear map
`M → Γ(W, 𝒢)`.  This file names that adjoint and computes its germ at a point.

The germ is what a stalkwise argument about a map out of `ℱ_M` consumes: by
`Stacks.AssociatedSheaf.associatedSheafStalkAddEquiv` the stalk `(ℱ_M)_x` is
`𝒪_{W,x} ⊗_A M`, and the content of this file is that under that identification the stalk of
the adjoint of `g : M → Γ(W, 𝒢)` sends `germ_x(s) ⊗ m` to `germ_x(s) • germ_x(g(m))`.  Every
element of `𝒪_{W,x}` is such a germ, so this determines the stalk of the adjoint, and nothing
else about the adjoint is needed to compare it with a map built at the stalks.

## Main definitions

* `Stacks.AssociatedSheaf.associatedSheafDesc`: the map `ℱ_M ⟶ 𝒢` adjoint to an `A`-linear
  map `M → Γ(W, 𝒢)`.

## Main results

* `Stacks.AssociatedSheaf.associatedSheafDesc_unit`: the defining property — the adjoint
  composed with the unit of the adjunction is the given map.
* `Stacks.AssociatedSheaf.associatedSheafDesc_app_top_assocTmul`: its reading on sections over
  the whole space, where the unit is `m ↦ 1 ⊗ m` followed by sheafification.
* `Stacks.AssociatedSheaf.associatedSheafStalkAddEquiv_symm_tmul_germ`: the inverse of the
  identification `(ℱ_M)_x ≅ 𝒪_{W,x} ⊗_A M` carries `germ_x(s) ⊗ m` to the germ of the section
  `s ⊗ m`, sheafified.
* `Stacks.AssociatedSheaf.associatedSheafDesc_app_assocTmul`: the adjoint on a pure tensor
  section over an arbitrary open.
* `Stacks.AssociatedSheaf.stalkMap_associatedSheafDesc_germ_tmul`: **the germ formula.**  The
  stalk at `x` of the adjoint of `g` sends the element of `(ℱ_M)_x` corresponding to
  `germ_x(s) ⊗ m` to `germ_x(s) • germ_x(g(m))`.
* `Stacks.AssociatedSheaf.stalkMap_associatedSheafFunctor_map_germ_tmul`: **the stalk
  identification is natural in `M`.**  The stalk of `ℱ_φ`, for `φ : M ⟶ N` an `A`-linear map,
  is the base change `𝒪_{W,x} ⊗_A φ`.

## Implementation notes

The map on stalks is taken to be `AlgebraicGeometry.SheafOfModules.stalkMap`, which is the
stalk of abelian groups together with its `𝒪_{W,x}`-linearity.  That linearity is the one place
where a scalar has to be moved across the stalk of a morphism of sheaves of modules, and taking
the already-linear map avoids reproving it: the underlying function of
`AlgebraicGeometry.SheafOfModules.stalkMap` is the stalk of the underlying morphism of
presheaves of abelian groups, by `rfl`, so every germ computation goes through
`TopCat.Presheaf.stalkFunctor_map_germ_apply` unchanged.

The scalar of the germ formula is written as the germ of a section over a neighbourhood `U`
rather than as an abstract element of `𝒪_{W,x}`: the scalar on the right-hand side acts through
the module structure of `AlgebraicGeometry.SheafOfModules.stalkObj`, whose ring is the stalk of
the sheaf of *rings* `𝒪_W` regarded in `RingCat`, while the tensor product on the left is taken
over the stalk in `CommRingCat`.  With a section as the input both spellings are germs of the
same `s` and no conversion between the two stalks occurs.  For the same reason the two places
where a section of `𝒪_W` acts on sections of a sheaf of modules carry an explicit `show` giving
that section its `RingCat` reading, which is the one the module instance is stated over.

The computation itself is at the level of sections: over `U` the section `s ⊗ m` of the
associated presheaf is `s • (1 ⊗ m)`, and `1 ⊗ m` over `U` is the restriction of `1 ⊗ m` over
the whole space, which is where the unit of the adjunction lives; the scalar `s` then comes out
as `germ_x(s)` by germ-semilinearity.  No universal property of the stalk is used.

Restriction maps are written `M.map f` rather than `M.restrictₛₗ f` — the two are equal by
`PresheafOfModules.restrictₛₗ_apply`, and `PresheafOfModules.naturality_apply`, which is what
moves the unit and the adjoint past a restriction, is stated in the first spelling.

Everything is stated at a single universe, as in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafStalk`: the module structure on a
stalk of a presheaf of modules is available only for a presheaf of modules over a presheaf of
rings on a space all living in one universe.

## References

* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH), clause (4): the
  mapping property of the sheaf associated to a module.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

universe u

noncomputable section

namespace Stacks.AssociatedSheaf

variable (W : RingedSpace.{u, u}) {A : Type u} [CommRing A]
  (α : A →+* W.presheaf.obj (op ⊤)) (M : ModuleCat.{u} A)
  (𝒢 : SheafOfModules.{u} (structureSheafRing W))

/-! ### The adjoint of a linear map into global sections -/

/-- **Clause (4) of Stacks 01BH as a constructor.**  The map of sheaves of `𝒪_W`-modules
`ℱ_M ⟶ 𝒢` adjoint to an `A`-linear map `M → Γ(W, 𝒢)`, the scalars of `A` acting on the global
sections through `α`. -/
def associatedSheafDesc (g : M ⟶ (globalSectionsFunctor.{u, u} W α).obj 𝒢) :
    (associatedSheafFunctor.{u, u} W α).obj M ⟶ 𝒢 :=
  ((associatedSheafAdjunction.{u, u} W α).homEquiv M 𝒢).symm g

/-- **The defining property of `Stacks.AssociatedSheaf.associatedSheafDesc`.**  Its effect on
global sections, precomposed with the unit of the adjunction, is the map it was built from. -/
theorem associatedSheafDesc_unit (g : M ⟶ (globalSectionsFunctor.{u, u} W α).obj 𝒢) :
    (associatedSheafAdjunction.{u, u} W α).unit.app M ≫
        (globalSectionsFunctor.{u, u} W α).map (associatedSheafDesc W α M 𝒢 g) = g :=
  Eq.trans (Adjunction.homEquiv_unit (associatedSheafAdjunction.{u, u} W α) M 𝒢
      (associatedSheafDesc W α M 𝒢 g)).symm
    (((associatedSheafAdjunction.{u, u} W α).homEquiv M 𝒢).apply_symm_apply g)

/-- `Stacks.AssociatedSheaf.associatedSheafDesc_unit`, read on an element of `M`: the component
over the whole space of the adjoint carries the unit of `m` to `g(m)`. -/
theorem associatedSheafDesc_app_top (g : M ⟶ (globalSectionsFunctor.{u, u} W α).obj 𝒢) (m : M) :
    (associatedSheafDesc W α M 𝒢 g).val.app (op ⊤)
        (((associatedSheafAdjunction.{u, u} W α).unit.app M).hom m) = g m := by
  have h := associatedSheafDesc_unit W α M 𝒢 g
  exact congrArg (fun φ => ModuleCat.Hom.hom φ m) h

/-- **The adjoint on sections over the whole space.**  The unit of
`Stacks.AssociatedSheaf.associatedSheafAdjunction` is `m ↦ 1 ⊗ m` followed by the unit of
sheafification, so the adjoint of `g` carries the sheafified section `1 ⊗ m` over the whole
space to `g(m)`. -/
theorem associatedSheafDesc_app_top_assocTmul
    (g : M ⟶ (globalSectionsFunctor.{u, u} W α).obj 𝒢) (m : M) :
    (associatedSheafDesc W α M 𝒢 g).val.app (op ⊤)
        ((associatedSheafUnit W α M).app (op ⊤)
          (assocTmul W α M ⊤ (1 : W.presheaf.obj (op ⊤)) m)) = g m :=
  associatedSheafDesc_app_top W α M 𝒢 g m

/-! ### Germs -/

variable (x : W.carrier)

/-- **The sheafification map on stalks, read on germs.**  The identification of the stalk of
the associated presheaf with that of the associated sheaf is the stalk of the sheafification
unit, so it carries the germ of a section to the germ of its image. -/
theorem sheafificationStalkAddEquiv_assocGerm (U : Opens W.carrier) (hx : x ∈ U)
    (t : ToType ((associatedPresheaf W α M).obj (op U))) :
    sheafificationStalkAddEquiv W α M x (assocGerm W α M x U hx t) =
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (associatedSheaf W α M).val.presheaf U x hx).hom
          ((associatedSheafUnit W α M).app (op U) t) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
    ((PresheafOfModules.toPresheaf (structureSheafRing W).obj).map
      (associatedSheafUnit W α M)) t

/-- **The identification `(ℱ_M)_x ≅ 𝒪_{W,x} ⊗_A M` on pure tensors of germs.**  Its inverse
carries `germ_x(s) ⊗ m`, for `s` a section of `𝒪_W` over a neighbourhood `U` of `x`, to the
germ at `x` of the sheafified section `s ⊗ m` over `U`. -/
theorem associatedSheafStalkAddEquiv_symm_tmul_germ (U : Opens W.carrier) (hx : x ∈ U)
    (s : W.presheaf.obj (op U)) (m : M) :
    letI := stalkAlgebra W α x
    (associatedSheafStalkAddEquiv W α M x).symm
        ((W.presheaf.germ U x hx).hom s ⊗ₜ[A] m) =
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (associatedSheaf W α M).val.presheaf U x hx).hom
          ((associatedSheafUnit W α M).app (op U) (assocTmul W α M U s m)) := by
  let := stalkAlgebra W α x
  refine Eq.trans ?_ (sheafificationStalkAddEquiv_assocGerm W α M x U hx (assocTmul W α M U s m))
  refine congrArg (sheafificationStalkAddEquiv W α M x) ?_
  refine (presheafStalkAddEquiv W α M x).symm_apply_eq.mpr ?_
  refine Eq.trans ?_ (presheafStalkFwd_assocGerm W α M x U hx (assocTmul W α M U s m)).symm
  exact (presheafStalkLeg_assocTmul W α M x U hx s m).symm

/-- **The pure tensor `s ⊗ m` is `s` acting on the restriction of `1 ⊗ m`.**  Over a
neighbourhood `U` the section `s ⊗ m` of the associated presheaf is `s` times the restriction
to `U` of the section `1 ⊗ m` over the whole space. -/
theorem assocTmul_eq_smul_res (U : Opens W.carrier) (s : W.presheaf.obj (op U)) (m : M) :
    assocTmul W α M U s m =
      s • (associatedPresheaf W α M).restrictₛₗ (homOfLE (le_top (a := U))).op
        (assocTmul W α M ⊤ (1 : W.presheaf.obj (op ⊤)) m) := by
  refine Eq.trans (congrArg (fun y => assocTmul W α M U y m) (mul_one s).symm) ?_
  refine Eq.trans (Stacks.SitePointBaseChange.smul_cofTmul (globalSectionsMap W α)
    (constantModulePresheaf W M) U s (1 : W.presheaf.obj (op U)) m).symm ?_
  refine congrArg (s • ·) ?_
  refine Eq.trans ?_ (Stacks.SitePointBaseChange.res_cofTmul (globalSectionsMap W α)
    (constantModulePresheaf W M) (homOfLE (le_top (a := U)))
    (1 : W.presheaf.obj (op ⊤)) m).symm
  exact congrArg (fun y => assocTmul W α M U y m)
    (map_one (W.presheaf.map (homOfLE (le_top (a := U))).op).hom).symm

/-- **The adjoint on a pure tensor section.**  Over a neighbourhood `U` of a point the adjoint
of `g` carries the sheafified section `s ⊗ m` to `s` times the restriction to `U` of `g(m)`. -/
theorem associatedSheafDesc_app_assocTmul
    (g : M ⟶ (globalSectionsFunctor.{u, u} W α).obj 𝒢) (U : Opens W.carrier)
    (s : W.presheaf.obj (op U)) (m : M) :
    (associatedSheafDesc W α M 𝒢 g).val.app (op U)
        ((associatedSheafUnit W α M).app (op U) (assocTmul W α M U s m)) =
      (show (structureSheafRing W).obj.obj (op U) from s) •
        𝒢.val.map (homOfLE (le_top (a := U))).op (g m) := by
  have hu : (associatedSheafUnit W α M).app (op U) (assocTmul W α M U s m) =
      (show (structureSheafRing W).obj.obj (op U) from s) •
        (associatedSheafUnit W α M).app (op U)
          ((associatedPresheaf W α M).map (homOfLE (le_top (a := U))).op
            (assocTmul W α M ⊤ (1 : W.presheaf.obj (op ⊤)) m)) := by
    refine Eq.trans (congrArg ((associatedSheafUnit W α M).app (op U))
      (assocTmul_eq_smul_res W α M U s m)) ?_
    exact map_smul _ _ _
  have hres : (associatedSheafUnit W α M).app (op U)
        ((associatedPresheaf W α M).map (homOfLE (le_top (a := U))).op
          (assocTmul W α M ⊤ (1 : W.presheaf.obj (op ⊤)) m)) =
      (associatedSheaf W α M).val.map (homOfLE (le_top (a := U))).op
        ((associatedSheafUnit W α M).app (op ⊤)
          (assocTmul W α M ⊤ (1 : W.presheaf.obj (op ⊤)) m)) :=
    PresheafOfModules.naturality_apply (associatedSheafUnit W α M)
      (homOfLE (le_top (a := U))).op _
  have hdesc : (associatedSheafDesc W α M 𝒢 g).val.app (op U)
        ((associatedSheaf W α M).val.map (homOfLE (le_top (a := U))).op
          ((associatedSheafUnit W α M).app (op ⊤)
            (assocTmul W α M ⊤ (1 : W.presheaf.obj (op ⊤)) m))) =
      𝒢.val.map (homOfLE (le_top (a := U))).op (g m) := by
    refine Eq.trans (PresheafOfModules.naturality_apply
      (associatedSheafDesc W α M 𝒢 g).val (homOfLE (le_top (a := U))).op _) ?_
    exact congrArg (𝒢.val.map (homOfLE (le_top (a := U))).op)
      (associatedSheafDesc_app_top_assocTmul W α M 𝒢 g m)
  refine Eq.trans (congrArg ((associatedSheafDesc W α M 𝒢 g).val.app (op U)) hu) ?_
  refine Eq.trans (map_smul _ _ _)
    (congrArg ((show (structureSheafRing W).obj.obj (op U) from s) • ·) ?_)
  exact Eq.trans (congrArg ((associatedSheafDesc W α M 𝒢 g).val.app (op U)) hres) hdesc

/-- **The germ formula for the adjoint.**  Let `g : M → Γ(W, 𝒢)` be `A`-linear, let `x` be a
point of `W` and let `s` be a section of `𝒪_W` over a neighbourhood `U` of `x`.  Under the
identification `(ℱ_M)_x ≅ 𝒪_{W,x} ⊗_A M` of
`Stacks.AssociatedSheaf.associatedSheafStalkAddEquiv`, the stalk at `x` of the adjoint
`ℱ_M ⟶ 𝒢` of `g` carries `germ_x(s) ⊗ m` to `germ_x(s) • germ_x(g(m))`.

Every element of `𝒪_{W,x}` is such a germ, so this determines the stalk of the adjoint
completely.  It is what makes a map out of an associated sheaf comparable with a map
constructed at the stalks: no further information about the adjoint is involved. -/
theorem stalkMap_associatedSheafDesc_germ_tmul
    (g : M ⟶ (globalSectionsFunctor.{u, u} W α).obj 𝒢) (U : Opens W.carrier) (hx : x ∈ U)
    (s : W.presheaf.obj (op U)) (m : M) :
    letI := stalkAlgebra W α x
    (AlgebraicGeometry.SheafOfModules.stalkMap (structureSheafRing W) x
          (associatedSheafDesc W α M 𝒢 g)).hom
        ((associatedSheafStalkAddEquiv W α M x).symm
          ((W.presheaf.germ U x hx).hom s ⊗ₜ[A] m)) =
      (TopCat.Presheaf.germ (C := RingCat.{u})
          (structureSheafRing W).obj U x hx).hom s •
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) 𝒢.val.presheaf ⊤ x trivial).hom (g m) := by
  let := stalkAlgebra W α x
  refine Eq.trans (congrArg
    (AlgebraicGeometry.SheafOfModules.stalkMap (structureSheafRing W) x
      (associatedSheafDesc W α M 𝒢 g)).hom
    (associatedSheafStalkAddEquiv_symm_tmul_germ W α M x U hx s m)) ?_
  refine Eq.trans (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
    ((PresheafOfModules.toPresheaf (structureSheafRing W).obj).map
      (associatedSheafDesc W α M 𝒢 g).val) _) ?_
  refine Eq.trans (congrArg (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) 𝒢.val.presheaf
    U x hx).hom (associatedSheafDesc_app_assocTmul W α M 𝒢 g U s m)) ?_
  refine Eq.trans (AlgebraicGeometry.SheafOfModules.germ_hom_smul
    (structureSheafRing W) x 𝒢.val U hx s
    (𝒢.val.map (homOfLE (le_top (a := U))).op (g m))) ?_
  refine congrArg ((TopCat.Presheaf.germ (C := RingCat.{u})
    (structureSheafRing W).obj U x hx).hom s • ·) ?_
  exact TopCat.Presheaf.germ_res_apply 𝒢.val.presheaf (homOfLE (le_top (a := U))) x hx (g m)

/-! ### Functoriality of the stalk identification in the module -/

/-- **The stalk identification `(ℱ_M)_x ≅ 𝒪_{W,x} ⊗_A M` is natural in `M`.**  For an
`A`-linear map `φ : M → N` the stalk at `x` of the induced map `ℱ_M ⟶ ℱ_N` is, under the
identifications of `Stacks.AssociatedSheaf.associatedSheafStalkAddEquiv`, the base change
`𝒪_{W,x} ⊗_A φ`: it carries `germ_x(s) ⊗ m` to `germ_x(s) ⊗ φ(m)`.

Every element of `𝒪_{W,x}` is such a germ and the pure tensors generate, so this determines the
stalk of `ℱ_φ` completely.  It is what lets the identification be carried along a complex: the
differential of a two-term complex of `A`-modules is such a `φ`, and its associated sheaf's
stalk differential is the base change of it. -/
theorem stalkMap_associatedSheafFunctor_map_germ_tmul (N : ModuleCat.{u} A) (φ : M ⟶ N)
    (U : Opens W.carrier) (hx : x ∈ U) (s : W.presheaf.obj (op U)) (m : M) :
    letI := stalkAlgebra W α x
    (AlgebraicGeometry.SheafOfModules.stalkMap (structureSheafRing W) x
          ((associatedSheafFunctor.{u, u} W α).map φ)).hom
        ((associatedSheafStalkAddEquiv W α M x).symm
          ((W.presheaf.germ U x hx).hom s ⊗ₜ[A] m)) =
      (associatedSheafStalkAddEquiv W α N x).symm
        ((W.presheaf.germ U x hx).hom s ⊗ₜ[A] φ m) := by
  let := stalkAlgebra W α x
  have hnat : ((associatedSheafFunctor.{u, u} W α).map φ).val.app (op U)
        ((associatedSheafUnit W α M).app (op U) (assocTmul W α M U s m)) =
      (associatedSheafUnit W α N).app (op U)
        ((Stacks.PresheafOfModules.ChangeOfRings.cofHom (globalSectionsMap W α)
          ((constantModuleFunctor W).map φ)).app (op U) (assocTmul W α M U s m)) := by
    let := hasModuleSheafify.{u, u} W
    let := moduleSheafifyWEqualsLocallyBijective.{u, u} W
    have hn := (PresheafOfModules.sheafificationAdjunction.{u}
      (R := structureSheafRing W)
      (𝟙 (structureSheafRing W).obj)).unit.naturality
        (Stacks.PresheafOfModules.ChangeOfRings.cofHom (globalSectionsMap W α)
          ((constantModuleFunctor W).map φ))
    exact (congrArg (fun ψ => PresheafOfModules.Hom.app ψ (op U)
      (assocTmul W α M U s m)) hn).symm
  have htmul : (Stacks.PresheafOfModules.ChangeOfRings.cofHom (globalSectionsMap W α)
        ((constantModuleFunctor W).map φ)).app (op U) (assocTmul W α M U s m) =
      assocTmul W α N U s (φ m) :=
    Stacks.PresheafOfModules.ChangeOfRings.cofHom_app_tmul (globalSectionsMap W α)
      ((constantModuleFunctor W).map φ) (op U) s m
  refine Eq.trans (congrArg
    (AlgebraicGeometry.SheafOfModules.stalkMap (structureSheafRing W) x
      ((associatedSheafFunctor.{u, u} W α).map φ)).hom
    (associatedSheafStalkAddEquiv_symm_tmul_germ W α M x U hx s m)) ?_
  refine Eq.trans (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
    ((PresheafOfModules.toPresheaf (structureSheafRing W).obj).map
      ((associatedSheafFunctor.{u, u} W α).map φ).val) _) ?_
  refine Eq.trans (congrArg (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
    (associatedSheaf W α N).val.presheaf U x hx).hom
    (Eq.trans hnat (congrArg ((associatedSheafUnit W α N).app (op U)) htmul))) ?_
  exact (associatedSheafStalkAddEquiv_symm_tmul_germ W α N x U hx s (φ m)).symm

end Stacks.AssociatedSheaf

end

end
