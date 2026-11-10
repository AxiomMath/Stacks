module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackPresheaf

/-!
# A concrete model for the pullback of presheaves of modules

Let `f : X ⟶ Y` be a continuous map of topological spaces and let `O` be a presheaf of rings
on `Y`.  Mathlib's `PresheafOfModules.pullback φ` is defined, for a morphism of presheaves of
rings `φ : S ⟶ F.op ⋙ R`, as the *abstract* left adjoint `(pushforward φ).leftAdjoint`, so it
has no description of its sections.  Stacks 008T, on the other hand, builds the pullback
`f_p G` of a presheaf of `O`-modules explicitly, as the objectwise filtered colimit
`(f_p G)(U) = colim_{V, U ⊆ f⁻¹V} G(V)` with the germwise scalar action
(`Stacks.PresheafOfModules.Pullback.pullbackModuleFunctor`).

This file identifies the two for the Kan-extension unit
`η : O ⟶ f_* (f_p O)`, by exhibiting the explicit functor as a left adjoint of
`PresheafOfModules.pushforward η` and invoking uniqueness of left adjoints.

The adjunction bijection is the abelian-group-level one,
`TopCat.Presheaf.pullbackPushforwardAdjunction Ab f`; all that has to be checked is that it
matches up the two linearity conditions.  In one direction that is the semilinearity of the
Kan-extension unit (`Stacks.PresheafOfModules.Pullback.pullbackModule_unit_smul`); in the other it
  is the same
statement read on germs, for which one needs that every germ of `f_p G` over `U` is the
restriction of a unit image (`Stacks.PresheafOfModules.Pullback.exists_unit_rep`) — the elementwise
  content extracted
here from `PresheafOfModules.ModuleColimit.jointly_surjective₂`.

## Main definitions

* `Stacks.PresheafOfModules.Pullback.pullbackRingUnitHom`: the Kan-extension unit `η : O ⟶ f_*(f_p
  O)` read as the
  morphism of presheaves of rings that `PresheafOfModules.pushforward` consumes.
* `Stacks.PresheafOfModules.Pullback.modUnit`, `Stacks.PresheafOfModules.Pullback.modRes`: the unit
  `M(V) → (f_p M)(f⁻¹V)` and the
  restriction maps of `f_p M`, typed as maps of sections of `f_p M` so that the scalar
  actions on their values are those of `Stacks.PresheafOfModules.Pullback.pullbackModuleFunctor`.

## Main results

* `Stacks.PresheafOfModules.Pullback.pbAbIso_ι`, `Stacks.PresheafOfModules.Pullback.pbRingIso_ι`:
  the colimit injection at the index
  `(V, U ⊆ f⁻¹V)` is the unit over `V` followed by the restriction to `U`.
* `Stacks.PresheafOfModules.Pullback.exists_unit_rep`: a scalar and a section of `f_p` over `U` are
  simultaneously
  restrictions of unit images from a single `V`.
* `Stacks.PresheafOfModules.Pullback.pullbackModuleHomEquiv`: the hom-set bijection
  `Hom_{f_p O}(f_p M, N) ≃ Hom_O(M, η_* N)`.
* `Stacks.PresheafOfModules.Pullback.pullbackModuleAdjunction`: `f_p ⊣ η_*` on presheaves of
  modules.
* `Stacks.PresheafOfModules.Pullback.pullbackIsoPullbackModuleFunctor`: **the concrete model.**
  `PresheafOfModules.pullback η ≅ Stacks.PresheafOfModules.Pullback.pullbackModuleFunctor f O`.

## Implementation notes

Several statements below are deliberate retypings — `modUnit`, `modRes`,
`abTransposeSect`, `abTransposeInvSect`, `psiSect` — of terms that are definitionally what
they say.  They exist because a section of `f_p M` over `U` has *two* spellings, one through
`Stacks.PresheafOfModules.Pullback.pullbackAb` (the underlying presheaf of abelian groups) and one
  through
`(Stacks.PresheafOfModules.Pullback.pullbackModuleFunctor f O).obj M` (the presheaf of modules),
  and only the
latter carries the scalar action.  The two are definitionally equal but not interchangeable
for `rw`, whose motive is checked at a lower transparency; fixing one spelling per statement
is what makes the rewrite chains in `abTransposeSect_smul` and `abTransposeInvSect_smul`
fire at all.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Limits Opposite

namespace Stacks.PresheafOfModules.Pullback

universe u

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (O : TopCat.Presheaf RingCat.{u} Y)

/-- The Kan-extension unit `η : O ⟶ f_*(f_p O)` read as a morphism of presheaves of rings
over the functor `Opens.map f`.  This is the datum `PresheafOfModules.pushforward` consumes. -/
noncomputable def pullbackRingUnitHom : O ⟶ (Opens.map f).op ⋙ pullbackRing f O :=
  (TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} f).unit.app O

/-- The components of `pullbackRingUnitHom` are the units `O(V) → (f_p O)(f⁻¹V)`. -/
theorem pullbackRingUnitHom_app (V : (Opens Y)ᵒᵖ) :
    (pullbackRingUnitHom f O).app V = pullbackRingUnit f O V :=
  (pullbackRingUnit_eq_adjunction_unit f O V).symm

variable (G : PresheafOfModules.{u} O)

/-- The colimit injection at `c`, followed by the colimit comparison with the left Kan extension,
is the Kan-extension unit followed by the restriction along `c.unop.unop.hom`. -/
private theorem ι_comp_colimitIso_hom_comp_leftKanExtensionObjIsoColimit_inv
    {C : Type*} [Category C] [HasColimitsOfSize.{u, u} C] (P : (Opens Y)ᵒᵖ ⥤ C) (U : (Opens X)ᵒᵖ)
    (c : ((CostructuredArrow (Opens.map f).op U)ᵒᵖ)ᵒᵖ) :
    colimit.ι ((opOpEquivalence (CostructuredArrow (Opens.map f).op U)).functor ⋙
          (CostructuredArrow.proj (Opens.map f).op U ⋙ P)) c ≫
        ((Functor.Final.colimitIso
            (opOpEquivalence (CostructuredArrow (Opens.map f).op U)).functor
            (CostructuredArrow.proj (Opens.map f).op U ⋙ P)).hom ≫
          ((Opens.map f).op.leftKanExtensionObjIsoColimit P U).inv)
      = ((Opens.map f).op.leftKanExtensionUnit P).app c.unop.unop.left ≫
          ((Opens.map f).op.leftKanExtension P).map c.unop.unop.hom := by
  have : FinallySmall.{u} (CostructuredArrow (Opens.map f).op U) :=
    finallySmall_of_essentiallySmall _
  rw [← Category.assoc, Functor.Final.ι_colimitIso_hom]
  exact Functor.ι_leftKanExtensionObjIsoColimit_inv (Opens.map f).op P U c.unop.unop

/-- **The germ at an arbitrary index is a restriction of a unit image.**  The colimit injection
at the object `(V, i : U ⊆ f⁻¹V)` of the neighbourhood category `N(U)` is the unit
`G(V) → (f_p G)(f⁻¹V)` followed by the restriction along `i`. -/
theorem pbAbIso_ι (U : (Opens X)ᵒᵖ)
    (c : ((CostructuredArrow (Opens.map f).op U)ᵒᵖ)ᵒᵖ)
    (m : G.presheaf.obj c.unop.unop.left) :
    (pbAbIso f O G U).hom (colimit.ι (pbMmod f O G U).presheaf c m)
      = (pullbackAb f (underlyingAb O G)).map c.unop.unop.hom
          (pullbackAbUnit f (underlyingAb O G) c.unop.unop.left m) := by
  have h2 := ConcreteCategory.congr_hom
    (ι_comp_colimitIso_hom_comp_leftKanExtensionObjIsoColimit_inv f G.presheaf U c) m
  simp only [ConcreteCategory.comp_apply] at h2
  rw [pbAbIso, pullbackAbUnit]
  exact h2

/-- The ring analogue of `Stacks.PresheafOfModules.Pullback.pbAbIso_ι`. -/
theorem pbRingIso_ι (U : (Opens X)ᵒᵖ)
    (c : ((CostructuredArrow (Opens.map f).op U)ᵒᵖ)ᵒᵖ)
    (a : O.obj c.unop.unop.left) :
    (pbRingIso f O U).hom (colimit.ι (pbRdiag f O U) c a)
      = (pullbackRing f O).map c.unop.unop.hom
          (pullbackRingUnit f O c.unop.unop.left a) := by
  have h2 := ConcreteCategory.congr_hom
    (ι_comp_colimitIso_hom_comp_leftKanExtensionObjIsoColimit_inv f O U c) a
  simp only [ConcreteCategory.comp_apply] at h2
  rw [pbRingIso, pullbackRingUnit]
  exact h2

/-- The Kan-extension unit `M(V) → (f_p M)(f⁻¹V)`, typed as a section of `f_p M`, so that
the `(f_p O)(f⁻¹V)`-action on its values is the one of
  `Stacks.PresheafOfModules.Pullback.pullbackModuleFunctor`. -/
noncomputable abbrev modUnit (V : (Opens Y)ᵒᵖ) (m : G.obj V) :
    ((pullbackModuleFunctor f O).obj G).obj ((Opens.map f).op.obj V) :=
  pullbackAbUnit f (underlyingAb O G) V m

/-- The restriction map of `f_p M`, typed as a map of sections of `f_p M`. -/
noncomputable abbrev modRes {U U' : (Opens X)ᵒᵖ} (i : U ⟶ U')
    (x : ((pullbackModuleFunctor f O).obj G).obj U) :
    ((pullbackModuleFunctor f O).obj G).obj U' :=
  (pullbackAb f (underlyingAb O G)).map i x

/-- Semilinearity of the Kan-extension unit
  (`Stacks.PresheafOfModules.Pullback.pullbackModule_unit_smul`) in the
`modUnit` spelling. -/
theorem modUnit_smul (V : (Opens Y)ᵒᵖ) (a : O.obj V) (m : G.obj V) :
    modUnit f O G V (a • m) = pullbackRingUnit f O V a • modUnit f O G V m :=
  pullbackModule_unit_smul f O G V a m

/-- Semilinearity of the restriction maps of `f_p M` in the `modRes` spelling. -/
theorem modRes_smul {U U' : (Opens X)ᵒᵖ} (i : U ⟶ U')
    (r : (pullbackRing f O).obj U) (x : ((pullbackModuleFunctor f O).obj G).obj U) :
    modRes f O G i (r • x) = (pullbackRing f O).map i r • modRes f O G i x :=
  PresheafOfModules.map_smul ((pullbackModuleFunctor f O).obj G) i r x

/-- **Joint representation by unit images.**  A scalar `r : (f_p O)(U)` and a section
`m : (f_p G)(U)` are simultaneously the restrictions, along one map `i : U ⊆ f⁻¹V`, of the unit
images of a scalar `a₀ : O(V)` and a section `m₀ : G(V)`.

This is `PresheafOfModules.ModuleColimit.jointly_surjective₂` read through the comparison
isomorphisms `pbRingIso`/`pbAbIso` and
  `Stacks.PresheafOfModules.Pullback.pbRingIso_ι`/`Stacks.PresheafOfModules.Pullback.pbAbIso_ι`; it
    is
filteredness of the neighbourhood category `N(U)`. -/
theorem exists_unit_rep (U : (Opens X)ᵒᵖ) (r : (pullbackRing f O).obj U)
    (m : ((pullbackModuleFunctor f O).obj G).obj U) :
    ∃ (V : (Opens Y)ᵒᵖ) (i : (Opens.map f).op.obj V ⟶ U) (a₀ : O.obj V) (m₀ : G.obj V),
      (pullbackRing f O).map i (pullbackRingUnit f O V a₀) = r ∧
        modRes f O G i (modUnit f O G V m₀) = m := by
  have : FinallySmall.{u} (CostructuredArrow (Opens.map f).op U) :=
    finallySmall_of_essentiallySmall _
  have : InitiallySmall.{u} ((CostructuredArrow (Opens.map f).op U)ᵒᵖ) := inferInstance
  obtain ⟨c, a₀, m₀, ha, hm⟩ := PresheafOfModules.ModuleColimit.jointly_surjective₂
    (hcR := colimit.isColimit (pbRdiag f O U))
    (hcM := colimit.isColimit (pbMmod f O G U).presheaf)
    ((pbRingIso f O U).ringCatIsoToRingEquiv.symm r)
    ((pbAbIso f O G U).symm.hom m)
  refine ⟨c.unop.unop.left, c.unop.unop.hom, a₀, m₀, ?_, ?_⟩
  · rw [← pbRingIso_ι f O U c a₀]
    rw [show colimit.ι (pbRdiag f O U) c a₀
        = (pbRingIso f O U).ringCatIsoToRingEquiv.symm r from ha]
    exact (pbRingIso f O U).ringCatIsoToRingEquiv.apply_symm_apply r
  · change (pullbackAb f (underlyingAb O G)).map c.unop.unop.hom
        (pullbackAbUnit f (underlyingAb O G) c.unop.unop.left m₀) = m
    rw [← pbAbIso_ι f O G U c m₀]
    rw [show colimit.ι (pbMmod f O G U).presheaf c m₀ = (pbAbIso f O G U).symm.hom m from hm]
    exact (pbAbIso f O G U).inv_hom_id_apply m

section Adjunction

variable {M : PresheafOfModules.{u} O} {N : PresheafOfModules.{u} (pullbackRing f O)}

/-- The abelian-group-level adjunction `f_p ⊣ f_*` on presheaves of abelian groups, through
which the module-level bijection is defined. -/
noncomputable abbrev abAdjunction :
    TopCat.Presheaf.pullback Ab.{u} f ⊣ TopCat.Presheaf.pushforward Ab.{u} f :=
  TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f

/-- Semilinearity of the restriction maps of a presheaf of `f_p O`-modules, read on the
underlying presheaf of abelian groups. -/
theorem presheaf_map_smul {U U' : (Opens X)ᵒᵖ} (i : U ⟶ U')
    (r : (pullbackRing f O).obj U) (y : N.obj U) :
    N.presheaf.map i (r • y) = (pullbackRing f O).map i r • N.presheaf.map i y :=
  PresheafOfModules.map_smul N i r y

/-- The underlying morphism of presheaves of abelian groups of a morphism out of `f_p M`,
spelled over `TopCat.Presheaf.pullback Ab f`. -/
noncomputable def abMap (φ : (pullbackModuleFunctor f O).obj M ⟶ N) :
    (TopCat.Presheaf.pullback Ab.{u} f).obj M.presheaf ⟶ N.presheaf :=
  (PresheafOfModules.toPresheaf _).map φ

/-- The underlying morphism of presheaves of abelian groups of a morphism into `η_* N`,
spelled over `TopCat.Presheaf.pushforward Ab f`. -/
noncomputable def abMapInv
    (ψ : M ⟶ (PresheafOfModules.pushforward (pullbackRingUnitHom f O)).obj N) :
    M.presheaf ⟶ (TopCat.Presheaf.pushforward Ab.{u} f).obj N.presheaf :=
  (PresheafOfModules.toPresheaf _).map ψ

/-- The underlying morphism of presheaves of abelian groups of a morphism out of `f_p M`,
transposed along the abelian-group-level adjunction. -/
noncomputable def abTranspose (φ : (pullbackModuleFunctor f O).obj M ⟶ N) :
    M.presheaf ⟶ (TopCat.Presheaf.pushforward Ab.{u} f).obj N.presheaf :=
  (abAdjunction f).homEquiv M.presheaf N.presheaf (abMap f O φ)

/-- `abTranspose` is the image of `abMap` under the hom-set bijection of `abAdjunction`. -/
theorem abTranspose_eq (φ : (pullbackModuleFunctor f O).obj M ⟶ N) :
    abTranspose f O φ = (abAdjunction f).homEquiv M.presheaf N.presheaf (abMap f O φ) :=
  rfl

/-- A section of the transpose, typed as a section of `N` over `f⁻¹V`, so that the
`(f_p O)(f⁻¹V)`-action on it is the one of `N`. -/
noncomputable abbrev abTransposeSect (φ : (pullbackModuleFunctor f O).obj M ⟶ N)
    (V : (Opens Y)ᵒᵖ) (m : M.obj V) : N.obj ((Opens.map f).op.obj V) :=
  (abTranspose f O φ).app V m

/-- `abTranspose` is the unit followed by the given morphism, on sections. -/
theorem abTransposeSect_eq (φ : (pullbackModuleFunctor f O).obj M ⟶ N) (V : (Opens Y)ᵒᵖ)
    (m : M.obj V) :
    abTransposeSect f O φ V m
      = φ.app ((Opens.map f).op.obj V) (modUnit f O M V m) := by
  rw [abTransposeSect, abTranspose_eq, Adjunction.homEquiv_unit, modUnit,
    pullbackAbUnit_eq_adjunction_unit]
  rfl

/-- **Semilinearity of `abTranspose`.**  The transposed map carries the `O(V)`-action to the
`(f_p O)(f⁻¹V)`-action along the Kan-extension unit: this is semilinearity of the unit
(`Stacks.PresheafOfModules.Pullback.modUnit_smul`) followed by the linearity of `φ`. -/
theorem abTransposeSect_smul (φ : (pullbackModuleFunctor f O).obj M ⟶ N) (V : (Opens Y)ᵒᵖ)
    (a : O.obj V) (m : M.obj V) :
    abTransposeSect f O φ V (a • m)
      = pullbackRingUnit f O V a • abTransposeSect f O φ V m := by
  rw [abTransposeSect_eq, abTransposeSect_eq, modUnit_smul]
  exact (φ.app ((Opens.map f).op.obj V)).hom.map_smul _ _

/-- **Forward direction of the adjunction.**  A morphism `f_p M ⟶ N` of presheaves of
`f_p O`-modules transposes to a morphism `M ⟶ η_* N` of presheaves of `O`-modules. -/
noncomputable def transposeHom (φ : (pullbackModuleFunctor f O).obj M ⟶ N) :
    M ⟶ (PresheafOfModules.pushforward (pullbackRingUnitHom f O)).obj N :=
  PresheafOfModules.homMk (abTranspose f O φ)
    (fun V a m => abTransposeSect_smul f O φ V a m)

/-- The underlying morphism of presheaves of abelian groups of a morphism into `η_* N`,
transposed along the abelian-group-level adjunction. -/
noncomputable def abTransposeInv
    (ψ : M ⟶ (PresheafOfModules.pushforward (pullbackRingUnitHom f O)).obj N) :
    (TopCat.Presheaf.pullback Ab.{u} f).obj M.presheaf ⟶ N.presheaf :=
  ((abAdjunction f).homEquiv M.presheaf N.presheaf).symm (abMapInv f O ψ)

/-- `abTransposeInv` is the image of `abMapInv` under the inverse of the hom-set bijection of
`abAdjunction`. -/
theorem abTransposeInv_eq
    (ψ : M ⟶ (PresheafOfModules.pushforward (pullbackRingUnitHom f O)).obj N) :
    abTransposeInv f O ψ
      = ((abAdjunction f).homEquiv M.presheaf N.presheaf).symm (abMapInv f O ψ) :=
  rfl

/-- A section of `ψ`, typed as a section of `N` over `f⁻¹V` rather than as a section of
`η_* N` over `V`, so that the scalar action on it is the `(f_p O)(f⁻¹V)`-action of `N`. -/
noncomputable abbrev psiSect
    (ψ : M ⟶ (PresheafOfModules.pushforward (pullbackRingUnitHom f O)).obj N)
    (V : (Opens Y)ᵒᵖ) (m : M.obj V) : N.obj ((Opens.map f).op.obj V) :=
  ψ.app V m

/-- Linearity of `ψ`, read through the restriction of scalars along `η.app V`: on sections of
`N` over `f⁻¹V` the `O(V)`-action becomes the action of the unit image. -/
theorem psiSect_smul
    (ψ : M ⟶ (PresheafOfModules.pushforward (pullbackRingUnitHom f O)).obj N)
    (V : (Opens Y)ᵒᵖ) (a : O.obj V) (m : M.obj V) :
    psiSect f O ψ V (a • m) = pullbackRingUnit f O V a • psiSect f O ψ V m :=
  (ψ.app V).hom.map_smul a m

/-- A section of the inverse transpose, typed as a section of `N`. -/
noncomputable abbrev abTransposeInvSect
    (ψ : M ⟶ (PresheafOfModules.pushforward (pullbackRingUnitHom f O)).obj N)
    (U : (Opens X)ᵒᵖ) (x : ((pullbackModuleFunctor f O).obj M).obj U) : N.obj U :=
  (abTransposeInv f O ψ).app U x

/-- `abTransposeInv` precomposed with the unit is the given morphism. -/
theorem abTransposeInvSect_unit
    (ψ : M ⟶ (PresheafOfModules.pushforward (pullbackRingUnitHom f O)).obj N)
    (V : (Opens Y)ᵒᵖ) (m : M.obj V) :
    abTransposeInvSect f O ψ ((Opens.map f).op.obj V) (modUnit f O M V m)
      = psiSect f O ψ V m := by
  have h : (abAdjunction f).homEquiv M.presheaf N.presheaf (abTransposeInv f O ψ)
      = abMapInv f O ψ := by
    rw [abTransposeInv_eq, Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_unit] at h
  have h3 : ((abAdjunction f).unit.app M.presheaf).app V ≫
      ((TopCat.Presheaf.pushforward Ab.{u} f).map (abTransposeInv f O ψ)).app V
      = (abMapInv f O ψ).app V := NatTrans.congr_app h V
  exact (ConcreteCategory.comp_apply (((abAdjunction f).unit.app M.presheaf).app V)
      (((TopCat.Presheaf.pushforward Ab.{u} f).map (abTransposeInv f O ψ)).app V) m).symm.trans
    (ConcreteCategory.congr_hom h3 m)

/-- Naturality of `abTransposeInv` in the open set, read on elements. -/
theorem abTransposeInvSect_res
    (ψ : M ⟶ (PresheafOfModules.pushforward (pullbackRingUnitHom f O)).obj N)
    {U U' : (Opens X)ᵒᵖ} (i : U ⟶ U')
    (x : ((pullbackModuleFunctor f O).obj M).obj U) :
    abTransposeInvSect f O ψ U' (modRes f O M i x)
      = N.presheaf.map i (abTransposeInvSect f O ψ U x) :=
  NatTrans.naturality_apply (abTransposeInv f O ψ) i x

/-- **Semilinearity of `abTransposeInv`.**  On sections over `U`, the inverse transpose is
`(f_p O)(U)`-linear. -/
theorem abTransposeInvSect_smul
    (ψ : M ⟶ (PresheafOfModules.pushforward (pullbackRingUnitHom f O)).obj N)
    (U : (Opens X)ᵒᵖ) (r : (pullbackRing f O).obj U)
    (m : ((pullbackModuleFunctor f O).obj M).obj U) :
    abTransposeInvSect f O ψ U (r • m) = r • abTransposeInvSect f O ψ U m := by
  obtain ⟨V, i, a₀, m₀, hr, hm⟩ := exists_unit_rep f O M U r m
  subst hr
  subst hm
  rw [← modRes_smul, ← modUnit_smul, abTransposeInvSect_res, abTransposeInvSect_res,
    abTransposeInvSect_unit, abTransposeInvSect_unit, psiSect_smul, presheaf_map_smul]
  rfl

/-- **Backward direction of the adjunction.** -/
noncomputable def transposeInv
    (ψ : M ⟶ (PresheafOfModules.pushforward (pullbackRingUnitHom f O)).obj N) :
    (pullbackModuleFunctor f O).obj M ⟶ N :=
  PresheafOfModules.homMk (abTransposeInv f O ψ)
    (fun U r m => abTransposeInvSect_smul f O ψ U r m)

/-- The underlying morphism of presheaves of abelian groups of `transposeHom φ` is
`abTranspose φ`. -/
theorem abMapInv_transposeHom (φ : (pullbackModuleFunctor f O).obj M ⟶ N) :
    abMapInv f O (transposeHom f O φ) = abTranspose f O φ :=
  rfl

/-- The underlying morphism of presheaves of abelian groups of `transposeInv ψ` is
`abTransposeInv ψ`. -/
theorem abMap_transposeInv
    (ψ : M ⟶ (PresheafOfModules.pushforward (pullbackRingUnitHom f O)).obj N) :
    abMap f O (transposeInv f O ψ) = abTransposeInv f O ψ :=
  rfl

/-- The hom-set bijection `Hom_{f_p O}(f_p M, N) ≃ Hom_O(M, η_* N)`: the abelian-group-level
bijection, both of whose directions preserve linearity. -/
noncomputable def pullbackModuleHomEquiv :
    ((pullbackModuleFunctor f O).obj M ⟶ N) ≃
      (M ⟶ (PresheafOfModules.pushforward (pullbackRingUnitHom f O)).obj N) where
  toFun := transposeHom f O
  invFun := transposeInv f O
  left_inv φ := by
    refine (PresheafOfModules.toPresheaf _).map_injective ?_
    change abMap f O (transposeInv f O (transposeHom f O φ)) = abMap f O φ
    rw [abMap_transposeInv, abTransposeInv_eq, abMapInv_transposeHom, abTranspose_eq,
      Equiv.symm_apply_apply]
  right_inv ψ := by
    refine (PresheafOfModules.toPresheaf _).map_injective ?_
    change abMapInv f O (transposeHom f O (transposeInv f O ψ)) = abMapInv f O ψ
    rw [abMapInv_transposeHom, abTranspose_eq, abMap_transposeInv, abTransposeInv_eq,
      Equiv.apply_symm_apply]

end Adjunction

/-- **Stacks 008T (3), adjoint form.**  The explicit pullback functor of presheaves of modules
is left adjoint to the pushforward along the Kan-extension unit `η : O ⟶ f_*(f_p O)`. -/
noncomputable def pullbackModuleAdjunction :
    pullbackModuleFunctor f O ⊣ PresheafOfModules.pushforward (pullbackRingUnitHom f O) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M N => pullbackModuleHomEquiv f O
      homEquiv_naturality_left_symm := by
        intro M' M N g ψ
        refine (PresheafOfModules.toPresheaf _).map_injective ?_
        change abMap f O (transposeInv f O (g ≫ ψ))
          = abMap f O ((pullbackModuleFunctor f O).map g ≫ transposeInv f O ψ)
        rw [abMap_transposeInv, abTransposeInv_eq]
        change ((abAdjunction f).homEquiv M'.presheaf N.presheaf).symm
            (abMapInv f O (g ≫ ψ))
          = (TopCat.Presheaf.pullback Ab.{u} f).map ((PresheafOfModules.toPresheaf O).map g) ≫
            abTransposeInv f O ψ
        rw [abTransposeInv_eq]
        exact (abAdjunction f).homEquiv_naturality_left_symm
          ((PresheafOfModules.toPresheaf O).map g) (abMapInv f O ψ)
      homEquiv_naturality_right := by
        intro M N N' φ h
        refine (PresheafOfModules.toPresheaf _).map_injective ?_
        change abMapInv f O (transposeHom f O (φ ≫ h))
          = abMapInv f O (transposeHom f O φ ≫
              (PresheafOfModules.pushforward (pullbackRingUnitHom f O)).map h)
        rw [abMapInv_transposeHom, abTranspose_eq]
        change (abAdjunction f).homEquiv M.presheaf N'.presheaf (abMap f O (φ ≫ h))
          = (abAdjunction f).homEquiv M.presheaf N.presheaf (abMap f O φ) ≫
            (TopCat.Presheaf.pushforward Ab.{u} f).map
              ((PresheafOfModules.toPresheaf (pullbackRing f O)).map h)
        exact (abAdjunction f).homEquiv_naturality_right (abMap f O φ)
          ((PresheafOfModules.toPresheaf (pullbackRing f O)).map h) }

/-- The pushforward of presheaves of modules along the Kan-extension unit
`η : O ⟶ f_*(f_p O)` is a right adjoint. -/
instance isRightAdjoint_pushforward_pullbackRingUnitHom :
    (PresheafOfModules.pushforward.{u} (pullbackRingUnitHom f O)).IsRightAdjoint :=
  (pullbackModuleAdjunction f O).isRightAdjoint

/-- **The concrete model of `PresheafOfModules.pullback`.**  Mathlib's abstract left adjoint of
`PresheafOfModules.pushforward η` is the objectwise filtered colimit of Stacks 008T,
`(f_p G)(U) = colim_{V, U ⊆ f⁻¹V} G(V)`, with the germwise scalar action. -/
noncomputable def pullbackIsoPullbackModuleFunctor :
    PresheafOfModules.pullback.{u} (pullbackRingUnitHom f O) ≅ pullbackModuleFunctor f O :=
  Adjunction.leftAdjointUniq
    (PresheafOfModules.pullbackPushforwardAdjunction (pullbackRingUnitHom f O))
    (pullbackModuleAdjunction f O)

end Stacks.PresheafOfModules.Pullback

end
