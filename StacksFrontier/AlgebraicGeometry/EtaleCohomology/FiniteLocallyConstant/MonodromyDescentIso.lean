module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.GaloisTrivializationExists

/-!
# A finite type locally constant sheaf is a descent sheaf of a Galois cover

Let `X` be an irreducible geometrically unibranch scheme with a geometric point `x`, and `F` a
finite type locally constant sheaf of `Λ`-modules on `X_étale`. Then there are a pointed Galois
cover `A` of `X` and a finitely generated `Λ`-module `N` with an action of `π₁(X, x)` trivial on
the stabilizer of `A`, such that `F` is the descent sheaf of `N` along `A`: the sheaf whose
sections over an étale `W ⟶ X` are the `Aut(A)`-equivariant locally constant maps
`W ×_X A → N`. The module `N` is the monodromy module of `F`.

This is the form in which Step 3 of the proof of [Stacks, Tag 03UG] uses the Galois covering
trivializing the sheaf.

## Main results

* `AlgebraicGeometry.exists_iso_monodromyDescentSheaf`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory Opposite

universe u r v

namespace AlgebraicGeometry

open Stacks.GroupCohomology

attribute [local instance] Stacks.DiscreteModuleTopology.hasForget₂ModuleCatTopCat
  Stacks.DiscreteModuleTopology.actionDiscreteTopology

variable {X : Scheme.{u}} [IrreducibleSpace X] (hX : IsGeometricallyUnibranch X)
  (x : GeometricPoint X) {Λ : Type r} [Ring Λ]

/-- **A finite type locally constant sheaf is the descent sheaf of its monodromy module along a
pointed Galois cover.** -/
theorem exists_iso_monodromyDescentSheaf
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)) (hF : ftlcProperty X Λ F) :
    ∃ (A : PointedGaloisCover x) (N : Action (ModuleCat.{max (u + 1) r} Λ)
        (EtaleFundamentalGroup X x))
      (hN : ∀ σ, galoisAut x σ A = 1 → actionLinearRepr N σ = 1),
      Module.Finite Λ N.V ∧ Nonempty (F ≅ monodromyDescentSheaf hX A N hN) := by
  let htriv := trivializedByPointedGaloisCovers hX x Λ
  let Φ := monodromyFTLCFunctor (Λ := Λ) hX htriv
  let N := Φ.obj ⟨F, hF⟩
  obtain ⟨K, -, hKo, hK⟩ :=
    exists_isOpen_normal_subgroup_ρ_eq_one_finiteType Λ (EtaleFundamentalGroup X x) N
  obtain ⟨A, hA⟩ := exists_pointedGaloisCover_subset x (hKo.mem_nhds K.one_mem)
  let N₀ := N.obj.obj.obj
  have hN : ∀ σ, galoisAut x σ A = 1 → actionLinearRepr N₀ σ = 1 := fun σ hσ ↦ by
    have h1 : N₀.ρ σ = 1 := hK σ (hA hσ)
    show ModuleCat.Hom.hom (N₀.ρ σ) = 1
    rw [h1]
    rfl
  have : Module.Finite Λ N₀.V := N.property
  let D := monodromyDescentSheaf hX A N₀ hN
  have hD : ftlcProperty X Λ D :=
    (A.etaleGaloisCovering hX).isFiniteTypeLocallyConstant_descentSheaf Λ N₀.V _
  let e : GaloisTrivialization A D (ModuleCat.of Λ N₀.V) :=
    (A.etaleGaloisCovering hX).trivialization Λ N₀.V _
  let E := (e.monodromyEquiv hX).symm.trans (monodromyDescentSectionsEquiv hX A N₀ hN)
  let I : Φ.obj ⟨D, hD⟩ ≅ N := ObjectProperty.isoMk _ (ObjectProperty.isoMk _
    (ObjectProperty.isoMk _ (Action.mkIso E.toModuleIso fun σ ↦ by
      refine ModuleCat.hom_ext (LinearMap.ext fun v ↦ ?_)
      obtain ⟨d, rfl⟩ := (e.monodromyEquiv hX).surjective v
      have h1 : (((monodromyAction x).obj D.obj).ρ σ).hom (e.monodromyEquiv hX d) =
          e.monodromyEquiv hX
            (D.obj.map ((finiteEtaleToEtale X).map (galoisAutHom x σ A)).op d) :=
        monodromyAction_ρ_ι_apply D.obj σ (op A) d
      show E ((((monodromyAction x).obj D.obj).ρ σ).hom (e.monodromyEquiv hX d)) =
        (N₀.ρ σ).hom (E (e.monodromyEquiv hX d))
      rw [h1]
      show monodromyDescentSectionsEquiv hX A N₀ hN ((e.monodromyEquiv hX).symm
          (e.monodromyEquiv hX _)) =
        (N₀.ρ σ).hom (monodromyDescentSectionsEquiv hX A N₀ hN ((e.monodromyEquiv hX).symm
          (e.monodromyEquiv hX d)))
      rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
      exact monodromyDescentSectionsEquiv_map hX A N₀ hN σ d)))
  exact ⟨A, N₀, hN, inferInstance,
    ⟨(ftlcProperty X Λ).ι.mapIso (Φ.preimageIso I.symm)⟩⟩

/-! ### Changing the group of a Galois covering along an isomorphism -/

namespace EtaleGaloisCovering

variable {X : Scheme.{u}} {H H' : Type*} [Group H] [Group H'] (G : EtaleGaloisCovering X H)
  (e : H' ≃* H)

/-- **A Galois covering with group `H` is a Galois covering with any group isomorphic to `H`.** -/
def comapMulEquiv : EtaleGaloisCovering X H' where
  cover := G.cover
  act h := G.act (e h)
  act_comp_hom h := G.act_comp_hom _
  act_one := by rw [map_one, G.act_one]
  act_mul h h' := by rw [map_mul, G.act_mul]
  surjective := G.surjective
  irreducibleSpace := G.irreducibleSpace
  exists_mem_agreeLocus a b hab w := by
    obtain ⟨h, hw, hmem⟩ := G.exists_mem_agreeLocus a b hab w
    have he : e (e.symm h) = h := e.apply_symm_apply h
    exact ⟨e.symm h, by rw [he]; exact hw, by convert hmem using 4⟩
  eq_of_comp_eq c _ _ hc := e.injective (G.eq_of_comp_eq c hc)

/-- The action of `h` on `W ×_X A` for the covering with group `H'` is that of `e h` for the
covering with group `H`. -/
theorem pullbackAct_comapMulEquiv (W : X.Etale) (h : H') :
    (G.comapMulEquiv e).pullbackAct W h = G.pullbackAct W (e h) :=
  rfl

variable (Λ : Type r) [Ring Λ] (N : Type (max (u + 1) v)) [AddCommGroup N] [Module Λ N]
  (ρ : H →* Module.End Λ N)

/-- The `ρ ∘ e`-equivariant maps for the covering with group `H'` are the `ρ`-equivariant maps for
the covering with group `H`. -/
theorem equivariantMaps_comapMulEquiv (W : X.Etale) :
    (G.comapMulEquiv e).equivariantMaps Λ N (ρ.comp e.toMonoidHom) W =
      G.equivariantMaps Λ N ρ W := by
  ext f
  refine ⟨fun hf h z => ?_, fun hf h z => hf (e h) z⟩
  have := hf (e.symm h) z
  rw [pullbackAct_comapMulEquiv] at this
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulEquiv.apply_symm_apply] at this
  exact this

/-- **The descent sheaf does not change along an isomorphism of groups.** -/
def descentSheafComapMulEquivIso :
    (G.comapMulEquiv e).descentSheaf Λ N (ρ.comp e.toMonoidHom) ≅ G.descentSheaf Λ N ρ :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents
      (fun W => (LinearEquiv.ofEq _ _ (G.equivariantMaps_comapMulEquiv e Λ N ρ W.unop)).toModuleIso)
      (fun _ => rfl))

end EtaleGaloisCovering

/-! ### A Galois covering with a finite group in the lowest universe -/

section Small

include hX x in
/-- **A finite type locally constant sheaf is a descent sheaf along a connected finite étale
Galois covering with a finite group** (taken in `Type`, as the group rings of Steps 7 and 8 of
the proof of [Stacks, Tag 03UG] require). -/
theorem exists_etaleGaloisCovering_iso_descentSheaf
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)) (hF : ftlcProperty X Λ F) :
    ∃ (H : Type) (_ : Group H) (_ : Fintype H) (G : EtaleGaloisCovering X H)
      (N : Type (max (u + 1) r)) (_ : AddCommGroup N) (_ : Module Λ N)
      (ρ : H →* Module.End Λ N),
      Module.Finite Λ N ∧ IsFinite G.cover.hom ∧ ConnectedSpace G.cover.left ∧
        Nonempty (F ≅ G.descentSheaf Λ N ρ) := by
  obtain ⟨A, N, hN, hfin, ⟨eF⟩⟩ := exists_iso_monodromyDescentSheaf hX x F hF
  let G₀ := A.etaleGaloisCovering hX
  have : Finite (Aut A.obj) := inferInstance
  let e : Shrink.{0} (Aut A.obj) ≃* Aut A.obj := Shrink.mulEquiv
  have : Fintype (Shrink.{0} (Aut A.obj)) := Fintype.ofFinite _
  refine ⟨Shrink.{0} (Aut A.obj), inferInstance, inferInstance, G₀.comapMulEquiv e, N.V,
    inferInstance, inferInstance, (autRepresentation A (actionLinearRepr N) hN).comp e.toMonoidHom,
    hfin, ?_, A.connectedSpace, ⟨eF ≪≫ (G₀.descentSheafComapMulEquivIso e Λ N.V _).symm⟩⟩
  exact inferInstanceAs (IsFinite A.obj.hom)

end Small

end AlgebraicGeometry

end
