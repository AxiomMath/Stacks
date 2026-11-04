module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.BaseChangeTwistComposition

/-!
# Transport of a base change twist along an isomorphism of fibres

Let `pr : Yb ⟶ Yl` and `pr' : Yb' ⟶ Yl'` be morphisms of schemes, `gl : Yl' ⟶ Yl` and
`e : Yb' ⟶ Yb` with `pr' ≫ gl = e ≫ pr`.  The inverse images `gl⁻¹ ⋙ pr'⁻¹` and `pr⁻¹ ⋙ e⁻¹` are
both left adjoint to the direct image along `pr' ≫ gl = e ≫ pr`, hence canonically isomorphic;
together with the unit of `e⁻¹ ⊣ e_*` this gives the base change map
`pr⁻¹ L ⟶ e_* pr'⁻¹ gl⁻¹ L`, an isomorphism when `e` is, which intertwines the base change
twists attached to compatible endomorphisms of the two squares.

## Main definitions

* `Stacks.EtaleCohomology.smallEtalePushforwardEquivOfIso`: direct image along an isomorphism of
  schemes is an equivalence.
* `Stacks.EtaleCohomology.etaleModuleBaseChangeMap`: the base change map
  `pr⁻¹ ⟶ gl⁻¹ ⋙ pr'⁻¹ ⋙ e_*`.

## Main results

* `Stacks.EtaleCohomology.unit_comp_map_etaleModuleBaseChangeMap`: its adjoint.
* `Stacks.EtaleCohomology.isIso_etaleModuleBaseChangeMap_app`: it is an isomorphism when `e` is.
* `Stacks.EtaleCohomology.etaleModuleBaseChangeMap_comp_twist`: it intertwines the base change
  twists attached to compatible endomorphisms `(A, B)` and `(A', B')` of the two squares, given
  that `ψ : 𝟭 ⟶ B_*` and `ψ' : 𝟭 ⟶ B'_*` are compatible with `gl_*`.

## References

* [Stacks Project, Tag 03V0](https://stacks.math.columbia.edu/tag/03V0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

/-! ### Direct image along an isomorphism -/

section Iso

variable {X Y : Scheme.{u}} (e : X ≅ Y) (A : Type*) [Category* A]

/-- **Direct image along an isomorphism of schemes is an equivalence**, with inverse the direct
image along the inverse isomorphism. -/
def smallEtalePushforwardEquivOfIso :
    Sheaf (smallEtaleTopology X) A ≌ Sheaf (smallEtaleTopology Y) A :=
  CategoryTheory.Equivalence.mk (smallEtalePushforward e.hom A) (smallEtalePushforward e.inv A)
    ((Functor.sheafPushforwardContinuousId' (smallEtaleBaseChangeIdOf (𝟙 X) rfl) A _).symm ≪≫
      (smallEtalePushforwardComp' e.hom e.inv (𝟙 X) e.hom_inv_id.symm A).symm)
    (smallEtalePushforwardComp' e.inv e.hom (𝟙 Y) e.inv_hom_id.symm A ≪≫
      Functor.sheafPushforwardContinuousId' (smallEtaleBaseChangeIdOf (𝟙 Y) rfl) A _)

/-- Direct image along the underlying morphism of an isomorphism of schemes is an equivalence. -/
instance isEquivalence_smallEtalePushforward_hom :
    (smallEtalePushforward e.hom A).IsEquivalence :=
  CategoryTheory.Equivalence.isEquivalence_functor (smallEtalePushforwardEquivOfIso e A)

end Iso

/-! ### The base change map -/

section BaseChangeMap

variable (Λ : Type r) [Ring Λ] {Yb Yb' Yl Yl' : Scheme.{u}} (pr : Yb ⟶ Yl) (pr' : Yb' ⟶ Yl')
  (gl : Yl' ⟶ Yl) (e : Yb' ⟶ Yb) (n : Yb' ⟶ Yl) (hn : n = pr' ≫ gl) (hn' : n = e ≫ pr)

/-- The two inverse images along the two sides of the square `pr' ≫ gl = e ≫ pr` agree: both are
left adjoint to the direct image along the diagonal. -/
def etaleModuleBaseChangeUnitIso :
    etaleModuleInverseImage.{u, r} Λ pr ⋙ etaleModuleInverseImage.{u, r} Λ e ≅
      etaleModuleInverseImage.{u, r} Λ gl ⋙ etaleModuleInverseImage.{u, r} Λ pr' :=
  ((etaleModuleInverseImageAdj.{u, r} Λ pr).comp
    (etaleModuleInverseImageAdj.{u, r} Λ e)).leftAdjointUniq
    (((etaleModuleInverseImageAdj.{u, r} Λ gl).comp
      (etaleModuleInverseImageAdj.{u, r} Λ pr')).ofNatIsoRight
      (etaleModuleDirectImageComp.{u, r} Λ pr' gl n hn ≪≫
        (etaleModuleDirectImageComp.{u, r} Λ e pr n hn').symm))

/-- **The base change map** `pr⁻¹ L ⟶ e_* pr'⁻¹ gl⁻¹ L`: the unit of `e⁻¹ ⊣ e_*` followed by
`e_*` of the identification `e⁻¹ pr⁻¹ ≅ pr'⁻¹ gl⁻¹`. -/
def etaleModuleBaseChangeMap :
    etaleModuleInverseImage.{u, r} Λ pr ⟶
      (etaleModuleInverseImage.{u, r} Λ gl ⋙ etaleModuleInverseImage.{u, r} Λ pr') ⋙
        etaleModuleDirectImage.{u, r} Λ e :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft _ (etaleModuleInverseImageAdj.{u, r} Λ e).unit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (etaleModuleBaseChangeUnitIso Λ pr pr' gl e n hn hn').hom _

/-- The component of the base change map at `L` is the unit of `e⁻¹ ⊣ e_*` at `pr⁻¹ L` followed
by `e_*` of the identification `e⁻¹ pr⁻¹ L ≅ pr'⁻¹ gl⁻¹ L`. -/
lemma etaleModuleBaseChangeMap_app (L : EtaleModules.{u, r} Λ Yl) :
    (etaleModuleBaseChangeMap Λ pr pr' gl e n hn hn').app L =
      (etaleModuleInverseImageAdj.{u, r} Λ e).unit.app
        ((etaleModuleInverseImage.{u, r} Λ pr).obj L) ≫
        (etaleModuleDirectImage.{u, r} Λ e).map
          ((etaleModuleBaseChangeUnitIso Λ pr pr' gl e n hn hn').hom.app L) := by
  simp [etaleModuleBaseChangeMap]

/-- **The adjoint of the base change map** is the unit of `gl⁻¹ ⊣ gl_*`, then `gl_*` of the unit
of `pr'⁻¹ ⊣ pr'_*`, then `gl_* pr'_* = (pr' ≫ gl)_* = (e ≫ pr)_* = pr_* e_*`. -/
lemma unit_comp_map_etaleModuleBaseChangeMap (L : EtaleModules.{u, r} Λ Yl) :
    (etaleModuleInverseImageAdj.{u, r} Λ pr).unit.app L ≫
        (etaleModuleDirectImage.{u, r} Λ pr).map
          ((etaleModuleBaseChangeMap Λ pr pr' gl e n hn hn').app L) =
      (etaleModuleInverseImageAdj.{u, r} Λ gl).unit.app L ≫
        (etaleModuleDirectImage.{u, r} Λ gl).map
          ((etaleModuleInverseImageAdj.{u, r} Λ pr').unit.app
            ((etaleModuleInverseImage.{u, r} Λ gl).obj L)) ≫
        (etaleModuleDirectImageComp.{u, r} Λ pr' gl n hn).hom.app
          ((etaleModuleInverseImage.{u, r} Λ pr').obj
            ((etaleModuleInverseImage.{u, r} Λ gl).obj L)) ≫
        (etaleModuleDirectImageComp.{u, r} Λ e pr n hn').inv.app
          ((etaleModuleInverseImage.{u, r} Λ pr').obj
            ((etaleModuleInverseImage.{u, r} Λ gl).obj L)) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((etaleModuleInverseImageAdj.{u, r} Λ pr).comp (etaleModuleInverseImageAdj.{u, r} Λ e))
    (((etaleModuleInverseImageAdj.{u, r} Λ gl).comp
      (etaleModuleInverseImageAdj.{u, r} Λ pr')).ofNatIsoRight
      (etaleModuleDirectImageComp.{u, r} Λ pr' gl n hn ≪≫
        (etaleModuleDirectImageComp.{u, r} Λ e pr n hn').symm)) L
  have hu : (((etaleModuleInverseImageAdj.{u, r} Λ gl).comp
      (etaleModuleInverseImageAdj.{u, r} Λ pr')).ofNatIsoRight
        (etaleModuleDirectImageComp.{u, r} Λ pr' gl n hn ≪≫
          (etaleModuleDirectImageComp.{u, r} Λ e pr n hn').symm)).unit.app L =
      ((etaleModuleInverseImageAdj.{u, r} Λ gl).comp
        (etaleModuleInverseImageAdj.{u, r} Λ pr')).unit.app L ≫
        (etaleModuleDirectImageComp.{u, r} Λ pr' gl n hn ≪≫
          (etaleModuleDirectImageComp.{u, r} Λ e pr n hn').symm).hom.app _ := by
    rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_id]
  rw [hu, Adjunction.comp_unit_app, Adjunction.comp_unit_app] at h
  rw [etaleModuleBaseChangeMap_app, Functor.map_comp, ← Category.assoc]
  simpa [etaleModuleBaseChangeUnitIso] using h

/-- **The base change map is an isomorphism when `e` is.** -/
lemma isIso_etaleModuleBaseChangeMap_app [IsIso e] (L : EtaleModules.{u, r} Λ Yl) :
    IsIso ((etaleModuleBaseChangeMap Λ pr pr' gl e n hn hn').app L) := by
  have : (etaleModuleDirectImage.{u, r} Λ e).IsEquivalence :=
    isEquivalence_smallEtalePushforward_hom (asIso e) (ModuleCat.{max (u + 1) r} Λ)
  have : (etaleModuleInverseImage.{u, r} Λ e).IsEquivalence :=
    (etaleModuleInverseImageAdj.{u, r} Λ e).isEquivalence_left_of_isEquivalence_right
  rw [etaleModuleBaseChangeMap_app]
  infer_instance

end BaseChangeMap

/-! ### The base change map intertwines the twists -/

section Heart

variable (Λ : Type r) [Ring Λ] {Yb Yb' Yl Yl' : Scheme.{u}} (pr : Yb ⟶ Yl) (pr' : Yb' ⟶ Yl')
  (gl : Yl' ⟶ Yl) (e : Yb' ⟶ Yb) (n : Yb' ⟶ Yl) (hn : n = pr' ≫ gl) (hn' : n = e ≫ pr)
  (A : Yb ⟶ Yb) (B : Yl ⟶ Yl) (w : A ≫ pr = pr ≫ B) (A' : Yb' ⟶ Yb') (B' : Yl' ⟶ Yl')
  (w' : A' ≫ pr' = pr' ≫ B') (eA : Yb' ⟶ Yb) (heA : eA = A' ≫ e) (heA' : eA = e ≫ A)
  (m : Yl' ⟶ Yl) (hm : m = B' ≫ gl) (hm' : m = gl ≫ B)
  (ψ : 𝟭 (EtaleModules.{u, r} Λ Yl) ⟶ etaleModuleDirectImage.{u, r} Λ B)
  (ψ' : 𝟭 (EtaleModules.{u, r} Λ Yl') ⟶ etaleModuleDirectImage.{u, r} Λ B')

/-- Pasting two commutative squares. -/
private lemma pasteSquares {D : Type*} [Category* D] {O₁ O₂ O₃ O₄ O₅ O₆ : D} {x : O₁ ⟶ O₂}
    {a' : O₂ ⟶ O₃} {a : O₁ ⟶ O₄} {y : O₄ ⟶ O₃} {b' : O₃ ⟶ O₆} {b : O₄ ⟶ O₅} {z : O₅ ⟶ O₆}
    (h₁ : x ≫ a' = a ≫ y) (h₂ : y ≫ b' = b ≫ z) : a ≫ b ≫ z = x ≫ a' ≫ b' := by
  rw [← h₂, ← reassoc_of% h₁]

/-- A functor carries the composite of two inverse pairs to an inverse pair. -/
private lemma map_inverse_pairs {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {X Y Z : C} {a : X ⟶ Y} {a' : Y ⟶ X} {b : Y ⟶ Z} {b' : Z ⟶ Y} (ha : a ≫ a' = 𝟙 _)
    (hb : b ≫ b' = 𝟙 _) : F.map a ≫ F.map b ≫ F.map (b' ≫ a') = 𝟙 _ := by
  rw [← F.map_comp, ← F.map_comp, ← Category.assoc b, hb, Category.id_comp, ha, F.map_id]

/-- If `g ≫ h = p ≫ c₅`, `h ≫ c₆ = 𝟙` and `η ≫ p = ψ ≫ Bη`, then `η ≫ g = ψ ≫ Bη ≫ c₅ ≫ c₆`. -/
private lemma solve_compat {D : Type*} [Category* D] {L G₁ M₁ M₃ P K : D} {η : L ⟶ G₁}
    {g : G₁ ⟶ M₁} {h : M₁ ⟶ K} {p : G₁ ⟶ P} {c₅ : P ⟶ K} {c₆ : K ⟶ M₁} {ψ : L ⟶ M₃}
    {Bη : M₃ ⟶ P} (hG : g ≫ h = p ≫ c₅) (hhi : h ≫ c₆ = 𝟙 _) (hψn : η ≫ p = ψ ≫ Bη) :
    η ≫ g = ψ ≫ Bη ≫ c₅ ≫ c₆ := by
  have hg : g = p ≫ c₅ ≫ c₆ := by
    rw [← Category.assoc, ← hG, Category.assoc, hhi, Category.comp_id]
  rw [hg, reassoc_of% hψn]

/-- **The base change map intertwines the base change twists.**  If `ψ'` is carried to `ψ` by
`gl_*`, then the base change map `pr⁻¹ L ⟶ e_* pr'⁻¹ gl⁻¹ L` followed by `e_*` of the twist of
`(A', B', ψ')` at `gl⁻¹ L` and the identification `e_* A'_* = (A' ≫ e)_* = (e ≫ A)_* = A_* e_*` is
the twist of `(A, B, ψ)` at `L` followed by `A_*` of the base change map. -/
theorem etaleModuleBaseChangeMap_comp_twist
    (hψ : ∀ M, (etaleModuleDirectImage.{u, r} Λ gl).map (ψ'.app M) ≫
        (etaleModuleDirectImageComp.{u, r} Λ B' gl m hm).hom.app M =
      ψ.app ((etaleModuleDirectImage.{u, r} Λ gl).obj M) ≫
        (etaleModuleDirectImageComp.{u, r} Λ gl B m hm').hom.app M)
    (L : EtaleModules.{u, r} Λ Yl) :
    (etaleModuleBaseChangeMap Λ pr pr' gl e n hn hn').app L ≫
        (etaleModuleDirectImage.{u, r} Λ e).map
          ((etaleModuleBaseChangeTwist.{u, r} Λ pr' A' B' w' ψ').app
            ((etaleModuleInverseImage.{u, r} Λ gl).obj L)) ≫
        ((etaleModuleDirectImageComp.{u, r} Λ A' e eA heA).hom.app
            ((etaleModuleInverseImage.{u, r} Λ pr').obj
              ((etaleModuleInverseImage.{u, r} Λ gl).obj L)) ≫
          (etaleModuleDirectImageComp.{u, r} Λ e A eA heA').inv.app
            ((etaleModuleInverseImage.{u, r} Λ pr').obj
              ((etaleModuleInverseImage.{u, r} Λ gl).obj L))) =
      (etaleModuleBaseChangeTwist.{u, r} Λ pr A B w ψ).app L ≫
        (etaleModuleDirectImage.{u, r} Λ A).map
          ((etaleModuleBaseChangeMap Λ pr pr' gl e n hn hn').app L) := by
  apply ((etaleModuleInverseImageAdj.{u, r} Λ pr).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  rw [Functor.map_comp (etaleModuleDirectImage.{u, r} Λ pr)
      ((etaleModuleBaseChangeMap Λ pr pr' gl e n hn hn').app L),
    Functor.map_comp (etaleModuleDirectImage.{u, r} Λ pr)
      ((etaleModuleDirectImage.{u, r} Λ e).map _),
    Functor.map_comp (etaleModuleDirectImage.{u, r} Λ pr)
      ((etaleModuleBaseChangeTwist.{u, r} Λ pr A B w ψ).app L)]
  have hPsi := unit_comp_map_etaleModuleBaseChangeMap Λ pr pr' gl e n hn hn' L
  have hTw := unit_comp_map_etaleModuleBaseChangeTwist Λ pr A B w ψ L
  have hTw' := congrArg (etaleModuleDirectImage.{u, r} Λ gl).map
    (unit_comp_map_etaleModuleBaseChangeTwist Λ pr' A' B' w' ψ'
      ((etaleModuleInverseImage.{u, r} Λ gl).obj L))
  have hn₁ := (etaleModuleDirectImageComp.{u, r} Λ pr' gl n hn).hom.naturality
    ((etaleModuleBaseChangeTwist.{u, r} Λ pr' A' B' w' ψ').app
      ((etaleModuleInverseImage.{u, r} Λ gl).obj L))
  have hn₂ := (etaleModuleDirectImageComp.{u, r} Λ e pr n hn').inv.naturality
    ((etaleModuleBaseChangeTwist.{u, r} Λ pr' A' B' w' ψ').app
      ((etaleModuleInverseImage.{u, r} Λ gl).obj L))
  have hG := hψ ((etaleModuleInverseImage.{u, r} Λ gl).obj L)
  have hψn := ψ.naturality ((etaleModuleInverseImageAdj.{u, r} Λ gl).unit.app L)
  have hn₅ := (etaleModuleDirectImageComp.{u, r} Λ gl B m hm').hom.naturality
    ((etaleModuleInverseImageAdj.{u, r} Λ pr').unit.app
      ((etaleModuleInverseImage.{u, r} Λ gl).obj L))
  have hn₆ := (etaleModuleDirectImageComp.{u, r} Λ B' gl m hm).inv.naturality
    ((etaleModuleInverseImageAdj.{u, r} Λ pr').unit.app
      ((etaleModuleInverseImage.{u, r} Λ gl).obj L))
  have hn₇ := (etaleModuleDirectImageComp.{u, r} Λ pr B (A ≫ pr) w).hom.naturality
    ((etaleModuleBaseChangeMap Λ pr pr' gl e n hn hn').app L)
  have hn₈ := (etaleModuleDirectImageComp.{u, r} Λ A pr (A ≫ pr) rfl).inv.naturality
    ((etaleModuleBaseChangeMap Λ pr pr' gl e n hn hn').app L)
  have hco := smallEtalePushforward_twistTransport_coherence pr pr' gl e n hn hn'
    A B w A' B' w' eA heA heA' m hm hm' (ModuleCat.{max (u + 1) r} Λ)
    ((etaleModuleInverseImage.{u, r} Λ pr').obj ((etaleModuleInverseImage.{u, r} Λ gl).obj L))
  have hBPsi := congrArg (etaleModuleDirectImage.{u, r} Λ B).map hPsi
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.id_map]
    at hn₁ hn₂ hψn hn₅ hn₆ hn₇ hn₈
  refine twistTransport_rearrange (Psi := hPsi) (N1 := ?_) (Tw' := ?_) (G2' := ?_) (N2 := ?_)
    (CohT := hco) (hinv := ?_) (Tw := hTw) (N3 := ?_) (BPsi := ?_)
    (Bv := (etaleModuleDirectImage.{u, r} Λ B).map ((etaleModuleDirectImage.{u, r} Λ pr).map
      ((etaleModuleBaseChangeMap Λ pr pr' gl e n hn hn').app L)))
    (Bc1 := (etaleModuleDirectImage.{u, r} Λ B).map
      ((etaleModuleDirectImageComp.{u, r} Λ pr' gl n hn).hom.app
        ((etaleModuleInverseImage.{u, r} Λ pr').obj ((etaleModuleInverseImage.{u, r} Λ gl).obj L))))
    (Bc2 := (etaleModuleDirectImage.{u, r} Λ B).map
      ((etaleModuleDirectImageComp.{u, r} Λ e pr n hn').inv.app
        ((etaleModuleInverseImage.{u, r} Λ pr').obj ((etaleModuleInverseImage.{u, r} Λ gl).obj L))))
    (gt := (etaleModuleDirectImage.{u, r} Λ gl).map ((etaleModuleDirectImage.{u, r} Λ pr').map
      ((etaleModuleBaseChangeTwist.{u, r} Λ pr' A' B' w' ψ').app
        ((etaleModuleInverseImage.{u, r} Λ gl).obj L))))
    (gψ' := (etaleModuleDirectImage.{u, r} Λ gl).map (ψ'.app
      ((etaleModuleInverseImage.{u, r} Λ gl).obj L)))
    (gBη := (etaleModuleDirectImage.{u, r} Λ gl).map ((etaleModuleDirectImage.{u, r} Λ B').map
      ((etaleModuleInverseImageAdj.{u, r} Λ pr').unit.app
        ((etaleModuleInverseImage.{u, r} Λ gl).obj L))))
    (Bηg := (etaleModuleDirectImage.{u, r} Λ B).map
      ((etaleModuleInverseImageAdj.{u, r} Λ gl).unit.app L))
    (c5 := (etaleModuleDirectImageComp.{u, r} Λ gl B m hm').hom.app
      ((etaleModuleInverseImage.{u, r} Λ gl).obj L))
    (c6 := (etaleModuleDirectImageComp.{u, r} Λ B' gl m hm).inv.app
      ((etaleModuleInverseImage.{u, r} Λ gl).obj L))
    (Bgη := (etaleModuleDirectImage.{u, r} Λ B).map ((etaleModuleDirectImage.{u, r} Λ gl).map
      ((etaleModuleInverseImageAdj.{u, r} Λ pr').unit.app
        ((etaleModuleInverseImage.{u, r} Λ gl).obj L))))
  · exact pasteSquares hn₁ hn₂
  · rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
    exact hTw'
  · exact solve_compat hG (Iso.hom_inv_id_app _ _) hψn
  · exact pasteSquares hn₅ hn₆
  · exact map_inverse_pairs _ (Iso.hom_inv_id_app _ _) (Iso.inv_hom_id_app _ _)
  · exact (Category.assoc _ _ _).trans (pasteSquares hn₇ hn₈)
  · simpa only [Functor.map_comp] using hBPsi

end Heart

end Stacks.EtaleCohomology

end
