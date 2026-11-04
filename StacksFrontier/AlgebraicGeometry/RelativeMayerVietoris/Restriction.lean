module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Restriction maps between the direct images of the restrictions of a module

Let `X` be a scheme and `F` an `𝒪_X`-module. For an open `W` of `X` write

`pushRestrict F W := (Scheme.Modules.pushforward W.ι).obj (F.restrict W.ι)`,

the `𝒪_X`-module `j_{W,*} j_W^* F` whose sections over an open `T` are the sections of `F` over
`W ⊓ T`. For `W' ≤ W` we construct the restriction morphism

`resPush F h : pushRestrict F W ⟶ pushRestrict F W'`

and identify it on sections with a single restriction map of `F`. We also record the sheaf
condition of `F` for a two-element cover, as used in the degree-`0` relative Mayer–Vietoris
sequence of [Stacks, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC).

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeMayerVietoris.pushRestrict`: the module `j_{W,*} j_W^* F`.
* `Stacks.AlgebraicGeometry.RelativeMayerVietoris.resPush`: the restriction morphism for `W' ≤ W`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeMayerVietoris.resPush_app`: on sections over `T` the morphism
  `resPush F h` is `F.presheaf.map` of the inclusion `W'.ι ''ᵁ (W'.ι ⁻¹ᵁ T) ≤ W.ι ''ᵁ (W.ι ⁻¹ᵁ T)`.
* `Stacks.AlgebraicGeometry.RelativeMayerVietoris.resPush_comp`: the restriction morphisms compose.
* `Stacks.AlgebraicGeometry.RelativeMayerVietoris.exists_gluing₂`: sections over two opens covering
  `Z` that agree on an open between their intersection and themselves glue to a section over `Z`.
* `Stacks.AlgebraicGeometry.RelativeMayerVietoris.eq_of_res_eq₂`: sections over `Z` agreeing on two
  opens covering `Z` are equal.
* `Stacks.AlgebraicGeometry.RelativeMayerVietoris.injective_app_of_mono`: a monomorphism of
  `𝒪_X`-modules is injective on sections.

## References

* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.RelativeMayerVietoris

variable {X : Scheme.{u}}

/-! ### Two computations with opens -/

/-- The preimage of an open along a composition is the iterated preimage. -/
theorem comp_preimage {Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (T : Z.Opens) :
    (f ≫ g) ⁻¹ᵁ T = f ⁻¹ᵁ (g ⁻¹ᵁ T) :=
  rfl

/-- The image under the inclusion of an open `W` of the preimage of an open `T` is `W ⊓ T`. -/
theorem ι_image_preimage (W T : X.Opens) : W.ι ''ᵁ (W.ι ⁻¹ᵁ T) = W ⊓ T := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨⟨x, h₁⟩, h₂, rfl⟩

/-- Monotonicity of `W ↦ W.ι ''ᵁ (W.ι ⁻¹ᵁ T)`. -/
theorem image_preimage_mono {W W' : X.Opens} (h : W' ≤ W) (T : X.Opens) :
    W'.ι ''ᵁ (W'.ι ⁻¹ᵁ T) ≤ W.ι ''ᵁ (W.ι ⁻¹ᵁ T) := by
  simpa only [ι_image_preimage] using inf_le_inf_right T h

/-! ### Restriction maps on sections -/

/-- The restriction map of the underlying abelian presheaf of an `𝒪_X`-module. -/
noncomputable abbrev res (F : X.Modules) {P Q : X.Opens} (h : Q ≤ P) : Γ(F, P) ⟶ Γ(F, Q) :=
  F.presheaf.map (homOfLE h).op

/-- Restriction maps compose. -/
theorem res_res (F : X.Modules) {P Q R : X.Opens} (hQP : Q ≤ P) (hRQ : R ≤ Q) (hRP : R ≤ P)
    (x : Γ(F, P)) : res F hRQ (res F hQP x) = res F hRP x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-! ### The restriction morphism between direct images -/

/-- The `𝒪_X`-module `j_{W,*} j_W^* F`: the direct image along the inclusion of the open `W` of the
restriction of `F` to `W`. Its sections over an open `T` are the sections of `F` over `W ⊓ T`. -/
noncomputable abbrev pushRestrict (F : X.Modules) (W : X.Opens) : X.Modules :=
  (Scheme.Modules.pushforward W.ι).obj (F.restrict W.ι)

/-- The restriction morphism `j_{W,*} j_W^* F ⟶ j_{W',*} j_{W'}^* F` for `W' ≤ W`: the direct image
along `W.ι` of the unit of the restriction–pushforward adjunction for the open immersion
`X.homOfLE h : W' ⟶ W`, composed with the comparison isomorphisms that rewrite `(W' ⟶ W ⟶ X)` as
`W' ⟶ X`. -/
noncomputable def resPush (F : X.Modules) {W W' : X.Opens} (h : W' ≤ W) :
    pushRestrict F W ⟶ pushRestrict F W' :=
  (Scheme.Modules.pushforward W.ι).map
      ((Scheme.Modules.restrictAdjunction (X.homOfLE h)).unit.app (F.restrict W.ι)) ≫
    (Scheme.Modules.pushforwardComp (X.homOfLE h) W.ι).hom.app _ ≫
    (Scheme.Modules.pushforwardCongr (X.homOfLE_ι h)).hom.app _ ≫
    (Scheme.Modules.pushforward W'.ι).map
      ((Scheme.Modules.restrictFunctorComp (X.homOfLE h) W.ι).inv.app F ≫
        (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h)).hom.app F)

/-- `resPush` is a restriction map of `F` on sections: the sections of `pushRestrict F W` over `T`
are the sections of `F` over `W.ι ''ᵁ (W.ι ⁻¹ᵁ T)`, and `resPush F h` is the restriction along the
inclusion of the corresponding open for `W'`. -/
theorem resPush_app (F : X.Modules) {W W' : X.Opens} (h : W' ≤ W) (T : X.Opens) :
    (resPush F h).app T = res F (image_preimage_mono h T) := by
  simp only [resPush, Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.restrictAdjunction_unit_app_app, Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforwardCongr_hom_app_app, Scheme.Modules.restrictFunctorComp_inv_app_app,
    Scheme.Modules.restrictFunctorCongr_hom_app_app, Scheme.Modules.restrict_map]
  dsimp only [Scheme.Modules.pushforward_obj_obj, Scheme.Modules.restrict_obj, Functor.comp_obj,
    comp_preimage]
  rw [Category.id_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  rfl

/-- The restriction morphisms compose. -/
theorem resPush_comp (F : X.Modules) {W₀ W₁ W₂ : X.Opens} (h₁ : W₁ ≤ W₀) (h₂ : W₂ ≤ W₁) :
    resPush F h₁ ≫ resPush F h₂ = resPush F (h₂.trans h₁) := by
  refine Scheme.Modules.hom_ext _ _ fun T => ?_
  simp only [Scheme.Modules.Hom.comp_app, resPush_app]
  dsimp only [Scheme.Modules.pushforward_obj_obj, Scheme.Modules.restrict_obj]
  rw [← Functor.map_comp]
  rfl

/-! ### The sheaf condition in the form used by Mayer–Vietoris -/

/-- The underlying abelian sheaf of an `𝒪_X`-module. -/
noncomputable abbrev sheaf (F : X.Modules) : TopCat.Sheaf AddCommGrpCat.{u} X :=
  ⟨F.presheaf, F.isSheaf⟩

/-- Separatedness for a two-element cover: two sections over `Z` that agree on `P` and on `Q`
agree, provided `P` and `Q` cover `Z`. -/
theorem eq_of_res_eq₂ (F : X.Modules) {P Q Z : X.Opens} (hZ : Z ≤ P ⊔ Q) (hP : P ≤ Z)
    (hQ : Q ≤ Z) (a b : Γ(F, Z)) (h₁ : res F hP a = res F hP b) (h₂ : res F hQ a = res F hQ b) :
    a = b :=
  (sheaf F).eq_of_locally_eq₂ (homOfLE hP) (homOfLE hQ) hZ a b h₁ h₂

/-- Gluing for a two-element cover: let `P` and `Q` cover `Z`, and let `R` be an open with
`P ⊓ Q ≤ R ≤ P` and `R ≤ Q`. Sections `s` over `P` and `t` over `Q` whose restrictions to `R` agree
glue to a section over `Z`. -/
theorem exists_gluing₂ (F : X.Modules) {P Q R Z : X.Opens} (hZ : Z ≤ P ⊔ Q) (hP : P ≤ Z)
    (hQ : Q ≤ Z) (hRP : R ≤ P) (hRQ : R ≤ Q) (hR : P ⊓ Q ≤ R) (s : Γ(F, P)) (t : Γ(F, Q))
    (hst : res F hRP s = res F hRQ t) :
    ∃ a : Γ(F, Z), res F hP a = s ∧ res F hQ a = t := by
  have key : ∀ {P Q R : X.Opens} (hRP : R ≤ P) (hRQ : R ≤ Q) (hR : P ⊓ Q ≤ R) (s : Γ(F, P))
      (t : Γ(F, Q)), res F hRP s = res F hRQ t →
      res F (inf_le_left : P ⊓ Q ≤ P) s = res F (inf_le_right : P ⊓ Q ≤ Q) t :=
    fun hRP hRQ hR s t hst => by rw [← res_res F hRP hR _ s, hst, res_res F hRQ hR _ t]
  obtain ⟨a, ha, -⟩ := (sheaf F).existsUnique_gluing' (U := fun b : Bool => bif b then P else Q)
    Z (fun b => homOfLE (by cases b; exacts [hQ, hP]))
    (le_trans hZ (sup_le (le_iSup (fun b : Bool => bif b then P else Q) true)
      (le_iSup (fun b : Bool => bif b then P else Q) false)))
    (Bool.rec t s) (by
      rintro (_ | _) (_ | _)
      · rfl
      · exact key hRQ hRP (by rwa [inf_comm]) t s hst.symm
      · exact key hRP hRQ hR s t hst
      · rfl)
  exact ⟨a, ha true, ha false⟩

/-! ### Monomorphisms are injective on sections -/

/-- A monomorphism of `𝒪_X`-modules is injective on sections over every open. -/
theorem injective_app_of_mono {M N : X.Modules} (φ : M ⟶ N) [Mono φ] (T : X.Opens) :
    Function.Injective (φ.app T) := by
  have h : Mono ((Scheme.Modules.toPresheaf X).map φ) := preserves_mono_of_preservesLimit _ φ
  rw [NatTrans.mono_iff_mono_app] at h
  exact (AddCommGrpCat.mono_iff_injective _).mp (h (op T))

end Stacks.AlgebraicGeometry.RelativeMayerVietoris

end
