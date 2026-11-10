module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutFiniteOrder

/-!
# The leg of a pushout along a finite order thickening is a finite order thickening

Let `i : Z ⟶ Z'` be a finite order thickening and `f : Z ⟶ Y` an affine morphism of schemes, and
let `Y' = Y ⨿_Z Z'` be a pushout. Then `b : Y ⟶ Y'` is again a thickening of finite order, of the
same order as `i`: [Stacks Project, Tag 07RT] says that `b` is a thickening, and the structure
sheaf `𝒪_{Y'} = 𝒪_Y ×_{f_*𝒪_Z} f'_*𝒪_{Z'}` it describes carries the kernel of `𝒪_{Y'} ⟶ 𝒪_Y`
into the kernel of `𝒪_{Z'} ⟶ 𝒪_Z`, so the power killing the second kills the first.

## Main results

* `Stacks.Thickenings.ker_app_pow_eq_bot_of_isNthOrderThickening`: for an `n`th order thickening
  `i`, the kernel of `i.app V` has vanishing `(n + 1)`st power over *every* open `V`, affine or
  not.
* `Stacks.Thickenings.ringHomKer_pow_eq_bot_of_isPullback`: in a cartesian square of commutative
  rings, nilpotence of a kernel of given order passes to the opposite map.
* `Stacks.Pushout.isNthOrderThickening_of_isPushout`: the leg `Y ⟶ Y'` of a pushout along an
  `n`th order thickening and an affine morphism is an `n`th order thickening.
* `Stacks.Pushout.isFiniteOrderThickening_of_isPushout`: the same for finite order.

## References

* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.Thickenings

/-- In a commuting square of rings, if the kernel of the bottom-left map has vanishing
`(n + 1)`st power, the left map kills the `(n + 1)`st power of the kernel of the top map. -/
private theorem map_eq_zero_of_pow_ker_eq_bot {R S T U : Type*} [CommRing R] [CommRing S]
    [CommRing T] [CommRing U] (ρ : R →+* S) (k : R →+* T) (k' : S →+* U) (r : T →+* U)
    (hsq : k'.comp ρ = r.comp k) {n : ℕ} (hk' : RingHom.ker k' ^ (n + 1) = ⊥) {x : R}
    (hx : x ∈ RingHom.ker k ^ (n + 1)) : ρ x = 0 := by
  have hle : Ideal.map ρ (RingHom.ker k) ≤ RingHom.ker k' := by
    refine Ideal.map_le_iff_le_comap.2 fun z hz => ?_
    rw [RingHom.mem_ker] at hz
    rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, hsq, RingHom.comp_apply, hz,
      map_zero]
  have hmem : ρ x ∈ Ideal.map ρ (RingHom.ker k ^ (n + 1)) := Ideal.mem_map_of_mem _ hx
  rw [Ideal.map_pow] at hmem
  have := Ideal.pow_right_mono hle (n + 1) hmem
  rwa [hk', Ideal.mem_bot] at this

/-- **The kernel of an `n`th order thickening on an arbitrary open.** If the kernel ideal sheaf of
the closed immersion `i : X ⟶ X'` has vanishing `(n + 1)`st power, then so has the kernel of
`i.app V : Γ(X', V) ⟶ Γ(X, i⁻¹ V)` for every open `V` of `X'`.

On an affine open the kernel of `i.app V` is the ideal of the kernel ideal sheaf
(`AlgebraicGeometry.Scheme.Hom.ker_apply`), whose powers are computed componentwise. A general
open is covered by affine ones, restriction carries the kernel over `V` into the kernel over each
of them, and a section of the structure sheaf is determined by its germs. -/
theorem ker_app_pow_eq_bot_of_isNthOrderThickening {X X' : Scheme.{u}} {i : X ⟶ X'} {n : ℕ}
    (hi : IsNthOrderThickening n i) (V : X'.Opens) :
    RingHom.ker (i.app V).hom ^ (n + 1) = ⊥ := by
  have := hi.1
  refine le_antisymm (fun y hy => ?_) bot_le
  rw [Ideal.mem_bot]
  refine TopCat.Presheaf.section_ext X'.sheaf V y 0 fun x hx => ?_
  obtain ⟨W, hW, hxW, hWV⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X'.isBasis_affineOpens) hx
  let ρ : Γ(X', V) ⟶ Γ(X', W) := X'.presheaf.map (homOfLE hWV).op
  have hW' : RingHom.ker (i.app W).hom ^ (n + 1) = ⊥ := by
    have h := congrArg (fun J : X'.IdealSheafData => J.ideal ⟨W, hW⟩) hi.2
    simpa only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.Hom.ker_apply,
      Scheme.IdealSheafData.ideal_bot, Pi.bot_apply] using h
  have hρ : ρ.hom y = 0 :=
    map_eq_zero_of_pow_ker_eq_bot ρ.hom (i.app V).hom (i.app W).hom
      (X.presheaf.map ((TopologicalSpace.Opens.map i.base).map (homOfLE hWV)).op).hom
      (congrArg CommRingCat.Hom.hom (i.naturality (homOfLE hWV).op)) hW' hy
  have hgerm := X'.presheaf.germ_res_apply (homOfLE hWV) x hxW y
  change (X'.presheaf.germ W x hxW) (ρ.hom y) = _ at hgerm
  rw [hρ, map_zero] at hgerm
  change _ = (X'.presheaf.germ V x hx) 0
  rw [map_zero]
  exact hgerm.symm

/-- **Nilpotence of a kernel passes across a cartesian square of rings.** If the square with
sides `p`, `q`, `f`, `g` of commutative rings is cartesian and the kernel of `g` has vanishing
`(n + 1)`st power, then so has the kernel of `p`.

`q` carries the kernel of `p` into the kernel of `g`, so it kills the `(n + 1)`st power of the
kernel of `p`, which `p` kills too; the square being cartesian, the two projections are jointly
injective. -/
theorem ringHomKer_pow_eq_bot_of_isPullback {P A B C : CommRingCat.{u}}
    {p : P ⟶ A} {q : P ⟶ B} {f : A ⟶ C} {g : B ⟶ C} (h : IsPullback p q f g) {n : ℕ}
    (hker : RingHom.ker g.hom ^ (n + 1) = ⊥) : RingHom.ker p.hom ^ (n + 1) = ⊥ := by
  have hT := h.map (forget CommRingCat.{u})
  refine le_antisymm (fun x hx => ?_) bot_le
  have hq : q.hom x = 0 :=
    map_eq_zero_of_pow_ker_eq_bot q.hom p.hom g.hom f.hom
      (congrArg CommRingCat.Hom.hom h.w.symm) hker hx
  have hp : p.hom x = 0 := by
    have := Ideal.pow_le_self (Nat.succ_ne_zero n) hx
    rwa [RingHom.mem_ker] at this
  have hz := Types.ext_of_isPullback hT (x₁ := x) (y₁ := 0)
    (by simpa using hp) (by simpa using hq)
  rw [Ideal.mem_bot]
  simpa using hz

end Stacks.Thickenings

namespace Stacks.Pushout

open Stacks.Thickenings

variable {Z Z' Y Y' : Scheme.{u}}

/-- **The leg of a pushout along an `n`th order thickening is an `n`th order thickening.** Let
`i : Z ⟶ Z'` be an `n`th order thickening and `f : Z ⟶ Y` an affine morphism, and let the square
`i ≫ a = f ≫ b` be a pushout of schemes. Then `b : Y ⟶ Y'` is an `n`th order thickening.

That `b` is a closed immersion is part of [Stacks Project, Tag 07RT]. Over an affine open `U` of
`Y'` the square of rings of sections is cartesian (the description of `𝒪_{Y'}` in Tag 07RT, read
on the pushout of locally ringed spaces, which our square is isomorphic to), and the kernel of
the leg opposite to `b.app U` has vanishing `(n + 1)`st power by
`Stacks.Thickenings.ker_app_pow_eq_bot_of_isNthOrderThickening`; so the kernel of `b.app U` has
too, by `Stacks.Thickenings.ringHomKer_pow_eq_bot_of_isPullback`. -/
theorem isNthOrderThickening_of_isPushout {i : Z ⟶ Z'} {f : Z ⟶ Y} {a : Z' ⟶ Y'} {b : Y ⟶ Y'}
    {n : ℕ} (hi : IsNthOrderThickening n i) [IsAffineHom f] (hpo : IsPushout i f a b) :
    IsNthOrderThickening n b := by
  have hfin : IsFiniteOrderThickening i := ⟨hi.1, n, hi.2⟩
  obtain ⟨Q, A, B', hcol, hch⟩ :=
    exists_isPushout_forgetToLocallyRingedSpace_of_isFiniteOrderThickening i f hfin
  have hpoQ : IsPushout i f A B' := IsPushout.of_map_of_faithful _ hcol
  let e : Q ≅ Y' := hpoQ.isoIsPushout _ _ hpo
  have heA : A ≫ e.hom = a := hpoQ.inl_isoIsPushout_hom _ _ hpo
  have heB : B' ≫ e.hom = b := hpoQ.inr_isoIsPushout_hom _ _ hpo
  have hthB : IsThickening B' :=
    isThickening_of_isPushout_forgetToLocallyRingedSpace hfin.isThickening f hcol hch
  have := hthB.1
  have hci : IsClosedImmersion b := by rw [← heB]; infer_instance
  refine ⟨hci, ?_⟩
  have hcol' : IsPushout (Scheme.forgetToLocallyRingedSpace.map i)
      (Scheme.forgetToLocallyRingedSpace.map f) (Scheme.forgetToLocallyRingedSpace.map a)
      (Scheme.forgetToLocallyRingedSpace.map b) :=
    hcol.of_iso' (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (Scheme.forgetToLocallyRingedSpace.mapIso e).symm
      (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id])
      (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id])
      (by rw [Iso.symm_hom, Functor.mapIso_inv, Iso.refl_hom, Category.id_comp,
        ← Functor.map_comp, ← heA, Category.assoc, Iso.hom_inv_id, Category.comp_id])
      (by rw [Iso.symm_hom, Functor.mapIso_inv, Iso.refl_hom, Category.id_comp,
        ← Functor.map_comp, ← heB, Category.assoc, Iso.hom_inv_id, Category.comp_id])
  refine Scheme.IdealSheafData.ext (funext fun U => ?_)
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.Hom.ker_apply,
    Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
  have hX : i ⁻¹ᵁ (a ⁻¹ᵁ U.1) = f ⁻¹ᵁ (b ⁻¹ᵁ U.1) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hpo.w]
  have hsq := isPullback_app_of_isPushout_forgetToLocallyRingedSpace hcol' U.1 hX
  refine ringHomKer_pow_eq_bot_of_isPullback hsq ?_
  have hV := ker_app_pow_eq_bot_of_isNthOrderThickening hi (a ⁻¹ᵁ U.1)
  have hinj : Function.Injective
      (eqToHom (congrArg (fun V : Z.Opens ↦ Γ(Z, V)) hX)).hom := by
    intro z w hzw
    have := congrArg (eqToHom (congrArg (fun V : Z.Opens ↦ Γ(Z, V)) hX.symm)).hom hzw
    simpa only [← CommRingCat.comp_apply, eqToHom_trans, eqToHom_refl,
      CommRingCat.id_apply] using this
  have hker : RingHom.ker (i.app (a ⁻¹ᵁ U.1) ≫
      eqToHom (congrArg (fun V : Z.Opens ↦ Γ(Z, V)) hX)).hom =
      RingHom.ker (i.app (a ⁻¹ᵁ U.1)).hom := by
    rw [CommRingCat.hom_comp, RingHom.ker_comp_of_injective _ hinj]
  rw [hker]
  exact hV

/-- **The leg of a pushout along a finite order thickening is a finite order thickening.** Let
`i : Z ⟶ Z'` be a finite order thickening and `f : Z ⟶ Y` an affine morphism, and let the square
`i ≫ a = f ≫ b` be a pushout of schemes. Then `b : Y ⟶ Y'` is a finite order thickening; this is
`Stacks.Pushout.isNthOrderThickening_of_isPushout`. -/
theorem isFiniteOrderThickening_of_isPushout {i : Z ⟶ Z'} {f : Z ⟶ Y} {a : Z' ⟶ Y'}
    {b : Y ⟶ Y'} (hi : IsFiniteOrderThickening i) [IsAffineHom f] (hpo : IsPushout i f a b) :
    IsFiniteOrderThickening b :=
  have h := isNthOrderThickening_of_isPushout (n := hi.2.choose) ⟨hi.1, hi.2.choose_spec⟩ hpo
  ⟨h.1, _, h.2⟩

end Stacks.Pushout

end
