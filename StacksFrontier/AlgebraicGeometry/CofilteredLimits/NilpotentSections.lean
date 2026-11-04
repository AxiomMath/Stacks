module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.AffineOpenSections

/-!
# Nilpotent sections of an inverse limit of schemes come from the stages

Let `{ Dᵢ }` be an inverse system of schemes indexed by a cofiltered category, with affine
transition morphisms, and let `c` be a limit cone over it. A nilpotent section of the limit over
the preimage of an affine open of a stage is the pullback of a section at some later stage which
is already nilpotent there. Consequently a morphism `g : T ⟶ lim Dᵢ` whose composites with the
projections kill the nilpotent sections of every stage kills the nilpotent sections of the limit,
and so factors through every surjective closed immersion into the limit — in particular through
the reduction of the limit. This is the computation behind the fact that the limit of the
reductions of the stages of an inverse system with affine transition morphisms is the reduction
of the limit, which the proof that a thickening of an affine algebraic space is affine uses.

## Main results

* `AlgebraicGeometry.exists_isNilpotent_appLE_π_eq_of_isLimit`: a nilpotent section over the
  preimage of an affine open of a stage comes from a nilpotent section at a later stage.
* `AlgebraicGeometry.app_eq_zero_of_isNilpotent_of_isLimit`: a morphism into the limit whose
  composites with the projections kill nilpotent sections of the stages kills the nilpotent
  sections of the limit.
* `AlgebraicGeometry.exists_lift_of_isClosedImmersion_of_surjective_of_isLimit`: such a morphism
  factors through every surjective closed immersion into the limit.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a)] (c : Cone D) (hc : IsLimit c)

include hc in
/-- **A nilpotent section of an inverse limit comes from a nilpotent section of a later stage.**
Let `{ Dᵢ }` be a cofiltered inverse system of schemes with affine transition morphisms, let `c`
be a limit cone, and let `W` be an affine open of the stage `Dᵢ`. Every nilpotent section of the
limit over `c.π.app i ⁻¹ᵁ W` is the pullback of a nilpotent section of `Dⱼ` over `D.map a ⁻¹ᵁ W`
for some `a : j ⟶ i`. -/
theorem exists_isNilpotent_appLE_π_eq_of_isLimit (i : I) {W : (D.obj i).Opens}
    (hW : IsAffineOpen W) (s : Γ(c.pt, c.π.app i ⁻¹ᵁ W)) (hs : IsNilpotent s) :
    ∃ (j : I) (a : j ⟶ i) (t : Γ(D.obj j, D.map a ⁻¹ᵁ W)), IsNilpotent t ∧
      (c.π.app j).appLE (D.map a ⁻¹ᵁ W) (c.π.app i ⁻¹ᵁ W)
        (le_of_eq (by rw [← Scheme.Hom.comp_preimage, c.w])) t = s := by
  obtain ⟨j, a, t, rfl⟩ := exists_appLE_π_eq_of_isAffineOpen_of_isLimit D c hc i hW s
  obtain ⟨n, hn⟩ := hs
  have heq : c.π.app j ⁻¹ᵁ (D.map a ⁻¹ᵁ W) = c.π.app i ⁻¹ᵁ W := by
    rw [← Scheme.Hom.comp_preimage, c.w]
  have hle : c.π.app i ⁻¹ᵁ W ≤ c.π.app j ⁻¹ᵁ (D.map a ⁻¹ᵁ W) := heq.ge
  have h0 : (c.π.app j).app (D.map a ⁻¹ᵁ W) (t ^ n) = 0 := by
    rw [← map_pow] at hn
    have h1 : (c.π.app j).app (D.map a ⁻¹ᵁ W) (t ^ n) = c.pt.presheaf.map (homOfLE heq.le).op
        ((c.π.app j).appLE (D.map a ⁻¹ᵁ W) (c.π.app i ⁻¹ᵁ W) hle (t ^ n)) := by
      dsimp only [Scheme.Hom.appLE, Functor.const_obj_obj]
      rw [← CommRingCat.comp_apply, Category.assoc, ← Functor.map_comp,
        show (homOfLE hle).op ≫ (homOfLE heq.le).op = 𝟙 _ from rfl,
        CategoryTheory.Functor.map_id, Category.comp_id]
    rw [h1, hn, map_zero]
  have hU : IsCompact (X := D.obj j) (D.map a ⁻¹ᵁ W : Set (D.obj j)) :=
    (hW.preimage (D.map a)).isCompact
  obtain ⟨k, b, hk⟩ := exists_app_map_eq_zero_of_isLimit D c hc hU (t ^ n) h0
  refine ⟨k, b ≫ a, (D.obj k).presheaf.map (eqToHom (by
      rw [Functor.map_comp, Scheme.Hom.comp_preimage])).op ((D.map b).app _ t), ?_, ?_⟩
  · refine ⟨n, ?_⟩
    rw [← map_pow, ← map_pow, hk, map_zero]
  · have hcw : c.π.app j = c.π.app k ≫ D.map b := (c.w b).symm
    rw [Scheme.Hom.appLE_congr_hom hcw _ _ _ (by rw [← hcw]; exact hle), Scheme.Hom.comp_appLE,
      CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

include hc in
/-- **A morphism into an inverse limit killing the nilpotent sections of the stages kills the
nilpotent sections of the limit.** Let `{ Dᵢ }` be a cofiltered inverse system of schemes with
affine transition morphisms and `c` a limit cone. If `g : T ⟶ c.pt` is such that every composite
`g ≫ c.π.app j` kills the nilpotent sections of `Dⱼ` over its affine opens, then `g` kills every
nilpotent section of the limit. -/
theorem app_eq_zero_of_isNilpotent_of_isLimit {T : Scheme.{u}} (g : T ⟶ c.pt)
    (hg : ∀ (j : I) (U : (D.obj j).Opens), IsAffineOpen U → ∀ t : Γ(D.obj j, U),
      IsNilpotent t → (g ≫ c.π.app j).app U t = 0)
    (U : c.pt.Opens) (s : Γ(c.pt, U)) (hs : IsNilpotent s) : g.app U s = 0 := by
  refine T.IsSheaf.section_ext fun x hx => ?_
  obtain ⟨_, ⟨i, W, hW, rfl⟩, hxW, hWU⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (isBasis_preimage_isAffineOpen D c hc)
      (show g.base x ∈ U from hx)
  refine ⟨g ⁻¹ᵁ (c.π.app i ⁻¹ᵁ W), Scheme.Hom.preimage_mono _ hWU, hxW, ?_⟩
  obtain ⟨j, a, t, ht, hts⟩ :=
    exists_isNilpotent_appLE_π_eq_of_isLimit D c hc i hW _
      (hs.map (c.pt.presheaf.map (homOfLE hWU).op).hom)
  have hgt := hg j _ (hW.preimage (D.map a)) t ht
  have key : (T.presheaf.map (homOfLE (Scheme.Hom.preimage_mono g hWU)).op) (g.app U s) =
      g.app (c.π.app i ⁻¹ᵁ W) ((c.pt.presheaf.map (homOfLE hWU).op) s) := by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
    rfl
  rw [key, ← hts, map_zero, ← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE,
    Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE, CommRingCat.comp_apply, hgt, map_zero]

include hc in
/-- **A morphism into an inverse limit killing the nilpotent sections of the stages factors
through every surjective closed immersion into the limit.** Let `{ Dᵢ }` be a cofiltered inverse
system of schemes with affine transition morphisms and `c` a limit cone, and let
`i : Z ⟶ c.pt` be a surjective closed immersion. If every composite `g ≫ c.π.app j` kills the
nilpotent sections of `Dⱼ` over its affine opens, then `g` factors through `i`. -/
theorem exists_lift_of_isClosedImmersion_of_surjective_of_isLimit {T Z : Scheme.{u}}
    (g : T ⟶ c.pt) (i : Z ⟶ c.pt) [IsClosedImmersion i] [Surjective i]
    (hg : ∀ (j : I) (U : (D.obj j).Opens), IsAffineOpen U → ∀ t : Γ(D.obj j, U),
      IsNilpotent t → (g ≫ c.π.app j).app U t = 0) :
    ∃ l : T ⟶ Z, l ≫ i = g := by
  have hker : i.ker ≤ c.pt.nilradical := by
    refine (Scheme.IdealSheafData.le_radical i.ker).trans ?_
    rw [← Scheme.IdealSheafData.vanishingIdeal_support,
      ← Scheme.IdealSheafData.vanishingIdeal_top]
    refine Scheme.IdealSheafData.vanishingIdeal_antimono fun x _ => ?_
    show x ∈ (i.ker.support : Set c.pt)
    rw [Scheme.Hom.support_ker, i.surjective.range_eq, closure_univ]
    trivial
  have hnil : c.pt.nilradical ≤ g.ker := by
    refine (Scheme.IdealSheafData.le_ofIdeals_iff).2 fun U s hs => ?_
    obtain ⟨n, hn⟩ := hs
    exact app_eq_zero_of_isNilpotent_of_isLimit D c hc g hg U s ⟨n, by simpa using hn⟩
  exact ⟨IsClosedImmersion.lift i g (hker.trans hnil), IsClosedImmersion.lift_fac _ _ _⟩

end AlgebraicGeometry

end
