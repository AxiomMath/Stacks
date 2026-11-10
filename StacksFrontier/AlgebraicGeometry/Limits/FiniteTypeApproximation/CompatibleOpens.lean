module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Detecting inverse limits of schemes along a compatible family of opens

Let `D : J ⥤ Scheme` be a diagram of schemes and let `V j ≤ D.obj j` be a family of opens
which is *compatible*, in the sense that `D.map f ⁻¹ᵁ V k = V j` for every `f : j ⟶ k`.
Such a family cuts out a subdiagram `compatibleOpensDiagram` of `D`, and any cone over `D`
restricts to a cone `compatibleOpensCone` over that subdiagram.

## Main results

* `AlgebraicGeometry.isLimitOfCompatibleOpensCover`: a cone over a cofiltered diagram of
  schemes is limiting as soon as there is a family of compatible families of opens which is
  closed under intersection, which covers `D.obj j₀` for some index `j₀`, and each of whose
  restricted cones is limiting.

This reduces the verification that a cone of schemes is an inverse limit to a verification on
an open cover.  It is the gluing step in the proof of Noetherian approximation for
quasi-compact quasi-separated schemes.

## References

* [Stacks Project, Tag 01YT](https://stacks.math.columbia.edu/tag/01YT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe v w u

namespace AlgebraicGeometry

variable {J : Type w} [Category.{v} J] (D : J ⥤ Scheme.{u})

/-- The subdiagram of a diagram of schemes `D` cut out by a family of opens `V j ≤ D.obj j`
which is compatible, i.e. satisfies `D.map f ⁻¹ᵁ V k = V j` for all `f : j ⟶ k`. -/
@[reducible] noncomputable def compatibleOpensDiagram (V : ∀ j, (D.obj j).Opens)
    (hV : ∀ ⦃j k : J⦄ (f : j ⟶ k), D.map f ⁻¹ᵁ V k = V j) : J ⥤ Scheme.{u} where
  obj j := V j
  map {_ _} f := (D.map f).resLE _ _ (hV f).ge
  map_id j := by simp [← cancel_mono (Scheme.Opens.ι (V j))]
  map_comp {_ _ l} f g := by
    rw [← cancel_mono (Scheme.Opens.ι (V l)), Category.assoc,
      Scheme.Hom.resLE_comp_resLE_assoc, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι,
      Functor.map_comp]

/-- A cone over a diagram of schemes `D` restricts to a cone over the subdiagram cut out by a
compatible family of opens `V`.  The vertex is any open `U` of the vertex of the cone such that
`c.π.app j ⁻¹ᵁ V j = U` for every `j`. -/
@[reducible] noncomputable def compatibleOpensCone (c : Cone D) (V : ∀ j, (D.obj j).Opens)
    (hV : ∀ ⦃j k : J⦄ (f : j ⟶ k), D.map f ⁻¹ᵁ V k = V j)
    (U : c.pt.Opens) (hU : ∀ j, c.π.app j ⁻¹ᵁ V j = U) :
    Cone (compatibleOpensDiagram D V hV) where
  pt := U
  π.app j := (c.π.app j).resLE _ _ (hU j).ge
  π.naturality {_ k} f := by
    refine (Category.id_comp _).trans ?_
    rw [← cancel_mono (Scheme.Opens.ι (V k)), Category.assoc,
      Scheme.Hom.resLE_comp_resLE_assoc, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι,
      c.w f]

variable {D}

section Cover

variable {c : Cone D} {ι : Type*} {V : ι → ∀ j, (D.obj j).Opens} {U : ι → c.pt.Opens}
  (hV : ∀ (a : ι) ⦃j k : J⦄ (f : j ⟶ k), D.map f ⁻¹ᵁ V a k = V a j)
  (hU : ∀ (a : ι) (j : J), c.π.app j ⁻¹ᵁ V a j = U a)

include hV in
/-- For a compatible family of opens, the preimage of `V a j` under the leg at `j` of any cone
over `D` does not depend on `j`. -/
lemma preimage_compatibleOpens_eq [IsCofiltered J] (s : Cone D) (a : ι) (j j' : J) :
    s.π.app j ⁻¹ᵁ V a j = s.π.app j' ⁻¹ᵁ V a j' := by
  obtain ⟨k, f, g, -⟩ := IsCofilteredOrEmpty.cone_objs j j'
  have e (l : J) (h : k ⟶ l) : s.π.app k ⁻¹ᵁ V a k = s.π.app l ⁻¹ᵁ V a l := by
    rw [← hV a h, ← Scheme.Hom.comp_preimage, s.w h]
  rw [← e j f, e j' g]

/-- Hom extensionality for a limiting restricted cone, phrased through `Scheme.Hom.resLE`. -/
lemma hom_ext_resLE (d : ι)
    (hlim : IsLimit (compatibleOpensCone D c (V d) (hV d) (U d) (hU d)))
    {Z : Scheme.{u}} (p q : Z ⟶ (U d).toScheme)
    (h : ∀ j : J, p ≫ (c.π.app j).resLE (V d j) (U d) (hU d j).ge =
      q ≫ (c.π.app j).resLE (V d j) (U d) (hU d j).ge) :
    p = q :=
  hlim.hom_ext h

/-- The lift supplied by a limiting restricted cone, phrased through `Scheme.Hom.resLE`. -/
lemma exists_hom_comp_resLE_eq (d : ι)
    (hlim : IsLimit (compatibleOpensCone D c (V d) (hV d) (U d) (hU d)))
    (s : Cone D) (W : s.pt.Opens) (hW : ∀ j, s.π.app j ⁻¹ᵁ V d j = W) :
    ∃ g : W.toScheme ⟶ (U d).toScheme, ∀ j : J,
      g ≫ (c.π.app j).resLE (V d j) (U d) (hU d j).ge =
        (s.π.app j).resLE (V d j) W (hW j).ge :=
  ⟨hlim.lift (compatibleOpensCone D s (V d) (hV d) W hW),
    hlim.fac (compatibleOpensCone D s (V d) (hV d) W hW)⟩

/-- Two morphisms from an open `W` of the vertex of a cone `s` into the vertex of `c` agree as
soon as they both induce the legs of `s` and `W` is contained in the locus cut out by a member
of the family whose restricted cone is limiting. -/
lemma hom_ext_of_le_compatibleOpens [IsCofiltered J] {s : Cone D} (d : ι)
    (hlim : IsLimit (compatibleOpensCone D c (V d) (hV d) (U d) (hU d)))
    {W : s.pt.Opens} {j₁ : J} (hW : W ≤ s.π.app j₁ ⁻¹ᵁ V d j₁)
    (α β : W.toScheme ⟶ c.pt)
    (hα : ∀ j, α ≫ c.π.app j = W.ι ≫ s.π.app j)
    (hβ : ∀ j, β ≫ c.π.app j = W.ι ≫ s.π.app j) :
    α = β := by
  obtain ⟨j₀⟩ := IsCofiltered.nonempty (C := J)
  have hWj : W ≤ s.π.app j₀ ⁻¹ᵁ V d j₀ :=
    (preimage_compatibleOpens_eq hV s d j₁ j₀) ▸ hW
  have hrange : ∀ γ : W.toScheme ⟶ c.pt, (∀ j, γ ≫ c.π.app j = W.ι ≫ s.π.app j) →
      Set.range γ.base ⊆ Set.range (U d).ι.base := by
    rintro γ hγ _ ⟨x, rfl⟩
    refine ⟨⟨_, ?_⟩, rfl⟩
    rw [← hU d j₀]
    change (c.π.app j₀).base (γ.base x) ∈ V d j₀
    rw [← Scheme.Hom.comp_apply, hγ j₀, Scheme.Hom.comp_apply]
    exact hWj x.2
  have hfac : ∀ (γ : W.toScheme ⟶ c.pt) (hγ : ∀ j, γ ≫ c.π.app j = W.ι ≫ s.π.app j),
      IsOpenImmersion.lift (U d).ι γ (hrange γ hγ) ≫ (U d).ι = γ := fun _ _ ↦
    IsOpenImmersion.lift_fac _ _ _
  rw [← hfac α hα, ← hfac β hβ]
  congr 1
  refine hom_ext_resLE hV hU d hlim _ _ fun j ↦ ?_
  rw [← cancel_mono (Scheme.Opens.ι (V d j))]
  simp only [Category.assoc, Scheme.Hom.resLE_comp_ι]
  rw [← Category.assoc, ← Category.assoc, hfac α hα, hfac β hβ, hα j, hβ j]

include hU in
/-- **Limits of schemes are detected on a compatible open cover.** Let `c` be a cone over a
diagram of schemes `D` indexed by a cofiltered category.  Suppose given a family of compatible
families of opens `V a` which is closed under intersection, which covers `D.obj j₀` for one
index `j₀`, and such that each restricted cone of `c` is limiting.  Then `c` is limiting. -/
noncomputable def isLimitOfCompatibleOpensCover [IsCofiltered J]
    (hinf : ∀ a b : ι, ∃ d : ι, ∀ j, V d j = V a j ⊓ V b j)
    (j₀ : J) (hcover : IsOpenCover fun a ↦ V a j₀)
    (hlim : ∀ a : ι, IsLimit (compatibleOpensCone D c (V a) (hV a) (U a) (hU a))) :
    IsLimit c := by
  classical
  refine IsLimit.ofExistsUnique fun s ↦ ?_
  have hT : ∀ (a : ι) (j : J), s.π.app j ⁻¹ᵁ V a j = s.π.app j₀ ⁻¹ᵁ V a j₀ := fun a j ↦
    preimage_compatibleOpens_eq hV s a j j₀
  have hTcover : IsOpenCover fun a ↦ s.π.app j₀ ⁻¹ᵁ V a j₀ :=
    IsOpenCover.mk (by
      rw [← Scheme.Hom.preimage_iSup, hcover.iSup_eq_top, Scheme.Hom.preimage_top])
  choose g hg using fun a : ι ↦ exists_hom_comp_resLE_eq hV hU a (hlim a) s _ (hT a)
  -- the morphism `s.π.app j₀ ⁻¹ᵁ V a j₀ ⟶ c.pt` supplied by the `a`-th limit
  obtain ⟨φ, hφ⟩ : ∃ φ : ∀ a : ι, (s.π.app j₀ ⁻¹ᵁ V a j₀ : s.pt.Opens).toScheme ⟶ c.pt,
      ∀ (a : ι) (j : J), φ a ≫ c.π.app j =
        (s.π.app j₀ ⁻¹ᵁ V a j₀ : s.pt.Opens).ι ≫ s.π.app j := by
    refine ⟨fun a ↦ g a ≫ (U a).ι, fun a j ↦ ?_⟩
    rw [Category.assoc, ← Scheme.Hom.resLE_comp_ι (c.π.app j) (hU a j).ge, ← Category.assoc,
      hg a j, Scheme.Hom.resLE_comp_ι]
  -- the `φ a` agree on the overlaps, hence glue
  have hglue : ∀ a b : ι,
      pullback.fst (s.π.app j₀ ⁻¹ᵁ V a j₀ : s.pt.Opens).ι
          (s.π.app j₀ ⁻¹ᵁ V b j₀ : s.pt.Opens).ι ≫ φ a =
        pullback.snd (s.π.app j₀ ⁻¹ᵁ V a j₀ : s.pt.Opens).ι
          (s.π.app j₀ ⁻¹ᵁ V b j₀ : s.pt.Opens).ι ≫ φ b := by
    intro a b
    obtain ⟨d, hd⟩ := hinf a b
    rw [← cancel_epi (isPullback_opens_inf (s.π.app j₀ ⁻¹ᵁ V a j₀)
      (s.π.app j₀ ⁻¹ᵁ V b j₀)).isoPullback.hom, ← Category.assoc, ← Category.assoc,
      IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_snd]
    refine hom_ext_of_le_compatibleOpens hV hU d (hlim d) (j₁ := j₀) ?_ _ _ ?_ ?_
    · rw [hd j₀, Scheme.Hom.preimage_inf]
    · intro j
      rw [Category.assoc, hφ a, ← Category.assoc]
      congr 1
      exact Scheme.homOfLE_ι _ _
    · intro j
      rw [Category.assoc, hφ b, ← Category.assoc]
      congr 1
      exact Scheme.homOfLE_ι _ _
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : s.pt ⟶ c.pt, ∀ a : ι,
      (s.π.app j₀ ⁻¹ᵁ V a j₀ : s.pt.Opens).ι ≫ Θ = φ a :=
    ⟨(s.pt.openCoverOfIsOpenCover _ hTcover).glueMorphisms (fun a ↦ φ a) hglue,
      fun a ↦ (s.pt.openCoverOfIsOpenCover _ hTcover).ι_glueMorphisms (fun a ↦ φ a) hglue a⟩
  have hext : ∀ {Z : Scheme.{u}} (f₁ f₂ : s.pt ⟶ Z),
      (∀ a : ι, (s.π.app j₀ ⁻¹ᵁ V a j₀ : s.pt.Opens).ι ≫ f₁ =
        (s.π.app j₀ ⁻¹ᵁ V a j₀ : s.pt.Opens).ι ≫ f₂) → f₁ = f₂ := fun f₁ f₂ h ↦
    (s.pt.openCoverOfIsOpenCover _ hTcover).hom_ext f₁ f₂ fun a ↦ h a
  refine ⟨Θ, fun j ↦ ?_, fun m hm ↦ ?_⟩
  · refine hext _ _ fun a ↦ ?_
    rw [← Category.assoc, hΘ a, hφ a j]
  · refine hext _ _ fun a ↦ ?_
    rw [hΘ a]
    refine hom_ext_of_le_compatibleOpens hV hU a (hlim a) (j₁ := j₀) le_rfl _ _ ?_ (hφ a)
    intro j
    rw [Category.assoc, hm j]

end Cover

end AlgebraicGeometry
