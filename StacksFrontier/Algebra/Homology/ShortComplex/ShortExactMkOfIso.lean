module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Short exactness of composable pairs identified up to isomorphism

Two composable pairs `A ⟶ B ⟶ D` and `A' ⟶ B' ⟶ D` with the same last object, related by
isomorphisms `A ≅ A'` and `B ≅ B'` commuting with the arrows, compose to zero together and, when
they do, form short exact short complexes together.  This is the form in which a sequence is
replaced by an isomorphic one whose arrows are written differently, without first assembling the
two short complexes.

## Main results

* `CategoryTheory.ShortComplex.exists_shortExact_mk_iff_of_isIso` and
  `CategoryTheory.ShortComplex.exists_shortExact_mk_iff_of_isIso₃`: the statement.
* `CategoryTheory.ShortComplex.exists_shortExact_mk_of_map` and
  `CategoryTheory.ShortComplex.exists_shortExact_mk_map`: a faithful exact functor reflects, and
  an exact functor preserves, short exactness of a composable pair.
-/

@[expose] public section

namespace CategoryTheory.ShortComplex

open Limits

section Preadditive

variable {C : Type*} [Category C] [Preadditive C]

/-- Short exactness of two composable pairs related by isomorphisms at all three terms. -/
private theorem exists_shortExact_mk_iff_of_isIso₃_aux {A B D A' B' D' : C} (a : A ⟶ B)
    (b : B ⟶ D) (a' : A' ⟶ B') (b' : B' ⟶ D') (eA : A ⟶ A') (eB : B ⟶ B') (eD : D ⟶ D')
    [IsIso eA] [IsIso eB] [IsIso eD] (ha : a ≫ eB = eA ≫ a') (hb : b ≫ eD = eB ≫ b') :
    (∃ h : a ≫ b = 0, (ShortComplex.mk a b h).ShortExact) ↔
      ∃ h : a' ≫ b' = 0, (ShortComplex.mk a' b' h).ShortExact := by
  have hab : a ≫ b ≫ eD = eA ≫ a' ≫ b' := by
    rw [hb, ← Category.assoc, ha, Category.assoc]
  have hz : a ≫ b = 0 ↔ a' ≫ b' = 0 :=
    ⟨fun h => by rw [← cancel_epi eA, ← hab, ← Category.assoc, h, zero_comp, comp_zero],
      fun h => by rw [← cancel_mono eD, Category.assoc, hab, h, comp_zero, zero_comp]⟩
  have e : ∀ h h', ShortComplex.mk a b h ≅ ShortComplex.mk a' b' h' := fun h h' =>
    ShortComplex.isoMk (asIso eA) (asIso eB) (asIso eD) ha.symm hb.symm
  exact ⟨fun ⟨h, hs⟩ => ⟨hz.1 h, (shortExact_iff_of_iso (e h _)).1 hs⟩,
    fun ⟨h', hs⟩ => ⟨hz.2 h', (shortExact_iff_of_iso (e _ h')).2 hs⟩⟩

/-- **Two composable pairs of morphisms identified at their first two terms are short exact
together.**  If `a ≫ eB = eA ≫ a'` and `b = eB ≫ b'` for isomorphisms `eA` and `eB`, then
`a ≫ b` vanishes exactly when `a' ≫ b'` does, and the short complexes they form are then short
exact together. -/
theorem exists_shortExact_mk_iff_of_isIso {A B D A' B' : C} (a : A ⟶ B) (b : B ⟶ D)
    (a' : A' ⟶ B') (b' : B' ⟶ D) (eA : A ⟶ A') (eB : B ⟶ B') [IsIso eA] [IsIso eB]
    (ha : a ≫ eB = eA ≫ a') (hb : b = eB ≫ b') :
    (∃ h : a ≫ b = 0, (ShortComplex.mk a b h).ShortExact) ↔
      ∃ h : a' ≫ b' = 0, (ShortComplex.mk a' b' h).ShortExact :=
  exists_shortExact_mk_iff_of_isIso₃_aux a b a' b' eA eB (𝟙 D) ha (by rw [Category.comp_id, hb])

/-- **Two composable pairs of morphisms identified up to isomorphism are short exact together.**
If `a ≫ eB = eA ≫ a'` and `b ≫ eD = eB ≫ b'` for isomorphisms `eA`, `eB` and `eD`, then `a ≫ b`
vanishes exactly when `a' ≫ b'` does, and the short complexes they form are then short exact
together. -/
theorem exists_shortExact_mk_iff_of_isIso₃ {A B D A' B' D' : C} (a : A ⟶ B) (b : B ⟶ D)
    (a' : A' ⟶ B') (b' : B' ⟶ D') (eA : A ⟶ A') (eB : B ⟶ B') (eD : D ⟶ D') [IsIso eA]
    [IsIso eB] [IsIso eD] (ha : a ≫ eB = eA ≫ a') (hb : b ≫ eD = eB ≫ b') :
    (∃ h : a ≫ b = 0, (ShortComplex.mk a b h).ShortExact) ↔
      ∃ h : a' ≫ b' = 0, (ShortComplex.mk a' b' h).ShortExact :=
  exists_shortExact_mk_iff_of_isIso₃_aux a b a' b' eA eB eD ha hb

end Preadditive

section Localization

variable {C₀ C₁ C₂ C₀' C₁' C₂' Cw E : Type*} [Category C₀] [Category C₁] [Category C₂]
  [Category C₀'] [Category C₁'] [Category C₂'] [Category Cw] [Category E] [Preadditive E]
  {G₀ : C₁ ⥤ C₀} {G₁ : C₂ ⥤ C₁} {G₀' : C₁' ⥤ C₀'} {G₁' : C₂' ⥤ C₁'} {K₀ : C₀ ⥤ C₀'}
  {K₁ : C₁ ⥤ C₁'} {K₂ : C₂ ⥤ C₂'} {I : C₀ ⥤ Cw} {D : Cw ⥤ E} {I' : C₀' ⥤ E}
  {IY : C₂} {IZ : C₁} {IW : C₀} {IY' : C₂'} {IZ' : C₁'} {IW' : C₀'}

/-- **A two-arrow sequence localizes along compatible identifications.**  Let `G₁ IY ⟶ IZ` and
`G₀ IZ ⟶ IW` be composable through `G₀`, and `G₁' IY' ⟶ IZ'`, `G₀' IZ' ⟶ IW'` a second such pair,
related to the first by natural comparisons `K₀ G₀ ⟶ G₀' K₁` and `K₁ G₁ ⟶ G₁' K₂`, isomorphisms
`K IY ≅ IY'` etc. compatible with the arrows, and a natural comparison `D I ⟶ I' K₀`, all
invertible.  Then `D I G₀ (G₁ IY ⟶ IZ)`, `D I (G₀ IZ ⟶ IW)` is short exact exactly when
`I' G₀' (G₁' IY' ⟶ IZ')`, `I' (G₀' IZ' ⟶ IW')` is.  This is the shape in which a sequence of
inverse images of modules is compared with its localization. -/
theorem exists_shortExact_mk_iff_of_localization
    (φ₁ : G₁.obj IY ⟶ IZ) (φ₀ : G₀.obj IZ ⟶ IW) (φ₁' : G₁'.obj IY' ⟶ IZ')
    (φ₀' : G₀'.obj IZ' ⟶ IW') (ψ₂ : K₂.obj IY ⟶ IY') (ψ₁ : K₁.obj IZ ⟶ IZ')
    (ψ₀ : K₀.obj IW ⟶ IW') [IsIso ψ₂] [IsIso ψ₁] [IsIso ψ₀]
    (q₀ : ∀ M, K₀.obj (G₀.obj M) ⟶ G₀'.obj (K₁.obj M)) (hq₀ : ∀ M, IsIso (q₀ M))
    (nq₀ : ∀ {M N : C₁} (f : M ⟶ N), K₀.map (G₀.map f) ≫ q₀ N = q₀ M ≫ G₀'.map (K₁.map f))
    (q₁ : ∀ M, K₁.obj (G₁.obj M) ⟶ G₁'.obj (K₂.obj M)) (hq₁ : ∀ M, IsIso (q₁ M))
    (p : ∀ M, D.obj (I.obj M) ⟶ I'.obj (K₀.obj M)) (hp : ∀ M, IsIso (p M))
    (np : ∀ {M N : C₀} (f : M ⟶ N), D.map (I.map f) ≫ p N = p M ≫ I'.map (K₀.map f))
    (H₁ : K₁.map φ₁ ≫ ψ₁ = q₁ IY ≫ G₁'.map ψ₂ ≫ φ₁')
    (H₀ : K₀.map φ₀ ≫ ψ₀ = q₀ IZ ≫ G₀'.map ψ₁ ≫ φ₀') :
    (∃ h : D.map (I.map (G₀.map φ₁)) ≫ D.map (I.map φ₀) = 0,
        (ShortComplex.mk _ _ h).ShortExact) ↔
      ∃ h : I'.map (G₀'.map φ₁') ≫ I'.map φ₀' = 0, (ShortComplex.mk _ _ h).ShortExact := by
  have := hq₀
  have := hq₁
  have := hp
  refine exists_shortExact_mk_iff_of_isIso₃ _ _ _ _
    (p _ ≫ I'.map (q₀ _ ≫ G₀'.map (q₁ _ ≫ G₁'.map ψ₂)))
    (p _ ≫ I'.map (q₀ _ ≫ G₀'.map ψ₁)) (p _ ≫ I'.map ψ₀) ?_ ?_
  · rw [reassoc_of% (np (G₀.map φ₁)), ← I'.map_comp, Category.assoc, ← I'.map_comp,
      reassoc_of% (nq₀ φ₁), ← G₀'.map_comp, H₁]
    simp only [Functor.map_comp, Category.assoc]
  · rw [reassoc_of% (np φ₀), ← I'.map_comp, H₀]
    simp only [Functor.map_comp, Category.assoc]

end Localization

section Transfer

variable {C₀ C₁ C₂ Cr Z₀ Z₁ Z₂ Zr : Type*} [Category C₀] [Category C₁] [Category C₂]
  [Category Cr] [Category Z₀] [Category Z₁] [Category Z₂] [Category Zr] [Preadditive Cr]
  {G₀ : C₁ ⥤ C₀} {G₁ : C₂ ⥤ C₁} {J : C₀ ⥤ Cr} {g₀ : Z₁ ⥤ Z₀} {g₁ : Z₂ ⥤ Z₁} {j : Z₀ ⥤ Zr}
  {Φ₀ : Z₀ ⥤ C₀} {Φ₁ : Z₁ ⥤ C₁} {Φ₂ : Z₂ ⥤ C₂} {Φr : Zr ⥤ Cr}
  {MY : C₂} {MZ : C₁} {MW : C₀} {NY : Z₂} {NZ : Z₁} {NW : Z₀}

/-- **A two-arrow sequence is carried to an isomorphic one by compatible comparison functors.**
Let `Φ` be functors from a second family of categories, commuting with the inverse image functors
up to natural isomorphisms `γ`, and let `M ≅ Φ N` be identifications under which the arrows
`G₁ M_Y ⟶ M_Z`, `G₀ M_Z ⟶ M_W` correspond to `Φ` of arrows `g₁ N_Y ⟶ N_Z`, `g₀ N_Z ⟶ N_W`.  Then
`J G₀ (G₁ M_Y ⟶ M_Z)`, `J (G₀ M_Z ⟶ M_W)` is short exact exactly when
`Φr (j g₀ (g₁ N_Y ⟶ N_Z))`, `Φr (j (g₀ N_Z ⟶ N_W))` is. -/
theorem exists_shortExact_mk_iff_of_comparison
    (φ₁ : G₁.obj MY ⟶ MZ) (φ₀ : G₀.obj MZ ⟶ MW) (φ₁' : g₁.obj NY ⟶ NZ) (φ₀' : g₀.obj NZ ⟶ NW)
    (aY : MY ≅ Φ₂.obj NY) (aZ : MZ ≅ Φ₁.obj NZ) (aW : MW ≅ Φ₀.obj NW)
    (γ₁ : Φ₂ ⋙ G₁ ≅ g₁ ⋙ Φ₁) (γ₀ : Φ₁ ⋙ G₀ ≅ g₀ ⋙ Φ₀) (γJ : Φ₀ ⋙ J ≅ j ⋙ Φr)
    (H₁ : γ₁.inv.app NY ≫ G₁.map aY.inv ≫ φ₁ = Φ₁.map φ₁' ≫ aZ.inv)
    (H₀ : γ₀.inv.app NZ ≫ G₀.map aZ.inv ≫ φ₀ = Φ₀.map φ₀' ≫ aW.inv) :
    (∃ h : J.map (G₀.map φ₁) ≫ J.map φ₀ = 0, (ShortComplex.mk _ _ h).ShortExact) ↔
      ∃ h : Φr.map (j.map (g₀.map φ₁')) ≫ Φr.map (j.map φ₀') = 0,
        (ShortComplex.mk _ _ h).ShortExact := by
  have H₁' : φ₁ ≫ aZ.hom = G₁.map aY.hom ≫ γ₁.hom.app NY ≫ Φ₁.map φ₁' := by
    rw [← cancel_epi (G₁.map aY.inv), ← cancel_epi (γ₁.inv.app NY)]
    simp only [← Category.assoc, H₁]
    simp [← Functor.map_comp]
  have H₀' : φ₀ ≫ aW.hom = G₀.map aZ.hom ≫ γ₀.hom.app NZ ≫ Φ₀.map φ₀' := by
    rw [← cancel_epi (G₀.map aZ.inv), ← cancel_epi (γ₀.inv.app NZ)]
    simp only [← Category.assoc, H₀]
    simp [← Functor.map_comp]
  refine exists_shortExact_mk_iff_of_isIso₃ _ _ _ _
    (J.map (G₀.map (G₁.map aY.hom ≫ γ₁.hom.app NY) ≫ γ₀.hom.app _) ≫ γJ.hom.app _)
    (J.map (G₀.map aZ.hom ≫ γ₀.hom.app NZ) ≫ γJ.hom.app _)
    (J.map aW.hom ≫ γJ.hom.app NW) ?_ ?_
  · have n₀ := γ₀.hom.naturality φ₁'
    have nJ := γJ.hom.naturality (g₀.map φ₁')
    simp only [Functor.comp_map] at n₀ nJ
    rw [← Category.assoc, ← J.map_comp, ← Category.assoc, ← G₀.map_comp, H₁', G₀.map_comp,
      G₀.map_comp, Category.assoc, Category.assoc, n₀]
    simp only [Functor.map_comp, Category.assoc, nJ]
  · have nJ := γJ.hom.naturality φ₀'
    simp only [Functor.comp_map] at nJ
    rw [← Category.assoc, ← J.map_comp, H₀']
    simp only [Functor.map_comp, Category.assoc, nJ]

/-- **Short exactness of a composable pair is carried across a natural isomorphism of functors.**
-/
theorem exists_shortExact_mk_map_iff_of_iso {C D : Type*} [Category C] [Category D]
    [Preadditive D] {F G : C ⥤ D} (α : F ≅ G) {A B E : C} (a : A ⟶ B) (b : B ⟶ E) :
    (∃ h : F.map a ≫ F.map b = 0, (ShortComplex.mk _ _ h).ShortExact) ↔
      ∃ h : G.map a ≫ G.map b = 0, (ShortComplex.mk _ _ h).ShortExact :=
  exists_shortExact_mk_iff_of_isIso₃ _ _ _ _ (α.hom.app A) (α.hom.app B) (α.hom.app E)
    (α.hom.naturality a) (α.hom.naturality b)

/-- **Short exactness of a composable pair is carried across a natural comparison of functors**,
given componentwise. -/
theorem exists_shortExact_mk_map_comp_iff {C D E : Type*} [Category C] [Category D]
    [Category E] [Preadditive E] {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
    (p : ∀ M, G.obj (F.obj M) ⟶ H.obj M) (hp : ∀ M, IsIso (p M))
    (np : ∀ {M N : C} (f : M ⟶ N), G.map (F.map f) ≫ p N = p M ≫ H.map f)
    {A B' E' : C} (a : A ⟶ B') (b : B' ⟶ E') :
    (∃ h : G.map (F.map a) ≫ G.map (F.map b) = 0, (ShortComplex.mk _ _ h).ShortExact) ↔
      ∃ h : H.map a ≫ H.map b = 0, (ShortComplex.mk _ _ h).ShortExact :=
  have := hp
  exists_shortExact_mk_iff_of_isIso₃ _ _ _ _ (p A) (p B') (p E') (np a) (np b)

/-- **A two-arrow sequence is unchanged by replacing the last stage along compatible
identifications.**  Let `φ₁ : M ⟶ M_Z` be a morphism and `φ₀ : G₀ M_Z ⟶ M_W`,
`φ₀' : G₀' M_Z ⟶ M_W'` two arrows, related by a natural comparison `K₀ G₀ ⟶ G₀'`, an isomorphism
`K₀ M_W ≅ M_W'` and a natural comparison `D I ⟶ I' K₀`, all invertible and compatible with `φ₀`
and `φ₀'`.  Then `D I G₀ φ₁`, `D I φ₀` is short exact exactly when `I' G₀' φ₁`, `I' φ₀'` is. -/
theorem exists_shortExact_mk_iff_of_replacement {C₁ C₀ C₀' Cw E : Type*} [Category C₁]
    [Category C₀] [Category C₀'] [Category Cw] [Category E] [Preadditive E]
    {G₀ : C₁ ⥤ C₀} {G₀' : C₁ ⥤ C₀'} {K₀ : C₀ ⥤ C₀'} {I : C₀ ⥤ Cw} {D : Cw ⥤ E} {I' : C₀' ⥤ E}
    {M MZ : C₁} {MW : C₀} {MW' : C₀'} (φ₁ : M ⟶ MZ) (φ₀ : G₀.obj MZ ⟶ MW)
    (φ₀' : G₀'.obj MZ ⟶ MW') (ψ₀ : K₀.obj MW ⟶ MW') [IsIso ψ₀]
    (q₀ : ∀ N, K₀.obj (G₀.obj N) ⟶ G₀'.obj N) (hq₀ : ∀ N, IsIso (q₀ N))
    (nq₀ : ∀ {N N' : C₁} (f : N ⟶ N'), K₀.map (G₀.map f) ≫ q₀ N' = q₀ N ≫ G₀'.map f)
    (p : ∀ N, D.obj (I.obj N) ⟶ I'.obj (K₀.obj N)) (hp : ∀ N, IsIso (p N))
    (np : ∀ {N N' : C₀} (f : N ⟶ N'), D.map (I.map f) ≫ p N' = p N ≫ I'.map (K₀.map f))
    (H₀ : K₀.map φ₀ ≫ ψ₀ = q₀ MZ ≫ φ₀') :
    (∃ h : D.map (I.map (G₀.map φ₁)) ≫ D.map (I.map φ₀) = 0,
        (ShortComplex.mk _ _ h).ShortExact) ↔
      ∃ h : I'.map (G₀'.map φ₁) ≫ I'.map φ₀' = 0, (ShortComplex.mk _ _ h).ShortExact := by
  have := hq₀
  have := hp
  refine exists_shortExact_mk_iff_of_isIso₃ _ _ _ _ (p _ ≫ I'.map (q₀ M)) (p _ ≫ I'.map (q₀ MZ))
    (p _ ≫ I'.map ψ₀) ?_ ?_
  · rw [reassoc_of% (np (G₀.map φ₁)), ← I'.map_comp, nq₀ φ₁, I'.map_comp, Category.assoc]
  · rw [reassoc_of% (np φ₀), ← I'.map_comp, H₀, I'.map_comp, Category.assoc]

end Transfer

section Abelian

variable {C : Type*} [Category C] [Abelian C] {D : Type*} [Category D] [Abelian D]

/-- **A faithful exact functor reflects short exactness of a composable pair.** -/
theorem exists_shortExact_mk_of_map (F : C ⥤ D) [F.Faithful] [F.PreservesZeroMorphisms]
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F] {A B E : C}
    (a : A ⟶ B) (b : B ⟶ E)
    (h : ∃ h : F.map a ≫ F.map b = 0, (ShortComplex.mk (F.map a) (F.map b) h).ShortExact) :
    ∃ h : a ≫ b = 0, (ShortComplex.mk a b h).ShortExact := by
  obtain ⟨hz, hs⟩ := h
  have hab : a ≫ b = 0 := F.map_injective (by rw [F.map_comp, hz, F.map_zero])
  exact ⟨hab, ShortComplex.ShortExact.mk'
    ((ShortComplex.mk a b hab).exact_map_iff_of_faithful F |>.mp hs.exact)
    (F.mono_of_mono_map hs.mono_f) (F.epi_of_epi_map hs.epi_g)⟩

/-- **An exact functor preserves short exactness of a composable pair.** -/
theorem exists_shortExact_mk_map (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [Limits.PreservesFiniteLimits F]
    [Limits.PreservesFiniteColimits F] {A B E : C} (a : A ⟶ B) (b : B ⟶ E)
    (h : ∃ h : a ≫ b = 0, (ShortComplex.mk a b h).ShortExact) :
    ∃ h : F.map a ≫ F.map b = 0, (ShortComplex.mk (F.map a) (F.map b) h).ShortExact := by
  obtain ⟨hz, hs⟩ := h
  exact ⟨by rw [← F.map_comp, hz, F.map_zero], hs.map_of_exact F⟩

end Abelian

end CategoryTheory.ShortComplex

end
