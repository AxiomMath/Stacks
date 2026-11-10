module

public import StacksFrontier.AlgebraicGeometry.Descent.CubeTrivialGlobal
public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.Restrict
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Descent
public import StacksFrontier.AlgebraicGeometry.NormInvertible.LocalIso
public import StacksFrontier.AlgebraicGeometry.QuasiAffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicOrder.Stalk
public import StacksFrontier.AlgebraicGeometry.Modules.InvertibleStalkFree
public import StacksFrontier.AlgebraicGeometry.Divisors.NonvanishingLocusRestrict
public import StacksFrontier.AlgebraicGeometry.SectionPowerOverOpen.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.UnitSpreading
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleSectionsBaseChange

/-!
# Gluing the local trivializations in the theorem of the cube

The last step of the proof of [Stacks, Tag 0BF4]: a module trivial over the preimages of an open
cover of the base, and trivial along a section of the projection, is trivial, the projection
having only constant functions on the preimage of every affine open.

## Main results

* `Stacks.Cube.exists_trivializing_of_iso`: a trivialization over an open subscheme is a section
  by which multiplication is bijective on every smaller open.
* `Stacks.Cube.surjective_app_of_geometricallyIntegral`: a proper, flat, finitely presented
  morphism with geometrically integral fibres has only the constant functions on the preimage of
  an affine open.
* `Stacks.Cube.nonempty_iso_unit_of_cover`: the gluing step, for a morphism `p` with a section `δ`.
* `Stacks.Cube.nonempty_iso_unit`: the theorem of the cube over an arbitrary connected base.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.Cube

/-- **A trivialization over an open subscheme is a trivializing section.** If the restriction of
`L` to the open subscheme `V` is trivial, there is a section `a` of `L` over `V` by which
multiplication is bijective on the sections over every open contained in `V`. -/
theorem exists_trivializing_of_iso {P : Scheme.{u}} (V : P.Opens) (L : P.Modules)
    (e : (Scheme.Modules.pullback V.ι).obj L ≅ Scheme.unitModule V) :
    ∃ a : Γ(L, V.ι ''ᵁ ⊤), ∀ (V' : P.Opens) (h : V' ≤ V.ι ''ᵁ ⊤),
      Function.Bijective fun c : Γ(P, V') => c • L.presheaf.map (homOfLE h).op a := by
  let r := Scheme.Modules.restrictFunctorIsoPullback V.ι
  let e' : L.restrict V.ι ≅ (Scheme.unitModule P).restrict V.ι :=
    r.app L ≪≫ e ≪≫ (Scheme.Modules.pullbackUnitIso V.ι).symm ≪≫ (r.app _).symm
  refine ⟨Stacks.AlgebraicGeometry.ModuleHomGlue.appImage V.ι e'.inv ⊤
    (show Γ(Scheme.unitModule P, V.ι ''ᵁ ⊤) from (1 : Γ(P, V.ι ''ᵁ ⊤))), fun V' h => ?_⟩
  obtain ⟨W', rfl⟩ : ∃ W', V.ι ''ᵁ W' = V' :=
    ⟨_, Stacks.AlgebraicGeometry.ModuleHomGlue.image_preimage_eq_self V.ι h⟩
  have hmap := Stacks.AlgebraicGeometry.ModuleHomGlue.appImage_map V.ι e'.inv
    (le_top : W' ≤ ⊤) (show Γ(Scheme.unitModule P, V.ι ''ᵁ ⊤) from (1 : Γ(P, V.ι ''ᵁ ⊤)))
  have h1 : (Scheme.unitModule P).presheaf.map
      (homOfLE (Scheme.Hom.image_mono V.ι (le_top : W' ≤ ⊤))).op
      (show Γ(Scheme.unitModule P, V.ι ''ᵁ ⊤) from (1 : Γ(P, V.ι ''ᵁ ⊤))) =
        (show Γ(Scheme.unitModule P, V.ι ''ᵁ W') from (1 : Γ(P, V.ι ''ᵁ W'))) :=
    map_one (P.presheaf.map (homOfLE (Scheme.Hom.image_mono V.ι (le_top : W' ≤ ⊤))).op).hom
  rw [h1] at hmap
  have hfun : (fun c : Γ(P, V.ι ''ᵁ W') => c • L.presheaf.map (homOfLE h).op
      (Stacks.AlgebraicGeometry.ModuleHomGlue.appImage V.ι e'.inv ⊤
        (show Γ(Scheme.unitModule P, V.ι ''ᵁ ⊤) from (1 : Γ(P, V.ι ''ᵁ ⊤))))) =
      fun c => Stacks.AlgebraicGeometry.ModuleHomGlue.appImage V.ι e'.inv W'
        (show Γ(Scheme.unitModule P, V.ι ''ᵁ W') from c) := by
    funext c
    rw [show homOfLE h = homOfLE (Scheme.Hom.image_mono V.ι (le_top : W' ≤ ⊤)) from rfl,
      ← hmap, ← Stacks.AlgebraicGeometry.ModuleHomGlue.appImage_smul]
    congr 1
    exact mul_one c
  rw [hfun]
  exact ((SheafOfModules.forget V.toScheme.ringCatSheaf ⋙
    PresheafOfModules.evaluation _ (op W')).mapIso e'.symm).toLinearEquiv.bijective


/-- Restriction of sections of a module in two steps. -/
theorem presheaf_map_map {P : Scheme.{u}} (L : P.Modules) {U V W : P.Opens} (h₁ : U ≤ V)
    (h₂ : V ≤ W) (a : Γ(L, W)) :
    L.presheaf.map (homOfLE h₁).op (L.presheaf.map (homOfLE h₂).op a) =
      L.presheaf.map (homOfLE (h₁.trans h₂)).op a := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- `Stacks.Cube.exists_trivializing_of_iso` with the section over the open `V` itself. -/
theorem exists_trivializing_of_iso' {P : Scheme.{u}} (V : P.Opens) (L : P.Modules)
    (e : (Scheme.Modules.pullback V.ι).obj L ≅ Scheme.unitModule V) :
    ∃ a : Γ(L, V), ∀ (V' : P.Opens) (h : V' ≤ V),
      Function.Bijective fun c : Γ(P, V') => c • L.presheaf.map (homOfLE h).op a := by
  obtain ⟨a, ha⟩ := exists_trivializing_of_iso V L e
  have hV : V ≤ V.ι ''ᵁ ⊤ := V.ι_image_top.ge
  refine ⟨L.presheaf.map (homOfLE hV).op a, fun V' h => ?_⟩
  rw [presheaf_map_map]
  exact ha V' (h.trans hV)

/-- Restriction of ring sections in two steps. -/
private theorem ring_presheaf_map_map {X : TopCat} (F : (Opens X)ᵒᵖ ⥤ CommRingCat) {U V W : Opens X}
    (h₁ : U ≤ V) (h₂ : V ≤ W) (a : F.obj (op W)) :
    F.map (homOfLE h₁).op (F.map (homOfLE h₂).op a) = F.map (homOfLE (h₁.trans h₂)).op a := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- Restriction of ring sections along `U ≤ U` is the identity. -/
private theorem ring_presheaf_map_self {X : TopCat} (F : (Opens X)ᵒᵖ ⥤ CommRingCat) {U : Opens X}
    (h : U ≤ U) (a : F.obj (op U)) : F.map (homOfLE h).op a = a := by
  rw [show (homOfLE _).op = 𝟙 _ from Subsingleton.elim _ _, CategoryTheory.Functor.map_id]
  rfl

/-- **Functions on the preimage of an affine open are constant along the fibres.** For a proper,
flat, finitely presented morphism `p : P ⟶ Z` with geometrically integral fibres and an affine
open `W` of `Z`, every function on `p⁻¹ W` is pulled back from `W`. This is
`ProperFlatGlobalSections.bijective_globalRingHom_of_geometricallyIntegral` (in the namespace
`Stacks.AlgebraicGeometry`) applied to the restriction of `p` over `W ≅ Spec Γ(Z, W)`. -/
theorem surjective_app_of_geometricallyIntegral {P Z : Scheme.{u}} (p : P ⟶ Z) [IsProper p]
    [Flat p] [LocallyOfFinitePresentation p] [GeometricallyIntegral p] {W : Z.Opens}
    (hW : IsAffineOpen W) : Function.Surjective (p.app W) := by
  have hpb := (isPullback_morphismRestrict p W).flip
  have : IsProper (p ∣_ W) := MorphismProperty.of_isPullback hpb inferInstance
  have : Flat (p ∣_ W) := MorphismProperty.of_isPullback hpb inferInstance
  have : LocallyOfFinitePresentation (p ∣_ W) := MorphismProperty.of_isPullback hpb inferInstance
  have : GeometricallyIntegral (p ∣_ W) := MorphismProperty.of_isPullback hpb inferInstance
  let p' : (p ⁻¹ᵁ W).toScheme ⟶ Spec (.of Γ(Z, W)) := (p ∣_ W) ≫ hW.isoSpec.hom
  have : GeometricallyIntegral p' :=
    MorphismProperty.of_isPullback (IsPullback.of_horiz_isIso (fst := 𝟙 _) (snd := p')
      (f := p ∣_ W) (g := hW.isoSpec.inv) ⟨by simp [p']⟩) inferInstance
  have hb :=
    (AlgebraicGeometry.ProperFlatGlobalSections.bijective_globalRingHom_of_geometricallyIntegral
      p').2
  have h1 : Function.Surjective (p ∣_ W).appTop := by
    have : Stacks.Cech.globalRingHom p' = (toSpecΓ (CommRingCat.of Γ(Z, W)) ≫
        hW.isoSpec.hom.appTop) ≫ (p ∣_ W).appTop := by
      simp only [Stacks.Cech.globalRingHom, p', Scheme.Hom.comp_appTop]
      rfl
    rw [this] at hb
    exact Function.Surjective.of_comp hb
  replace h1 : Function.Surjective ((p ∣_ W).app ⊤) := h1
  rw [morphismRestrict_app', Scheme.Hom.appLE] at h1
  intro c
  have hle : (p ⁻¹ᵁ W).ι ''ᵁ ⊤ ≤ p ⁻¹ᵁ W := (p ⁻¹ᵁ W).ι_image_top.le
  obtain ⟨d, hd⟩ := h1 (P.presheaf.map (homOfLE hle).op c)
  let d' : Γ(Z, W.ι ''ᵁ ⊤) := d
  have hA : (p ⁻¹ᵁ W).ι ''ᵁ ⊤ ≤ p ⁻¹ᵁ (W.ι ''ᵁ ⊤) := by
    rw [(p ⁻¹ᵁ W).ι_image_top, W.ι_image_top]
  have hd2 : P.presheaf.map (homOfLE hA).op (p.app (W.ι ''ᵁ ⊤) d') =
      P.presheaf.map (homOfLE hle).op c :=
    hd
  refine ⟨Z.presheaf.map (homOfLE W.ι_image_top.ge).op d', ?_⟩
  have hnat : p.app W (Z.presheaf.map (homOfLE W.ι_image_top.ge).op d') =
      P.presheaf.map (homOfLE (Scheme.Hom.preimage_mono p W.ι_image_top.ge)).op
        (p.app (W.ι ''ᵁ ⊤) d') :=
    congr($(p.naturality (homOfLE W.ι_image_top.ge).op) d')
  rw [hnat]
  have g2 : p ⁻¹ᵁ W ≤ (p ⁻¹ᵁ W).ι ''ᵁ ⊤ := (p ⁻¹ᵁ W).ι_image_top.ge
  have := congrArg (P.presheaf.map (homOfLE g2).op) hd2
  rw [ring_presheaf_map_map, ring_presheaf_map_map, ring_presheaf_map_self] at this
  exact this

/-- **A section of the structure sheaf vanishing nowhere is a unit.** If the germ of `v`, read as
a section of `𝒪_Z`, avoids `𝔪_z · 𝒪_{Z,z}` at every point `z` of `U`, then `v` is invertible. -/
theorem isUnit_of_forall_notMem_maximalSmul {Z : Scheme.{u}} (U : Z.Opens) (v : Γ(Z, U))
    (h : ∀ (z : Z) (hz : z ∈ U), ((Scheme.unitModule Z).presheaf.germ U z hz).hom
      (show Γ(Scheme.unitModule Z, U) from v) ∉
        Stacks.ModuleStalk.maximalSmul (Scheme.unitModule Z) z) :
    IsUnit v := by
  have hb : Z.basicOpen v = U := by
    refine le_antisymm (Z.basicOpen_le v) fun z hz => ?_
    rw [Scheme.mem_basicOpen Z v z hz]
    by_contra hu
    apply h z hz
    have hm : (Z.presheaf.germ U z hz).hom v ∈ IsLocalRing.maximalIdeal (Z.presheaf.stalk z) := hu
    have := Stacks.ModuleStalk.smul_mem_maximalSmul_of_mem_maximalIdeal
      (M := Scheme.unitModule Z) hm (((Scheme.unitModule Z).presheaf.germ U z hz).hom
        (show Γ(Scheme.unitModule Z, U) from (1 : Γ(Z, U))))
    rwa [← Stacks.ModuleStalk.germ_smul,
      show (v • (show Γ(Scheme.unitModule Z, U) from (1 : Γ(Z, U))) : Γ(Scheme.unitModule Z, U)) =
        show Γ(Scheme.unitModule Z, U) from v from mul_one v] at this
  have h1 : IsUnit (Z.presheaf.map (homOfLE (Z.basicOpen_le v)).op v) :=
    Z.toRingedSpace.isUnit_res_basicOpen v
  have h2 : Z.presheaf.map (homOfLE hb.ge).op (Z.presheaf.map (homOfLE (Z.basicOpen_le v)).op v) =
      v := by
    rw [ring_presheaf_map_map, ring_presheaf_map_self]
  rw [← h2]
  exact h1.map _

/-- **A trivializing section vanishes nowhere.** If multiplication by `a` is bijective on the
sections over every open inside `V`, then the germ of `a` at a point of `V` avoids
`𝔪_y · L_y`: it is a basis of the stalk. -/
theorem germ_notMem_maximalSmul_of_bijective {P : Scheme.{u}} (L : P.Modules) {V : P.Opens}
    (a : Γ(L, V))
    (ha : ∀ (V' : P.Opens) (h : V' ≤ V),
      Function.Bijective fun c : Γ(P, V') => c • L.presheaf.map (homOfLE h).op a)
    (y : P) (hy : y ∈ V) :
    (L.presheaf.germ V y hy).hom a ∉ Stacks.ModuleStalk.maximalSmul L y := by
  have hm := Stacks.Divisors.isStalkBasis_germ_of_bijective_smul (L := L) a ha y hy
  intro hmem
  have h1 := (Stacks.SheafOfModules.Invertible.mem_maximalIdeal_smul_top_iff
    hm.linearEquiv.symm _).1 hmem
  rw [(LinearEquiv.symm_apply_eq _).2 hm.linearEquiv_one.symm] at h1
  exact (IsLocalRing.notMem_maximalIdeal.2 isUnit_one) h1

section Glue

variable {Z P : Scheme.{u}} (p : P ⟶ Z) (δ : Z ⟶ P) (L : P.Modules)
  (ε : (Scheme.Modules.pullback δ).obj L ≅ Scheme.unitModule Z)

/-- The value along the section `δ` of a section of `L`: its pullback along `δ`, read as a
function through the trivialization `ε` of `δ^* L`. -/
def sectionAlong (V : P.Opens) (a : Γ(L, V)) : Γ(Z, δ ⁻¹ᵁ V) :=
  ε.hom.app (δ ⁻¹ᵁ V) (Stacks.Cech.pullbackSections δ L V a)

/-- The value along `δ` is semilinear along `δ^♯`. -/
theorem sectionAlong_smul (V : P.Opens) (c : Γ(P, V)) (a : Γ(L, V)) :
    sectionAlong δ L ε V (c • a) = δ.app V c * sectionAlong δ L ε V a := by
  simp only [sectionAlong]
  rw [Stacks.Cech.pullbackSections_smul, Scheme.Modules.Hom.app_smul]
  rfl

/-- The value along `δ` commutes with restriction. -/
theorem sectionAlong_map {V V' : P.Opens} (h : V' ≤ V) (a : Γ(L, V)) :
    sectionAlong δ L ε V' (L.presheaf.map (homOfLE h).op a) =
      Z.presheaf.map (homOfLE (Scheme.Hom.preimage_mono δ h)).op (sectionAlong δ L ε V a) := by
  simp only [sectionAlong]
  rw [Stacks.Cech.pullbackSections_map]
  exact congr($(ε.hom.mapPresheaf.naturality (homOfLE (Scheme.Hom.preimage_mono δ h)).op)
    (Stacks.Cech.pullbackSections δ L V a))

/-- **The value along `δ` of a trivializing section is a unit.** -/
theorem isUnit_sectionAlong (V : P.Opens) (a : Γ(L, V))
    (ha : ∀ (V' : P.Opens) (h : V' ≤ V),
      Function.Bijective fun c : Γ(P, V') => c • L.presheaf.map (homOfLE h).op a) :
    IsUnit (sectionAlong δ L ε V a) := by
  refine isUnit_of_forall_notMem_maximalSmul _ _ fun z hz => ?_
  have h1 : δ.base z ∈ Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn L V a :=
    (Stacks.NonvanishingLocusRestrict.mem_nonvanishingLocusOn_iff L V hz).2
      (germ_notMem_maximalSmul_of_bijective L a ha _ hz)
  have h2 : z ∈ Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn
      ((Scheme.Modules.pullback δ).obj L) (δ ⁻¹ᵁ V) (Stacks.Cech.pullbackSections δ L V a) := by
    have := Stacks.NonvanishingLocusRestrict.preimage_nonvanishingLocusOn δ L a
    exact (Set.ext_iff.1 this z).1 h1
  rw [← Stacks.SectionPowerOverOpen.nonvanishingLocusOn_congr ε] at h2
  exact ((Stacks.NonvanishingLocusRestrict.mem_nonvanishingLocusOn_iff _ _ hz).1 h2)

variable {p δ} (hδ : δ ≫ p = 𝟙 Z)

include hδ in
/-- Since `δ ≫ p = 𝟙`, the map `Γ(Z, W) → Γ(Z, (δ ≫ p)⁻¹ W)` is an isomorphism. -/
theorem isIso_app_comp (W : Z.Opens) : IsIso ((δ ≫ p).app W) := by
  rw [hδ]
  infer_instance

variable (hp : ∀ W : Z.Opens, IsAffineOpen W → Function.Surjective (p.app W))

include hδ hp in
/-- **Uniqueness of normalized trivializing sections.** Two sections of `L` over an open `T` of
`P` which both trivialize `L` there and both have value `1` along `δ` agree, provided `T` is
covered by preimages of affine opens of `Z`. -/
theorem eq_of_sectionAlong_eq_one (T : P.Opens)
    (hT : ∀ x ∈ T, ∃ W : Z.Opens, IsAffineOpen W ∧ p.base x ∈ W ∧ p ⁻¹ᵁ W ≤ T)
    (a b : Γ(L, T)) (ha : Function.Bijective fun c : Γ(P, T) => c • a)
    (hb : Function.Bijective fun c : Γ(P, T) => c • b)
    (hna : sectionAlong δ L ε T a = 1) (hnb : sectionAlong δ L ε T b = 1) : a = b := by
  obtain ⟨u, hu⟩ := Stacks.SheafOfModules.exists_units_smul_eq (X := P.toRingedSpace) (L := L)
    T a b ha hb
  have h1 : δ.app T (u : Γ(P, T)) = 1 := by
    have := sectionAlong_smul δ L ε T (u : Γ(P, T)) a
    rw [hna, mul_one] at this
    rw [← this, ← hnb]
    exact congrArg (sectionAlong δ L ε T) hu
  have hu1 : (u : Γ(P, T)) = 1 := by
    refine TopCat.Sheaf.eq_of_locally_eq' P.sheaf
      (fun W : {W : Z.Opens // IsAffineOpen W ∧ p ⁻¹ᵁ W ≤ T} => p ⁻¹ᵁ W.1) T
      (fun W => homOfLE W.2.2) ?_ _ _ ?_
    · intro x hx
      obtain ⟨W, hW, hxW, hWT⟩ := hT x hx
      exact Opens.mem_iSup.2 ⟨⟨W, hW, hWT⟩, hxW⟩
    · rintro ⟨W, hW, hWT⟩
      obtain ⟨d, hd⟩ := hp W hW (P.presheaf.map (homOfLE hWT).op u)
      have := isIso_app_comp hδ W
      have hinj : Function.Injective ((δ ≫ p).app W) :=
        (ConcreteCategory.bijective_of_isIso ((δ ≫ p).app W)).1
      have h2 : (δ ≫ p).app W d = (δ ≫ p).app W 1 := by
        change δ.app (p ⁻¹ᵁ W) (p.app W d) = δ.app (p ⁻¹ᵁ W) (p.app W 1)
        rw [hd, map_one, map_one]
        have hnat := congr($(δ.naturality (homOfLE hWT).op) (u : Γ(P, T)))
        simp only [CommRingCat.comp_apply] at hnat
        change δ.app (p ⁻¹ᵁ W) (P.presheaf.map (homOfLE hWT).op (u : Γ(P, T))) = 1
        rw [hnat, h1, map_one]
      change P.presheaf.map (homOfLE hWT).op (u : Γ(P, T)) = P.presheaf.map (homOfLE hWT).op 1
      rw [← hd, hinj h2, map_one, map_one]
  calc a = (1 : Γ(P, T)) • a := (one_smul _ a).symm
    _ = b := by rw [← hu1]; exact hu

include hδ in
/-- **Existence of normalized trivializing sections.** If `L` is trivial over `p⁻¹ U`, it has a
trivializing section there with value `1` along `δ`. -/
theorem exists_sectionAlong_eq_one (U : Z.Opens)
    (e : (Scheme.Modules.pullback (p ⁻¹ᵁ U).ι).obj L ≅ Scheme.unitModule (p ⁻¹ᵁ U)) :
    ∃ b : Γ(L, p ⁻¹ᵁ U), (∀ (V' : P.Opens) (h : V' ≤ p ⁻¹ᵁ U),
      Function.Bijective fun c : Γ(P, V') => c • L.presheaf.map (homOfLE h).op b) ∧
        sectionAlong δ L ε (p ⁻¹ᵁ U) b = 1 := by
  obtain ⟨a, ha⟩ := exists_trivializing_of_iso' (p ⁻¹ᵁ U) L e
  have hv := isUnit_sectionAlong δ L ε (p ⁻¹ᵁ U) a ha
  have := isIso_app_comp hδ U
  have hbij := ConcreteCategory.bijective_of_isIso ((δ ≫ p).app U)
  obtain ⟨w, hw⟩ := hbij.2
    (show Γ(Z, (δ ≫ p) ⁻¹ᵁ U) from (↑hv.unit⁻¹ : Γ(Z, δ ⁻¹ᵁ p ⁻¹ᵁ U)))
  obtain ⟨w', hw'⟩ := hbij.2
    (show Γ(Z, (δ ≫ p) ⁻¹ᵁ U) from (↑hv.unit : Γ(Z, δ ⁻¹ᵁ p ⁻¹ᵁ U)))
  have hww : w * w' = 1 := hbij.1 (by
    rw [map_mul, map_one, hw, hw']
    exact hv.unit.inv_mul)
  have hwu : IsUnit (p.app U w) :=
    (show IsUnit w from ⟨⟨w, w', hww, by rw [mul_comm]; exact hww⟩, rfl⟩).map (p.app U).hom
  refine ⟨p.app U w • a, fun V' h => ?_, ?_⟩
  · have := Stacks.SheafOfModules.bijective_smul_units_smul (X := P.toRingedSpace) (L := L)
      (p ⁻¹ᵁ U) a ha hwu.unit V' h
    rwa [hwu.unit_spec] at this
  · rw [sectionAlong_smul]
    change (δ ≫ p).app U w * _ = 1
    rw [hw]
    exact hv.val_inv_mul

include hδ hp ε in
/-- **The gluing step of the theorem of the cube.** Let `p : P ⟶ Z` have a section `δ` with
`δ^* L` trivial, and suppose every function on the preimage of an affine open of `Z` is pulled
back from it. If `L` is trivial over the preimages of the members of an open cover of `Z`, then
`L` is trivial: the trivializing sections normalized along `δ` are unique, hence glue. -/
theorem nonempty_iso_unit_of_cover
    (hU : ∀ z : Z, ∃ U : Z.Opens, z ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (p ⁻¹ᵁ U).ι).obj L ≅ Scheme.unitModule (p ⁻¹ᵁ U))) :
    Nonempty (L ≅ Scheme.unitModule P) := by
  choose U hzU e using hU
  choose b hb hbn using fun z => exists_sectionAlong_eq_one L ε hδ (U z) (e z).some
  have hcover : (⊤ : P.Opens) ≤ ⨆ z, p ⁻¹ᵁ U z := fun x _ =>
    Opens.mem_iSup.2 ⟨p.base x, hzU _⟩
  obtain ⟨s, hs, -⟩ := Stacks.SheafOfModules.existsUnique_glue (X := P.toRingedSpace) (M := L)
    (fun z => p ⁻¹ᵁ U z) ⊤ (fun _ => le_top) hcover b (fun z w => by
      refine eq_of_sectionAlong_eq_one L ε hδ hp _ (fun x hx => ?_) _ _ ?_ ?_ ?_ ?_
      · obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
          (show p.base x ∈ U z ⊓ U w from hx) (U z ⊓ U w).isOpen
        exact ⟨W, hW, hxW, fun y hy => hWU hy⟩
      · exact hb z _ inf_le_left
      · exact hb w _ inf_le_right
      · change sectionAlong δ L ε _ (L.presheaf.map (homOfLE inf_le_left).op (b z)) = 1
        rw [sectionAlong_map, hbn, map_one]
      · change sectionAlong δ L ε _ (L.presheaf.map (homOfLE inf_le_right).op (b w)) = 1
        rw [sectionAlong_map, hbn, map_one])
  refine Stacks.SheafOfModules.nonempty_iso_unit_of_bijective_smul_on_cover (X := P.toRingedSpace)
    L (Stacks.SheafOfModules.sectionsOfTop L s) (fun z => p ⁻¹ᵁ U z)
    (IsOpenCover.mk (eq_top_iff.2 hcover)) fun z V hV => ?_
  have : (Stacks.SheafOfModules.sectionsOfTop L s).eval (op V) =
      L.presheaf.map (homOfLE hV).op (b z) := by
    rw [← hs z]
    exact (presheaf_map_map L hV le_top s).symm
  rw [this]
  exact hb z V hV

end Glue

section Cube

variable {Z X Y P : Scheme.{u}} {fX : X ⟶ Z} {fY : Y ⟶ Z} {r : P ⟶ X} {q : P ⟶ Y}
  (H : IsPullback r q fX fY)
  [IsProper fX] [Flat fX] [LocallyOfFinitePresentation fX] [GeometricallyIntegral fX]
  [IsProper fY] [Flat fY] [LocallyOfFinitePresentation fY] [GeometricallyIntegral fY]
  (σ : Z ⟶ X) (τ : Z ⟶ Y) (hσ : σ ≫ fX = 𝟙 _) (hτ : τ ≫ fY = 𝟙 _)
  (j₁ : Y ⟶ P) (hj₁r : j₁ ≫ r = fY ≫ σ) (hj₁q : j₁ ≫ q = 𝟙 Y)
  (j₂ : X ⟶ P) (hj₂r : j₂ ≫ r = 𝟙 X) (hj₂q : j₂ ≫ q = fX ≫ τ)
  (L : P.Modules) [Stacks.SheafOfModules.IsInvertible P.presheaf P.ringCatSheaf.2 L]
  (e₁ : Nonempty ((Scheme.Modules.pullback j₁).obj L ≅ Scheme.unitModule Y))
  (e₂ : Nonempty ((Scheme.Modules.pullback j₂).obj L ≅ Scheme.unitModule X))

include H hσ hτ hj₁r hj₁q hj₂r hj₂q e₁ e₂ in
/-- **The theorem of the cube over a connected base.** Let `P = X ×_Z Y` with `X ⟶ Z` and
`Y ⟶ Z` proper, flat, of finite presentation with geometrically integral fibres and with sections
`σ`, `τ`, and let `L` be invertible on `P`, trivial along the two faces `j₁` and `j₂` and on one
fibre of `p : P ⟶ Z`. If `Z` is connected, `L` is trivial. -/
theorem nonempty_iso_unit [ConnectedSpace Z] (p : P ⟶ Z) (hp : r ≫ fX = p) (z₀ : Z)
    (hz₀ : Nonempty ((Scheme.Modules.pullback (pullback.fst p (Z.fromSpecResidueField z₀))).obj
      L ≅ Scheme.unitModule (pullback p (Z.fromSpecResidueField z₀)))) :
    Nonempty (L ≅ Scheme.unitModule P) := by
  subst hp
  have : IsProper r := MorphismProperty.of_isPullback H.flip inferInstance
  have : Flat r := MorphismProperty.of_isPullback H.flip inferInstance
  have : LocallyOfFinitePresentation r := MorphismProperty.of_isPullback H.flip inferInstance
  have := geometricallyIntegral_comp H
  have hδ : (τ ≫ j₁) ≫ r ≫ fX = 𝟙 Z := by
    rw [Category.assoc, ← Category.assoc j₁, hj₁r, Category.assoc, hσ, Category.comp_id, hτ]
  obtain ⟨e⟩ := e₁
  let ε : (Scheme.Modules.pullback (τ ≫ j₁)).obj L ≅ Scheme.unitModule Z :=
    ((Scheme.Modules.pullbackComp τ j₁).app L).symm ≪≫ (Scheme.Modules.pullback τ).mapIso e ≪≫
      Scheme.Modules.pullbackUnitIso τ
  refine nonempty_iso_unit_of_cover L ε hδ
    (fun W hW => surjective_app_of_geometricallyIntegral _ hW) fun z => ?_
  obtain ⟨U, hz, -, hU⟩ := forall_exists_isAffineOpen_trivial H σ τ hσ hτ j₁ hj₁r hj₁q j₂ hj₂r
    hj₂q L ⟨e⟩ e₂ z₀ hz₀ z
  exact ⟨U, hz, hU⟩

end Cube

end Stacks.Cube

end
