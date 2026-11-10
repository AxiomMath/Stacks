module

public import StacksFrontier.AlgebraicGeometry.Conormal.SplitSequence
public import StacksFrontier.AlgebraicGeometry.Conormal.Stalk
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.NakayamaGenerators

/-!
# Cotangent fibres of two nested immersions

Let `i : Z ⟶ Y` and `j : Y ⟶ X` be immersions of schemes, let `z : Z` and write `x = j (i z)`.
The defining ideal sheaf of `j` is contained in that of `i ≫ j`, so their stalks `I_x` and `J_x`
at `x` satisfy `I_x ⊆ J_x`, and the inclusion descends to a map of cotangent fibres
`I_x / 𝔪_x I_x ⟶ J_x / 𝔪_x J_x`, linear over the residue field at `x`.

When the conormal sequence of the pair is exact and locally split, the stalk at `z` of its
left-hand map `i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X}` admits a retraction of `𝒪_{Z,z}`-modules: a retraction
over a neighbourhood of `z` induces one on stalks, because the germ of a section may be computed
after restricting into that neighbourhood.  A split injection stays injective after reduction
modulo the maximal ideal, which is how [Stacks Project, Tag 068Z] obtains injectivity of the map
of cotangent fibres.

## Main definitions

* `Stacks.AlgebraicGeometry.idealCotangentFiberMap`: the map of cotangent fibres.
* `Stacks.AlgebraicGeometry.ambientStalkModule`: the stalk at `z` of a sheaf of modules on `Z`,
  as a module over the local ring of `X` at `x`.

## Main results

* `Stacks.AlgebraicGeometry.idealCotangentFiberMap_mk`: the map sends the class of a germ to the
  class of the same germ, which pins it down.
* `Stacks.AlgebraicGeometry.injective_idealCotangentFiberMap_of_stalkRetraction`: the map of
  cotangent fibres is injective as soon as it is computed, through surjections of its two sides,
  by a morphism of sheaves of modules on `Z` with a retraction near `z`.
* `Stacks.AlgebraicGeometry.injective_idealCotangentFiberMap_of_conormalClasses`: the same
  injectivity from a morphism with a retraction near `z` together with the conormal classes of
  germs, which need be neither surjective nor defined on all of the two stalks.

## References

* [Stacks Project, Tag 068Z](https://stacks.math.columbia.edu/tag/068Z)
* [Stacks Project, Tag 062S](https://stacks.math.columbia.edu/tag/062S)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.AlgebraicGeometry

open Stacks.AlgebraicGeometry.RegularIdealSheaf

/-! ### Reduction of a linear map modulo an ideal -/

/-- **The reduction of a linear map modulo an ideal**, `M / m M ⟶ N / m N`, linear over
`R / m`. -/
private def mapQSMulTop {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (m : Ideal R) (f : M →ₗ[R] N) :
    (M ⧸ m • (⊤ : Submodule R M)) →ₗ[R ⧸ m] (N ⧸ m • (⊤ : Submodule R N)) where
  toFun := Submodule.mapQ _ _ f (Submodule.smul_top_le_comap_smul_top m f)
  map_add' := map_add _
  map_smul' c u := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    rw [RingHom.id_apply, Module.Quotient.mk_smul_mk, Submodule.mapQ_apply,
      Submodule.mapQ_apply, map_smul, Module.Quotient.mk_smul_mk]

private theorem mapQSMulTop_mk {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (m : Ideal R) (f : M →ₗ[R] N) (a : M) :
    mapQSMulTop m f (Submodule.Quotient.mk a) = Submodule.Quotient.mk (f a) := rfl

/-! ### The map of cotangent fibres -/

variable {Z Y X : Scheme.{u}}

/-- Stalk ideals are monotone in the ideal subsheaf. -/
public theorem stalkIdeal_mono {W : LocallyRingedSpace.{u}}
    {I J : (Stacks.RingedSpace.structureSheafModule W.toRingedSpace).Submodule} (h : I ≤ J)
    (w : W) :
    Stacks.RingedSpace.stalkIdeal I w ≤ Stacks.RingedSpace.stalkIdeal J w := by
  refine Ideal.span_mono ?_
  rintro a ⟨U, hw, s, hs, rfl⟩
  exact ⟨U, hw, s, SheafOfModules.Submodule.le_iff.mp h _ hs, rfl⟩

/-- The stalk at `j (i z)` of the defining ideal of `Y` is contained in that of `Z`. -/
private theorem stalkIdeal_le_comp (i : Z ⟶ Y) (j : Y ⟶ X) (z : Z) :
    Stacks.RingedSpace.stalkIdeal (X := X.toLocallyRingedSpace)
        (definingIdealOfHom j) (j (i z)) ≤
      Stacks.RingedSpace.stalkIdeal (X := X.toLocallyRingedSpace)
        (definingIdealOfHom (i ≫ j)) (j (i z)) :=
  stalkIdeal_mono (definingIdealOfHom_le_comp i j) _

/-- **The map `I_x / 𝔪_x I_x ⟶ J_x / 𝔪_x J_x` of cotangent fibres** of two nested immersions
`i : Z ⟶ Y` and `j : Y ⟶ X` at `x = j (i z)`: it is induced by the inclusion of the stalk at
`x` of the defining ideal of `Y` into that of `Z`, and is linear over the residue field. -/
@[no_expose]
def idealCotangentFiberMap (i : Z ⟶ Y) (j : Y ⟶ X) (z : Z) :
    Stacks.RingedSpace.idealCotangentFiber (X := X.toLocallyRingedSpace)
        (definingIdealOfHom j) (j (i z)) →ₗ[
      X.presheaf.stalk (j (i z)) ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk (j (i z)))]
      Stacks.RingedSpace.idealCotangentFiber (X := X.toLocallyRingedSpace)
        (definingIdealOfHom (i ≫ j)) (j (i z)) :=
  mapQSMulTop _ (Submodule.inclusion (stalkIdeal_le_comp i j z))

/-- **The map of cotangent fibres sends the class of a germ to the class of the same germ.** -/
theorem idealCotangentFiberMap_mk (i : Z ⟶ Y) (j : Y ⟶ X) (z : Z)
    (a : Stacks.RingedSpace.stalkIdeal (X := X.toLocallyRingedSpace)
      (definingIdealOfHom j) (j (i z)))
    (ha : (a : X.presheaf.stalk (j (i z))) ∈
      Stacks.RingedSpace.stalkIdeal (X := X.toLocallyRingedSpace)
        (definingIdealOfHom (i ≫ j)) (j (i z))) :
    idealCotangentFiberMap i j z (Submodule.Quotient.mk a) = Submodule.Quotient.mk ⟨a, ha⟩ :=
  mapQSMulTop_mk _ _ a

/-! ### Reduction of the injectivity to a split injection of stalks -/

/-- A linear map into the cotangent fibre `I / m I` annihilates `m` times its source. -/
private theorem apply_eq_zero_of_mem_smul_top {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {m I : Ideal R} (p : M →ₗ[R] (I ⧸ m • (⊤ : Submodule R I))) {u : M}
    (hu : u ∈ m • (⊤ : Submodule R M)) : p u = 0 := by
  refine Submodule.smul_induction_on hu (fun s hs b _ => ?_) (fun b d hb hd => ?_)
  · rw [map_smul]
    obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (p b)
    rw [← hw, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hs Submodule.mem_top
  · rw [map_add, hb, hd, add_zero]

/-- **Injectivity of the map of cotangent fibres from a split injection of stalk modules.**
Suppose given `𝒪_{X,x}`-modules `M` and `N` and a map `f : M ⟶ N` with a retraction, a
surjection `p : M ⟶ I_x / 𝔪_x I_x`, and a map `q : N ⟶ J_x / 𝔪_x J_x` whose kernel is contained
in `𝔪_x N`, such that `q ∘ f` is the map of cotangent fibres composed with `p`.  Then the map of
cotangent fibres is injective.

This is the final step of [Stacks Project, Tag 068Z]: `M` and `N` are the stalks at `z` of
`i^* 𝒞_{Y/X}` and of `𝒞_{Z/X}`, `f` is the stalk of the left-hand map of the conormal sequence,
and the retraction comes from a local splitting. -/
private theorem injective_idealCotangentFiberMap_of_split (i : Z ⟶ Y) (j : Y ⟶ X) (z : Z)
    {M N : Type*} [AddCommGroup M] [Module (X.presheaf.stalk (j (i z))) M] [AddCommGroup N]
    [Module (X.presheaf.stalk (j (i z))) N]
    (f : M →ₗ[X.presheaf.stalk (j (i z))] N) (ρ : N →ₗ[X.presheaf.stalk (j (i z))] M)
    (hρ : ∀ a : M, ρ (f a) = a)
    (p : M →ₗ[X.presheaf.stalk (j (i z))]
      Stacks.RingedSpace.idealCotangentFiber (X := X.toLocallyRingedSpace)
        (definingIdealOfHom j) (j (i z)))
    (hp : Function.Surjective p)
    (q : N →ₗ[X.presheaf.stalk (j (i z))]
      Stacks.RingedSpace.idealCotangentFiber (X := X.toLocallyRingedSpace)
        (definingIdealOfHom (i ≫ j)) (j (i z)))
    (hq : ∀ ν : N, q ν = 0 →
      ν ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (j (i z))) •
        (⊤ : Submodule (X.presheaf.stalk (j (i z))) N))
    (hsq : ∀ μ : M, q (f μ) = idealCotangentFiberMap i j z (p μ)) :
    Function.Injective (idealCotangentFiberMap i j z) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro ξ hξ
  obtain ⟨μ, rfl⟩ := hp ξ
  have hmem : μ ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (j (i z))) •
      (⊤ : Submodule (X.presheaf.stalk (j (i z))) M) := by
    rw [← hρ μ]
    exact Submodule.smul_top_le_comap_smul_top _ ρ (hq _ ((hsq μ).trans hξ))
  exact apply_eq_zero_of_mem_smul_top p hmem

/-! ### Retractions on stalks -/

section StalkRetraction

variable {W : Scheme.{u}} {A B : W.Modules}

/-- The module structure over the stalk of the structure sheaf on the stalk of a sheaf of
modules. -/
abbrev stalkModule (M : W.Modules) (w : W) :
    Module (ToType (W.presheaf.stalk w))
      (ToType (TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf w)) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := W.presheaf) M.val w

/-- Germ-semilinearity of the scalar action on the stalk of a sheaf of modules. -/
private theorem germ_smul (M : W.Modules) (w : W) (U : W.Opens) (hU : w ∈ U) (c : Γ(W, U))
    (x : Γ(M, U)) :
    letI := stalkModule M w
    TopCat.Presheaf.germ (C := Ab.{u}) M.presheaf U w hU (c • x) =
      W.presheaf.germ U w hU c • TopCat.Presheaf.germ (C := Ab.{u}) M.presheaf U w hU x :=
  PresheafOfModules.germ_smul (R := W.presheaf) M.val w U hU c x

/-- The intersection of an open with another, written as the image under the inclusion of the
first of the preimage of the second. -/
private abbrev imPre (V U : W.Opens) : W.Opens := V.ι ''ᵁ (V.ι ⁻¹ᵁ U)

private theorem imPre_le (V U : W.Opens) : imPre V U ≤ U := Scheme.Hom.image_preimage_le V.ι U

private theorem mem_imPre {V U : W.Opens} {w : W} (hV : w ∈ V) (hU : w ∈ U) : w ∈ imPre V U := by
  change w ∈ V.ι ''ᵁ (V.ι ⁻¹ᵁ U)
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact ⟨hV, hU⟩

private theorem imPre_mono (V : W.Opens) {U U' : W.Opens} (h : U' ≤ U) :
    imPre V U' ≤ imPre V U :=
  Scheme.Hom.image_mono _ (V.ι.preimage_mono h)

/-- Two composites of restriction maps of a presheaf on a space agree. -/
private theorem map_comp_map_eq {P : TopCat.Presheaf Ab.{u} W} {U₁ U₂ U₂' U₃ : W.Opens}
    (a : U₂ ⟶ U₁) (b : U₃ ⟶ U₂) (a' : U₂' ⟶ U₁) (b' : U₃ ⟶ U₂') :
    P.map a.op ≫ P.map b.op = P.map a'.op ≫ P.map b'.op := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-- The scalar action on the sections of a restriction is the action of the ambient scheme
through the section isomorphism of the open immersion. -/
private theorem restrict_smul_eq (V : W.Opens) (U : V.toScheme.Opens) (M : W.Modules)
    (c : Γ(V.toScheme, U)) (y : Γ(M, V.ι ''ᵁ U)) :
    @HSMul.hSMul (ToType Γ(V.toScheme, U))
        (ToType Γ((Scheme.Modules.restrictFunctor V.ι).obj M, U))
        (ToType Γ((Scheme.Modules.restrictFunctor V.ι).obj M, U)) _ c y =
      (V.ι.appIso U).inv c • y := rfl

/-- A morphism of restrictions along the inclusion of `V`, read on the sections of the original
sheaves over the part of an open that lies in `V`. -/
private def rApp (V : W.Opens)
    (r : (Scheme.Modules.restrictFunctor V.ι).obj B ⟶
      (Scheme.Modules.restrictFunctor V.ι).obj A) (U : W.Opens) :
    Γ(B, imPre V U) ⟶ Γ(A, imPre V U) :=
  r.app (V.ι ⁻¹ᵁ U)

/-- A morphism of restrictions along an open immersion is linear for the scalars of the ambient
scheme. -/
private theorem rApp_smul (V : W.Opens)
    (r : (Scheme.Modules.restrictFunctor V.ι).obj B ⟶
      (Scheme.Modules.restrictFunctor V.ι).obj A) (U : W.Opens)
    (c : Γ(W, imPre V U)) (y : Γ(B, imPre V U)) :
    rApp V r U (c • y) = c • rApp V r U y := by
  have hc : (V.ι.appIso (V.ι ⁻¹ᵁ U)).inv ((V.ι.appIso (V.ι ⁻¹ᵁ U)).hom c) = c :=
    CategoryTheory.Iso.hom_inv_id_apply (V.ι.appIso (V.ι ⁻¹ᵁ U)) c
  have h := Scheme.Modules.Hom.app_smul r ((V.ι.appIso (V.ι ⁻¹ᵁ U)).hom c) y
  rw [restrict_smul_eq V (V.ι ⁻¹ᵁ U) B ((V.ι.appIso (V.ι ⁻¹ᵁ U)).hom c) y,
    restrict_smul_eq V (V.ι ⁻¹ᵁ U) A ((V.ι.appIso (V.ι ⁻¹ᵁ U)).hom c)
      (r.app (V.ι ⁻¹ᵁ U) y), hc] at h
  exact h

/-- Naturality of a morphism of restrictions, read on the sections of the original sheaves. -/
private theorem rApp_naturality (V : W.Opens) {U U' : W.Opens} (h : U' ≤ U)
    (r : (Scheme.Modules.restrictFunctor V.ι).obj B ⟶
      (Scheme.Modules.restrictFunctor V.ι).obj A) :
    B.presheaf.map (homOfLE (imPre_mono V h)).op ≫ rApp V r U' =
      rApp V r U ≫ A.presheaf.map (homOfLE (imPre_mono V h)).op := by
  have hnat := r.mapPresheaf.naturality (homOfLE (V.ι.preimage_mono h)).op
  simp only [Scheme.Modules.mapPresheaf_app] at hnat
  rw [Scheme.Modules.restrict_map, Scheme.Modules.restrict_map,
    Subsingleton.elim (V.ι.opensFunctor.map (homOfLE (V.ι.preimage_mono h)))
      (homOfLE (imPre_mono V h))] at hnat
  exact hnat

/-- A section over an open is restricted into `V` and hit with the retraction; its germ is the
component of the cocone computing the retraction on stalks. -/
private def restrictRetractionApp (V : W.Opens) (w : W) (hw : w ∈ V)
    (r : (Scheme.Modules.restrictFunctor V.ι).obj B ⟶
      (Scheme.Modules.restrictFunctor V.ι).obj A) (U : W.Opens) (hU : w ∈ U) :
    Γ(B, U) ⟶ TopCat.Presheaf.stalk (C := Ab.{u}) A.presheaf w :=
  B.presheaf.map (homOfLE (imPre_le V U)).op ≫ rApp V r U ≫
    TopCat.Presheaf.germ (C := Ab.{u}) A.presheaf (imPre V U) w (mem_imPre hw hU)

private theorem restrictRetractionApp_res (V : W.Opens) (w : W) (hw : w ∈ V)
    (r : (Scheme.Modules.restrictFunctor V.ι).obj B ⟶
      (Scheme.Modules.restrictFunctor V.ι).obj A) {U U' : W.Opens} (hU : w ∈ U) (hU' : w ∈ U')
    (h : U' ≤ U) :
    B.presheaf.map (homOfLE h).op ≫ restrictRetractionApp V w hw r U' hU' =
      restrictRetractionApp V w hw r U hU := by
  rw [restrictRetractionApp, restrictRetractionApp, ← Category.assoc,
    map_comp_map_eq (P := B.presheaf) (homOfLE h) (homOfLE (imPre_le V U'))
      (homOfLE (imPre_le V U)) (homOfLE (imPre_mono V h))]
  slice_lhs 2 3 => rw [rApp_naturality V h r]
  slice_lhs 3 4 => rw [TopCat.Presheaf.germ_res]

/-- The stalk of the source, as a cocone over the diagram computing the stalk of the target. -/
private def restrictRetractionCocone (V : W.Opens) (w : W) (hw : w ∈ V)
    (r : (Scheme.Modules.restrictFunctor V.ι).obj B ⟶
      (Scheme.Modules.restrictFunctor V.ι).obj A) :
    Limits.Cocone ((OpenNhds.inclusion w).op ⋙ B.presheaf) where
  pt := TopCat.Presheaf.stalk (C := Ab.{u}) A.presheaf w
  ι :=
    { app := fun Uop => restrictRetractionApp V w hw r Uop.unop.1 Uop.unop.2
      naturality := fun Uop Uop' f =>
        (restrictRetractionApp_res V w hw r Uop.unop.2 Uop'.unop.2
          ((OpenNhds.inclusion w).map f.unop).le).trans (Category.comp_id _).symm }

/-- The map on stalks produced by a retraction over a neighbourhood. -/
private def restrictRetractionHom (V : W.Opens) (w : W) (hw : w ∈ V)
    (r : (Scheme.Modules.restrictFunctor V.ι).obj B ⟶
      (Scheme.Modules.restrictFunctor V.ι).obj A) :
    ToType (TopCat.Presheaf.stalk (C := Ab.{u}) B.presheaf w) →+
      ToType (TopCat.Presheaf.stalk (C := Ab.{u}) A.presheaf w) :=
  (Limits.colimit.desc _ (restrictRetractionCocone V w hw r)).hom

private theorem restrictRetractionHom_germ (V : W.Opens) (w : W) (hw : w ∈ V)
    (r : (Scheme.Modules.restrictFunctor V.ι).obj B ⟶
      (Scheme.Modules.restrictFunctor V.ι).obj A)
    (U : W.Opens) (hU : w ∈ U) (s : Γ(B, U)) :
    restrictRetractionHom V w hw r (TopCat.Presheaf.germ (C := Ab.{u}) B.presheaf U w hU s) =
      TopCat.Presheaf.germ (C := Ab.{u}) A.presheaf (imPre V U) w (mem_imPre hw hU)
        (rApp V r U (B.presheaf.map (homOfLE (imPre_le V U)).op s)) :=
  ConcreteCategory.congr_hom
    (Limits.colimit.ι_desc (restrictRetractionCocone V w hw r) (op (⟨U, hU⟩ : OpenNhds w))) s

/-- The map on stalks produced by a retraction is linear over the stalk of the structure
sheaf. -/
private theorem restrictRetractionHom_smul (V : W.Opens) (w : W) (hw : w ∈ V)
    (r : (Scheme.Modules.restrictFunctor V.ι).obj B ⟶
      (Scheme.Modules.restrictFunctor V.ι).obj A)
    (c : ToType (W.presheaf.stalk w))
    (m : ToType (TopCat.Presheaf.stalk (C := Ab.{u}) B.presheaf w)) :
    letI := stalkModule A w
    letI := stalkModule B w
    restrictRetractionHom V w hw r (c • m) = c • restrictRetractionHom V w hw r m := by
  let _ := stalkModule A w
  let _ := stalkModule B w
  obtain ⟨U₁, h₁, c₀, hc⟩ := TopCat.Presheaf.exists_germ_eq W.presheaf c
  obtain ⟨U₂, h₂, m₀, hm⟩ := TopCat.Presheaf.exists_germ_eq B.presheaf m
  have hmem : w ∈ U₁ ⊓ U₂ := ⟨h₁, h₂⟩
  set c₁ := W.presheaf.map (homOfLE (inf_le_left (a := U₁) (b := U₂))).op c₀ with hc₁
  set m₁ := B.presheaf.map (homOfLE (inf_le_right (a := U₁) (b := U₂))).op m₀ with hm₁
  have hc' : W.presheaf.germ (U₁ ⊓ U₂) w hmem c₁ = c :=
    (TopCat.Presheaf.germ_res_apply W.presheaf (homOfLE inf_le_left) w hmem c₀).trans hc
  have hm' : TopCat.Presheaf.germ (C := Ab.{u}) B.presheaf (U₁ ⊓ U₂) w hmem m₁ = m :=
    (TopCat.Presheaf.germ_res_apply B.presheaf (homOfLE inf_le_right) w hmem m₀).trans hm
  rw [← hc', ← hm', ← germ_smul B w (U₁ ⊓ U₂) hmem c₁ m₁,
    restrictRetractionHom_germ, restrictRetractionHom_germ, Scheme.Modules.map_smul,
    rApp_smul V r (U₁ ⊓ U₂) (W.presheaf.map (homOfLE (imPre_le V (U₁ ⊓ U₂))).op c₁)
      (B.presheaf.map (homOfLE (imPre_le V (U₁ ⊓ U₂))).op m₁),
    germ_smul A w (imPre V (U₁ ⊓ U₂)) (mem_imPre hw hmem),
    TopCat.Presheaf.germ_res_apply W.presheaf (homOfLE (imPre_le V (U₁ ⊓ U₂))) w
      (mem_imPre hw hmem)]

/-- The retraction on stalks, as a linear map. -/
private def restrictRetraction (V : W.Opens) (w : W) (hw : w ∈ V)
    (r : (Scheme.Modules.restrictFunctor V.ι).obj B ⟶
      (Scheme.Modules.restrictFunctor V.ι).obj A) :
    letI := stalkModule A w
    letI := stalkModule B w
    ToType (TopCat.Presheaf.stalk (C := Ab.{u}) B.presheaf w) →ₗ[ToType (W.presheaf.stalk w)]
      ToType (TopCat.Presheaf.stalk (C := Ab.{u}) A.presheaf w) :=
  letI := stalkModule A w
  letI := stalkModule B w
  { toFun := restrictRetractionHom V w hw r
    map_add' := map_add _
    map_smul' := restrictRetractionHom_smul V w hw r }

/-- The additive map on stalks induced by a morphism of sheaves of modules. -/
def stalkHom (ψ : A ⟶ B) (w : W) :
    ToType (TopCat.Presheaf.stalk (C := Ab.{u}) A.presheaf w) →+
      ToType (TopCat.Presheaf.stalk (C := Ab.{u}) B.presheaf w) :=
  ((TopCat.Presheaf.stalkFunctor Ab.{u} w).map ψ.mapPresheaf).hom

/-- The map `stalkHom ψ w` sends the germ at `w` of a section `t` of `A` over `U` to the germ
at `w` of `ψ.app U t`. -/
theorem stalkHom_germ (ψ : A ⟶ B) (w : W) (U : W.Opens) (hU : w ∈ U) (t : Γ(A, U)) :
    stalkHom ψ w (TopCat.Presheaf.germ (C := Ab.{u}) A.presheaf U w hU t) =
      TopCat.Presheaf.germ (C := Ab.{u}) B.presheaf U w hU (ψ.app U t) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U w hU ψ.mapPresheaf t

/-- The linear map on stalks induced by a morphism of sheaves of modules. -/
def stalkLinearMap (ψ : A ⟶ B) (w : W) :
    letI := stalkModule A w
    letI := stalkModule B w
    ToType (TopCat.Presheaf.stalk (C := Ab.{u}) A.presheaf w) →ₗ[ToType (W.presheaf.stalk w)]
      ToType (TopCat.Presheaf.stalk (C := Ab.{u}) B.presheaf w) :=
  letI := stalkModule A w
  letI := stalkModule B w
  { toFun := fun a => stalkHom ψ w a
    map_add' := map_add (stalkHom ψ w)
    map_smul' := fun c m => by
      obtain ⟨U₁, h₁, c₀, hc⟩ := TopCat.Presheaf.exists_germ_eq W.presheaf c
      obtain ⟨U₂, h₂, m₀, hm⟩ := TopCat.Presheaf.exists_germ_eq A.presheaf m
      have hmem : w ∈ U₁ ⊓ U₂ := ⟨h₁, h₂⟩
      set c₁ := W.presheaf.map (homOfLE (inf_le_left (a := U₁) (b := U₂))).op c₀ with hc₁
      set m₁ := A.presheaf.map (homOfLE (inf_le_right (a := U₁) (b := U₂))).op m₀ with hm₁
      have hc' : W.presheaf.germ (U₁ ⊓ U₂) w hmem c₁ = c :=
        (TopCat.Presheaf.germ_res_apply W.presheaf (homOfLE inf_le_left) w hmem c₀).trans hc
      have hm' : TopCat.Presheaf.germ (C := Ab.{u}) A.presheaf (U₁ ⊓ U₂) w hmem m₁ = m :=
        (TopCat.Presheaf.germ_res_apply A.presheaf (homOfLE inf_le_right) w hmem m₀).trans hm
      rw [RingHom.id_apply, ← hc', ← hm', ← germ_smul A w (U₁ ⊓ U₂) hmem c₁ m₁,
        stalkHom_germ, stalkHom_germ, Scheme.Modules.Hom.app_smul,
        germ_smul B w (U₁ ⊓ U₂) hmem] }

/-- **A morphism of sheaves of modules whose restriction to a neighbourhood of a point admits a
retraction is a split injection on the stalk at that point.** -/
private theorem exists_stalkLinearMap_retraction (ψ : A ⟶ B) (w : W) (V : W.Opens)
    (hw : w ∈ V)
    (r : (Scheme.Modules.restrictFunctor V.ι).obj B ⟶
      (Scheme.Modules.restrictFunctor V.ι).obj A)
    (hr : (Scheme.Modules.restrictFunctor V.ι).map ψ ≫ r = 𝟙 _) :
    letI := stalkModule A w
    letI := stalkModule B w
    ∃ ρ : ToType (TopCat.Presheaf.stalk (C := Ab.{u}) B.presheaf w) →ₗ[
        ToType (W.presheaf.stalk w)]
      ToType (TopCat.Presheaf.stalk (C := Ab.{u}) A.presheaf w),
      ∀ a, ρ (stalkLinearMap ψ w a) = a := by
  let _ := stalkModule A w
  let _ := stalkModule B w
  refine ⟨restrictRetraction V w hw r, fun a => ?_⟩
  obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq A.presheaf a
  have hid : ψ.app (imPre V U) ≫ rApp V r U = 𝟙 Γ(A, imPre V U) := by
    have h1 := congrArg (fun m => Scheme.Modules.Hom.app m (V.ι ⁻¹ᵁ U)) hr
    rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app] at h1
    exact h1
  have hnatψ : ψ.app (imPre V U) (A.presheaf.map (homOfLE (imPre_le V U)).op s) =
      B.presheaf.map (homOfLE (imPre_le V U)).op (ψ.app U s) := by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
    exact ConcreteCategory.congr_hom (ψ.mapPresheaf.naturality (homOfLE (imPre_le V U)).op) s
  have hcomp : ∀ t : Γ(A, imPre V U), rApp V r U (ψ.app (imPre V U) t) = t := fun t => by
    rw [← ConcreteCategory.comp_apply, hid, ConcreteCategory.id_apply]
  change restrictRetractionHom V w hw r
    (stalkHom ψ w (TopCat.Presheaf.germ (C := Ab.{u}) A.presheaf U w hU s)) = _
  rw [stalkHom_germ, restrictRetractionHom_germ, ← hnatψ, hcomp,
    TopCat.Presheaf.germ_res_apply A.presheaf (homOfLE (imPre_le V U)) w (mem_imPre hw hU)]

end StalkRetraction

/-! ### The conormal sequence of a pair of immersions -/

/-- **The stalk of the left-hand map of a locally split conormal sequence is a split
injection.** For immersions `i : Z ⟶ Y` and `j : Y ⟶ X` whose conormal sequence is exact and
locally split and for `z : Z`, the map `(i^* 𝒞_{Y/X})_z ⟶ (𝒞_{Z/X})_z` admits a retraction of
`𝒪_{Z,z}`-modules. -/
private theorem exists_conormalSequenceLeftMap_stalk_retraction (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion j] (hS : IsSplitExactConormalSequence i j) (z : Z) :
    letI := stalkModule ((modulePullback i.toLRSHom.toShHom).obj
      (Stacks.ClosedImmersion.conormalSheaf j.liftCoborder.toLRSHom.toShHom)) z
    letI := stalkModule
      (Stacks.ClosedImmersion.conormalSheaf (i ≫ j).liftCoborder.toLRSHom.toShHom) z
    ∃ ρ : ToType (TopCat.Presheaf.stalk (C := Ab.{u})
          (Scheme.Modules.presheaf (Stacks.ClosedImmersion.conormalSheaf
            (i ≫ j).liftCoborder.toLRSHom.toShHom)) z) →ₗ[ToType (Z.presheaf.stalk z)]
        ToType (TopCat.Presheaf.stalk (C := Ab.{u})
          (Scheme.Modules.presheaf ((modulePullback i.toLRSHom.toShHom).obj
            (Stacks.ClosedImmersion.conormalSheaf j.liftCoborder.toLRSHom.toShHom))) z),
      ∀ a, ρ (stalkLinearMap (conormalSequenceLeftMap i j) z a) = a := by
  obtain ⟨V, hz, r, hr⟩ := hS.locallySplit z
  exact exists_stalkLinearMap_retraction (conormalSequenceLeftMap i j) z V hz r hr

/-! ### Injectivity of the map of cotangent fibres -/

/-- The module structure over the local ring of `X` at `j (i z)`, through the map of local rings
of two nested immersions `i : Z ⟶ Y` and `j : Y ⟶ X`, on the stalk at `z` of a sheaf of modules
on `Z`. -/
abbrev ambientStalkModule (i : Z ⟶ Y) (j : Y ⟶ X) (M : Z.Modules) (z : Z) :
    Module (X.presheaf.stalk (j (i z)))
      (ToType (TopCat.Presheaf.stalk (C := Ab.{u}) (Scheme.Modules.presheaf M) z)) :=
  letI := stalkModule M z
  Module.compHom _ (j.stalkMap (i z) ≫ i.stalkMap z).hom

attribute [local instance] ambientStalkModule

/-- **Injectivity of the map of cotangent fibres from a morphism of sheaves of modules with a
local retraction.** Let `i : Z ⟶ Y` and `j : Y ⟶ X` be immersions, let `x = j (i z)` and write
`I_x ⊆ J_x` for the stalks at `x` of the defining ideals of `j` and of `i ≫ j`.  Let `ψ : A ⟶ B`
be a morphism of sheaves of modules on `Z` whose restriction to a neighbourhood of `z` admits a
retraction, let `p : A_z ⟶ I_x / 𝔪_x I_x` be surjective and let `q : B_z ⟶ J_x / 𝔪_x J_x` have
kernel inside `𝔪_x B_z`.  If `p` and `q` carry the germ of `ψ` to the map of cotangent fibres,
then that map is injective.

Taking `ψ` to be the left-hand map `i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X}` of the conormal sequence of
[Stacks Project, Tag 062S] gives the final step of [Stacks Project, Tag 068Z]. -/
theorem injective_idealCotangentFiberMap_of_stalkRetraction (i : Z ⟶ Y) (j : Y ⟶ X) (z : Z)
    {A B : Z.Modules} (ψ : A ⟶ B) (V : Z.Opens) (hz : z ∈ V)
    (r : (Scheme.Modules.restrictFunctor V.ι).obj B ⟶
      (Scheme.Modules.restrictFunctor V.ι).obj A)
    (hr : (Scheme.Modules.restrictFunctor V.ι).map ψ ≫ r = 𝟙 _)
    (p : ToType (TopCat.Presheaf.stalk (C := Ab.{u}) A.presheaf z) →ₗ[
        X.presheaf.stalk (j (i z))]
      Stacks.RingedSpace.idealCotangentFiber (X := X.toLocallyRingedSpace)
        (definingIdealOfHom j) (j (i z)))
    (hp : Function.Surjective p)
    (q : ToType (TopCat.Presheaf.stalk (C := Ab.{u}) B.presheaf z) →ₗ[
        X.presheaf.stalk (j (i z))]
      Stacks.RingedSpace.idealCotangentFiber (X := X.toLocallyRingedSpace)
        (definingIdealOfHom (i ≫ j)) (j (i z)))
    (hq : ∀ ν : ToType (TopCat.Presheaf.stalk (C := Ab.{u}) B.presheaf z), q ν = 0 →
      ν ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (j (i z))) •
        (⊤ : Submodule (X.presheaf.stalk (j (i z)))
          (ToType (TopCat.Presheaf.stalk (C := Ab.{u}) B.presheaf z))))
    (hsq : ∀ (U : Z.Opens) (hU : z ∈ U) (s : Γ(A, U)),
      q (TopCat.Presheaf.germ (C := Ab.{u}) B.presheaf U z hU (ψ.app U s)) =
        idealCotangentFiberMap i j z
          (p (TopCat.Presheaf.germ (C := Ab.{u}) A.presheaf U z hU s))) :
    Function.Injective (idealCotangentFiberMap i j z) := by
  let _ := stalkModule A z
  let _ := stalkModule B z
  obtain ⟨ρ, hρ⟩ := exists_stalkLinearMap_retraction ψ z V hz r hr
  refine injective_idealCotangentFiberMap_of_split i j z
    (M := ToType (TopCat.Presheaf.stalk (C := Ab.{u}) A.presheaf z))
    (N := ToType (TopCat.Presheaf.stalk (C := Ab.{u}) B.presheaf z))
    { toFun := fun a => stalkLinearMap ψ z a
      map_add' := map_add (stalkLinearMap ψ z)
      map_smul' := fun c a =>
        (stalkLinearMap ψ z).map_smul ((j.stalkMap (i z) ≫ i.stalkMap z).hom c) a }
    { toFun := fun b => ρ b
      map_add' := map_add ρ
      map_smul' := fun c b => ρ.map_smul ((j.stalkMap (i z) ≫ i.stalkMap z).hom c) b }
    hρ p hp q hq fun μ => ?_
  obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq A.presheaf μ
  exact (congrArg (fun y => q y) (stalkHom_germ ψ z U hU s)).trans (hsq U hU s)

/-! ### Injectivity from the conormal classes of germs -/

/-- An additive and semilinear map carries `m • ⊤` into `m • ⊤`. -/
private theorem mem_smul_top_of_map_smul {R M N : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] {m : Ideal R} (c : M → N)
    (hadd : ∀ x y : M, c (x + y) = c x + c y)
    (hsmul : ∀ (s : R) (x : M), c (s • x) = s • c x) {a : M}
    (ha : a ∈ m • (⊤ : Submodule R M)) : c a ∈ m • (⊤ : Submodule R N) := by
  refine Submodule.smul_induction_on ha (fun s hs b _ => ?_) (fun b d hb hd => ?_)
  · rw [hsmul]
    exact Submodule.smul_mem_smul hs Submodule.mem_top
  · rw [hadd]
    exact Submodule.add_mem _ hb hd

/-- **Injectivity of the map of cotangent fibres from a local retraction and the conormal classes
of germs.** Let `i : Z ⟶ Y` and `j : Y ⟶ X` be immersions, let `x = j (i z)` and write
`I_x ⊆ J_x` for the stalks at `x` of the defining ideals of `j` and of `i ≫ j`.  Let `ψ : A ⟶ B`
be a morphism of sheaves of modules on `Z` whose restriction to a neighbourhood of `z` admits a
retraction, and let `cI : I_x ⟶ A_z` and `cJ : J_x ⟶ B_z` assign to a germ its conormal class,
`cJ` being additive and `𝒪_{X,x}`-semilinear and the two being intertwined by the stalk of `ψ`.
If an `𝒪_{X,x}`-linear `p : A_z ⟶ I_x / 𝔪_x I_x` returns the class of `a` from `cI a`, then the
map of cotangent fibres is injective.

Taking `ψ` to be the left-hand map `i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X}` of the conormal sequence of
[Stacks Project, Tag 062S] gives the final step of [Stacks Project, Tag 068Z]. -/
theorem injective_idealCotangentFiberMap_of_conormalClasses (i : Z ⟶ Y) (j : Y ⟶ X) (z : Z)
    {A B : Z.Modules} (ψ : A ⟶ B) (V : Z.Opens) (hz : z ∈ V)
    (r : (Scheme.Modules.restrictFunctor V.ι).obj B ⟶
      (Scheme.Modules.restrictFunctor V.ι).obj A)
    (hr : (Scheme.Modules.restrictFunctor V.ι).map ψ ≫ r = 𝟙 _)
    (cI : Stacks.RingedSpace.stalkIdeal (X := X.toLocallyRingedSpace)
        (definingIdealOfHom j) (j (i z)) →
      ToType (TopCat.Presheaf.stalk (C := Ab.{u}) A.presheaf z))
    (cJ : Stacks.RingedSpace.stalkIdeal (X := X.toLocallyRingedSpace)
        (definingIdealOfHom (i ≫ j)) (j (i z)) →
      ToType (TopCat.Presheaf.stalk (C := Ab.{u}) B.presheaf z))
    (hcJadd : ∀ b b', cJ (b + b') = cJ b + cJ b')
    (hcJsmul : ∀ (c : X.presheaf.stalk (j (i z))) (b), cJ (c • b) = c • cJ b)
    (hcomp : ∀ (a : Stacks.RingedSpace.stalkIdeal (X := X.toLocallyRingedSpace)
        (definingIdealOfHom j) (j (i z)))
      (ha : (a : X.presheaf.stalk (j (i z))) ∈
        Stacks.RingedSpace.stalkIdeal (X := X.toLocallyRingedSpace)
          (definingIdealOfHom (i ≫ j)) (j (i z))),
      stalkLinearMap ψ z (cI a) = cJ ⟨a, ha⟩)
    (p : ToType (TopCat.Presheaf.stalk (C := Ab.{u}) A.presheaf z)
      →ₗ[X.presheaf.stalk (j (i z))] Stacks.RingedSpace.idealCotangentFiber
        (X := X.toLocallyRingedSpace) (definingIdealOfHom j) (j (i z)))
    (hp : ∀ a, p (cI a) = Submodule.Quotient.mk a) :
    Function.Injective (idealCotangentFiberMap i j z) := by
  let _ := stalkModule A z
  let _ := stalkModule B z
  obtain ⟨ρ, hρ⟩ := exists_stalkLinearMap_retraction ψ z V hz r hr
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro ξ hξ
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
  rw [idealCotangentFiberMap_mk i j z a (stalkIdeal_le_comp i j z a.2),
    Submodule.Quotient.mk_eq_zero] at hξ
  have h1 := mem_smul_top_of_map_smul cJ hcJadd hcJsmul hξ
  have h2 := mem_smul_top_of_map_smul (⇑ρ) (map_add ρ)
    (fun s x => ρ.map_smul ((j.stalkMap (i z) ≫ i.stalkMap z).hom s) x) h1
  rw [← hcomp a (stalkIdeal_le_comp i j z a.2), hρ (cI a)] at h2
  rw [← hp a]
  exact apply_eq_zero_of_mem_smul_top p h2

end Stacks.AlgebraicGeometry

end

