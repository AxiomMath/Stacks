module

public import Mathlib.Topology.Sheaves.Sheafify
public import StacksFrontier.AlgebraicGeometry.SectionRingGeometric.GlobalSections

/-!
# Surjectivity on stalks, and multiplication by a global section

Let `X` be a scheme and `L` an `𝒪_X`-module. `Stacks.GradedSections.mulMap s m` is multiplication
by a section `s : 𝟙_ ⟶ L ^⊗ n`, read as a morphism of modules `L ^⊗ m ⟶ L ^⊗ (n + m)`: it is `s`
whiskered on the right by `m` copies of `L`. It is surjective on the stalk at `x` as soon as `s`
is.

## Main definitions

* `Stacks.SectionProduct.pgerm`, `Stacks.SectionProduct.pstalkHom`: the germ map and the induced
  map of stalks for a presheaf of modules on a scheme, both as bundled additive maps.
* `Stacks.SectionProduct.SurjStalk`: surjectivity of the stalk map of a morphism of
  `𝒪_X`-modules at a point.
* `Stacks.SectionProduct.hStruct`, `Stacks.SectionProduct.forgetFun`: the sheaf condition on the
  structure presheaf of rings, and the forgetful functor to presheaves of modules.

## Main results

* `Stacks.SectionProduct.pstalkHom_whiskerLeft_surjective`: tensoring on the left preserves
  surjectivity on stalks, at the presheaf level.
* `Stacks.SectionProduct.pstalkHom_toSheafify_bijective`: sheafification does not change stalks,
  for presheaves of modules.
* `Stacks.SectionProduct.SurjStalk.whiskerLeft`, `Stacks.SectionProduct.SurjStalk.whiskerRight`:
  the same for the monoidal structure on `SheafOfModules`.
* `Stacks.SectionProduct.surjStalk_mulMap`: multiplication by a section is surjective on the
  stalk wherever the section is.

## Implementation notes

* `TopCat.Presheaf.germ` is applied through `ConcreteCategory.hom` in Mathlib's lemmas and
  through `AddCommGrpCat.Hom.hom` when written with dot notation. The two spellings are
  definitionally but not syntactically equal, so `rw` with a germ lemma can fail with "did not
  find an occurrence". The lemmas below are stated through the bundled `pgerm`, and
  `exists_pgerm_eq`, `pgerm_res`, `pgerm_eq_exists` and `pstalkHom_pgerm` are the only places
  where the two spellings meet.
* `A.map i.op a` has type `(ModuleCat.restrictScalars _).obj (A.obj _)`, so a tactic step that
  mentions `A.map i.op a ⊗ₜ P.map i.op p` reports a spurious application type mismatch. Such
  steps are stated as the lemmas `pgerm_tmul_res` and `pstalkHom_whiskerLeft_pgerm_tmul`, which
  are applied with the tensor factors left as placeholders.
* `PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app` needs its morphism
  argument `𝟙 (structureSheaf X.presheaf (hStruct X)).obj` explicitly, since neither
  `Stacks.SheafOfModules.TensorSheafification.toSheafify` nor
  `Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction` unfolds for instance search.
* `SurjStalk.whiskerRight` takes the morphism before the object, so `h.whiskerRight L` puts `L`
  in the morphism slot and fails with a deterministic timeout at `whnf` rather than a type
  error; its arguments are given positionally.

## References

* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public section

open CategoryTheory Category AlgebraicGeometry Opposite MonoidalCategory
  Stacks.SheafOfModules.TensorSheafification
open TopologicalSpace
open scoped TensorProduct

universe u

namespace Stacks.SectionProduct

variable {X : Scheme.{u}}

/-- The sheaf condition on the structure presheaf of rings of a scheme. -/
abbrev hStruct (X : Scheme.{u}) : Presheaf.IsSheaf (Opens.grothendieckTopology ↥X)
    (structureRingPresheaf X.presheaf) :=
  Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X

/-! ### Germs and stalk maps for presheaves of modules -/

/-- The germ at `x` of a presheaf of modules on a scheme, as an additive map. -/
noncomputable def pgerm (P : PresheafOfModulesOfCommRing.{u} X.presheaf) (U : X.Opens) (x : X)
    (hx : x ∈ U) : P.obj (op U) →+ TopCat.Presheaf.stalk (C := Ab.{u}) P.presheaf x :=
  (TopCat.Presheaf.germ (C := Ab.{u}) P.presheaf U x hx).hom

/-- The map of stalks induced by a morphism of presheaves of modules, as an additive map. -/
noncomputable def pstalkHom {P Q : PresheafOfModulesOfCommRing.{u} X.presheaf} (φ : P ⟶ Q)
    (x : X) :
    TopCat.Presheaf.stalk (C := Ab.{u}) P.presheaf x →+
      TopCat.Presheaf.stalk (C := Ab.{u}) Q.presheaf x :=
  ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
    ((PresheafOfModules.toPresheaf (structureRingPresheaf X.presheaf)).map φ)).hom

/-- The stalk map of `φ` sends the germ of a section `t` to the germ of `φ.app (op U) t`. -/
theorem pstalkHom_pgerm {P Q : PresheafOfModulesOfCommRing.{u} X.presheaf} (φ : P ⟶ Q) (x : X)
    (U : X.Opens) (hx : x ∈ U) (t : P.obj (op U)) :
    pstalkHom φ x (pgerm P U x hx t) = pgerm Q U x hx (φ.app (op U) t) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
    ((PresheafOfModules.toPresheaf (structureRingPresheaf X.presheaf)).map φ) t

/-- Every element of a stalk of a presheaf of modules is the germ of a section. -/
theorem exists_pgerm_eq (P : PresheafOfModulesOfCommRing.{u} X.presheaf) {x : X}
    (z : TopCat.Presheaf.stalk (C := Ab.{u}) P.presheaf x) :
    ∃ (U : X.Opens) (hx : x ∈ U) (t : P.obj (op U)), pgerm P U x hx t = z := by
  obtain ⟨U, hx, t, ht⟩ := TopCat.Presheaf.exists_germ_eq (C := Ab.{u}) P.presheaf z
  exact ⟨U, hx, t, ht⟩

/-- The germ of a restricted section is the germ of the section. -/
theorem pgerm_res (P : PresheafOfModulesOfCommRing.{u} X.presheaf) {U V : X.Opens} (i : U ⟶ V)
    (x : X) (hx : x ∈ U) (s : P.obj (op V)) :
    pgerm P U x hx (P.map i.op s) = pgerm P V x (leOfHom i hx) s :=
  TopCat.Presheaf.germ_res_apply (C := Ab.{u}) P.presheaf i x hx s

/-- Two sections with the same germ at `x` agree after restriction to some open neighbourhood of
`x`. -/
theorem pgerm_eq_exists (P : PresheafOfModulesOfCommRing.{u} X.presheaf) (x : X) {U V : X.Opens}
    (hU : x ∈ U) (hV : x ∈ V) (s : P.obj (op U)) (t : P.obj (op V))
    (h : pgerm P U x hU s = pgerm P V x hV t) :
    ∃ (W : X.Opens) (_ : x ∈ W) (iU : W ⟶ U) (iV : W ⟶ V), P.map iU.op s = P.map iV.op t := by
  obtain ⟨W, hW, iU, iV, he⟩ := TopCat.Presheaf.germ_eq (C := Ab.{u}) P.presheaf x hU hV s t h
  exact ⟨W, hW, iU, iV, he⟩

/-- The stalk map of a composite is the composite of the stalk maps. -/
theorem pstalkHom_comp {P Q R : PresheafOfModulesOfCommRing.{u} X.presheaf} (φ : P ⟶ Q)
    (ψ : Q ⟶ R) (x : X) (m : TopCat.Presheaf.stalk (C := Ab.{u}) P.presheaf x) :
    pstalkHom (φ ≫ ψ) x m = pstalkHom ψ x (pstalkHom φ x m) := by
  obtain ⟨U, hx, t, rfl⟩ := exists_pgerm_eq P m
  rw [pstalkHom_pgerm, pstalkHom_pgerm, pstalkHom_pgerm]
  rfl

/-- The stalk map of the identity is the identity. -/
theorem pstalkHom_id (P : PresheafOfModulesOfCommRing.{u} X.presheaf) (x : X)
    (m : TopCat.Presheaf.stalk (C := Ab.{u}) P.presheaf x) : pstalkHom (𝟙 P) x m = m := by
  obtain ⟨U, hx, t, rfl⟩ := exists_pgerm_eq P m
  rw [pstalkHom_pgerm]
  rfl

/-- A morphism of presheaves of modules that is an isomorphism is bijective on stalks. -/
theorem pstalkHom_bijective_of_isIso {P Q : PresheafOfModulesOfCommRing.{u} X.presheaf}
    (φ : P ⟶ Q) [IsIso φ] (x : X) : Function.Bijective (pstalkHom φ x) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨pstalkHom (inv φ) x, fun m => ?_, fun m => ?_⟩
  · rw [← pstalkHom_comp, IsIso.hom_inv_id, pstalkHom_id]
  · rw [← pstalkHom_comp, IsIso.inv_hom_id, pstalkHom_id]

/-! ### Whiskering a presheaf morphism preserves surjectivity on stalks -/

/-- The germ of an elementary tensor of restricted sections is the germ of the elementary tensor of
the sections. -/
theorem pgerm_tmul_res (A Q : PresheafOfModulesOfCommRing.{u} X.presheaf) {U W : X.Opens}
    (i : W ⟶ U) (x : X) (hxW : x ∈ W) (a : A.obj (op U)) (q : Q.obj (op U)) :
    pgerm (PresheafOfModules.tensorObj A Q) W x hxW
        (A.map i.op a ⊗ₜ[(structureRingPresheaf X.presheaf).obj (op W)] Q.map i.op q) =
      pgerm (PresheafOfModules.tensorObj A Q) U x (leOfHom i hxW)
        (a ⊗ₜ[(structureRingPresheaf X.presheaf).obj (op U)] q) :=
  pgerm_res (PresheafOfModules.tensorObj A Q) i x hxW
    (a ⊗ₜ[(structureRingPresheaf X.presheaf).obj (op U)] q)

/-- The stalk map of `PresheafOfModules.tensorHom (𝟙 A) φ` on the germ of `a ⊗ₜ p` is the germ of
`a ⊗ₜ φ.app (op W) p`. -/
theorem pstalkHom_whiskerLeft_pgerm_tmul (A : PresheafOfModulesOfCommRing.{u} X.presheaf)
    {P Q : PresheafOfModulesOfCommRing.{u} X.presheaf} (φ : P ⟶ Q) (x : X) (W : X.Opens)
    (hxW : x ∈ W) (a : A.obj (op W)) (p : P.obj (op W)) :
    pstalkHom (PresheafOfModules.tensorHom (𝟙 A) φ) x
        (pgerm (PresheafOfModules.tensorObj A P) W x hxW
          (a ⊗ₜ[(structureRingPresheaf X.presheaf).obj (op W)] p)) =
      pgerm (PresheafOfModules.tensorObj A Q) W x hxW
        (a ⊗ₜ[(structureRingPresheaf X.presheaf).obj (op W)] φ.app (op W) p) :=
  pstalkHom_pgerm (PresheafOfModules.tensorHom (𝟙 A) φ) x W hxW _

/-- **Tensoring on the left preserves surjectivity on stalks, at the presheaf level.** -/
theorem pstalkHom_whiskerLeft_surjective (A : PresheafOfModulesOfCommRing.{u} X.presheaf)
    {P Q : PresheafOfModulesOfCommRing.{u} X.presheaf} (φ : P ⟶ Q) (x : X)
    (h : Function.Surjective (pstalkHom φ x)) :
    Function.Surjective (pstalkHom (PresheafOfModules.tensorHom (𝟙 A) φ) x) := by
  intro z
  obtain ⟨U, hxU, w, rfl⟩ := exists_pgerm_eq (PresheafOfModules.tensorObj A Q) z
  rw [← AddMonoidHom.mem_range]
  induction w using TensorProduct.induction_on with
  | zero => exact (map_zero (pgerm (PresheafOfModules.tensorObj A Q) U x hxU)) ▸ zero_mem _
  | tmul a q =>
    obtain ⟨ξ, hξ⟩ := h (pgerm Q U x hxU q)
    obtain ⟨U₁, hxU₁, p, rfl⟩ := exists_pgerm_eq P ξ
    obtain ⟨W, hxW, i₁, i₂, heq⟩ := pgerm_eq_exists Q x hxU₁ hxU (φ.app (op U₁) p) q
      ((pstalkHom_pgerm φ x U₁ hxU₁ p).symm.trans hξ)
    refine ⟨pgerm (PresheafOfModules.tensorObj A P) W x hxW
      (A.map i₂.op a ⊗ₜ[(structureRingPresheaf X.presheaf).obj (op W)] P.map i₁.op p), ?_⟩
    refine (pstalkHom_whiskerLeft_pgerm_tmul A φ x W hxW _ _).trans ?_
    refine Eq.trans (congrArg (fun z => pgerm (PresheafOfModules.tensorObj A Q) W x hxW
      (A.map i₂.op a ⊗ₜ[(structureRingPresheaf X.presheaf).obj (op W)] z)) ?_)
      (pgerm_tmul_res A Q i₂ x hxW a q)
    exact (PresheafOfModules.naturality_apply φ i₁.op p).trans heq
  | add w w' hw hw' =>
    exact (map_add (pgerm (PresheafOfModules.tensorObj A Q) U x hxU) w w') ▸ add_mem hw hw'

/-! ### Sheafification does not change stalks -/

/-- **The sheafification unit is bijective on stalks.** -/
theorem pstalkHom_toSheafify_bijective (P : PresheafOfModulesOfCommRing.{u} X.presheaf) (x : X) :
    Function.Bijective (pstalkHom (toSheafify X.presheaf (hStruct X) P) x) := by
  have h1 : (PresheafOfModules.toPresheaf (structureRingPresheaf X.presheaf)).map
      (toSheafify X.presheaf (hStruct X) P) =
      CategoryTheory.toSheafify (Opens.grothendieckTopology ↥X) P.presheaf :=
    PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app
      (𝟙 (structureSheaf X.presheaf (hStruct X)).obj) P
  have hiso : IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
      ((PresheafOfModules.toPresheaf (structureRingPresheaf X.presheaf)).map
        (toSheafify X.presheaf (hStruct X) P))) := by
    rw [h1]
    exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x Ab.{u} P.presheaf
  exact ConcreteCategory.bijective_of_isIso _

/-- The underlying presheaf of modules of a sheaf of modules on a scheme, as a functor. -/
noncomputable abbrev forgetFun (X : Scheme.{u}) :
    SheafOfModules.{u} (structureSheaf X.presheaf (hStruct X)) ⥤
      PresheafOfModules.{u} (structureSheaf X.presheaf (hStruct X)).obj :=
  SheafOfModules.forget (structureSheaf X.presheaf (hStruct X)) ⋙
    PresheafOfModules.restrictScalars (𝟙 (structureSheaf X.presheaf (hStruct X)).obj)

/-- **Sheafification preserves surjectivity on stalks.** -/
theorem surjective_pstalkHom_sheafify_map
    {P Q : PresheafOfModulesOfCommRing.{u} X.presheaf} (φ : P ⟶ Q) (x : X)
    (h : Function.Surjective (pstalkHom φ x)) :
    Function.Surjective
      (pstalkHom ((forgetFun X).map ((sheafify X.presheaf (hStruct X)).map φ)) x) := by
  have hnat : φ ≫ toSheafify X.presheaf (hStruct X) Q =
      toSheafify X.presheaf (hStruct X) P ≫
        (forgetFun X).map ((sheafify X.presheaf (hStruct X)).map φ) :=
    (sheafifyAdjunction X.presheaf (hStruct X)).unit.naturality φ
  intro z
  obtain ⟨w, hw⟩ := (pstalkHom_toSheafify_bijective Q x).2 z
  obtain ⟨v, hv⟩ := h w
  refine ⟨pstalkHom (toSheafify X.presheaf (hStruct X) P) x v, ?_⟩
  have e := congrArg
    (fun ψ : P ⟶ (forgetFun X).obj ((sheafify X.presheaf (hStruct X)).obj Q) =>
      pstalkHom ψ x v) hnat
  have l := pstalkHom_comp φ (toSheafify X.presheaf (hStruct X) Q) x v
  have r := pstalkHom_comp (toSheafify X.presheaf (hStruct X) P)
    ((forgetFun X).map ((sheafify X.presheaf (hStruct X)).map φ)) x v
  rw [← r, ← e, l, hv, hw]

/-! ### Surjectivity on stalks for modules on a scheme -/

section SheafLevel

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-- The stalk map of a morphism of `𝒪_X`-modules is the stalk map of the underlying morphism of
presheaves of modules. -/
theorem mapFun_eq_pstalkHom {M N : X.Modules} (φ : M ⟶ N) (x : X)
    (m : TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x) :
    Stacks.ModuleStalk.mapFun φ x m = pstalkHom ((forgetFun X).map φ) x m := rfl

/-- **Surjectivity of the stalk map at a point**, for a morphism of `𝒪_X`-modules. -/
def SurjStalk {M N : X.Modules} (φ : M ⟶ N) (x : X) : Prop :=
  Function.Surjective (Stacks.ModuleStalk.mapFun φ x)

/-- An isomorphism of `𝒪_X`-modules is bijective on stalks. -/
theorem mapFun_bijective_of_isIso {M N : X.Modules} (φ : M ⟶ N) [IsIso φ] (x : X) :
    Function.Bijective (Stacks.ModuleStalk.mapFun φ x) :=
  Function.bijective_iff_has_inverse.mpr ⟨Stacks.ModuleStalk.mapFun (inv φ) x,
    fun _ => by
      rw [← Stacks.ModuleStalk.mapFun_comp, IsIso.hom_inv_id, Stacks.ModuleStalk.mapFun_id],
    fun _ => by
      rw [← Stacks.ModuleStalk.mapFun_comp, IsIso.inv_hom_id, Stacks.ModuleStalk.mapFun_id]⟩

/-- A morphism `e` with `e' ≫ e = 𝟙 N` is surjective on stalks. -/
theorem surjStalk_of_inv {M N : X.Modules} {e : M ⟶ N} {e' : N ⟶ M} (he : e' ≫ e = 𝟙 N)
    (x : X) : SurjStalk e x := fun z =>
  ⟨Stacks.ModuleStalk.mapFun e' x z, by
    rw [← Stacks.ModuleStalk.mapFun_comp, he, Stacks.ModuleStalk.mapFun_id]⟩

/-- A composite of morphisms that are surjective on stalks is surjective on stalks. -/
theorem SurjStalk.comp {M N K : X.Modules} {φ : M ⟶ N} {ψ : N ⟶ K} {x : X}
    (hφ : SurjStalk φ x) (hψ : SurjStalk ψ x) : SurjStalk (φ ≫ ψ) x := by
  intro z
  obtain ⟨w, hw⟩ := hψ z
  obtain ⟨v, hv⟩ := hφ w
  exact ⟨v, by rw [Stacks.ModuleStalk.mapFun_comp, hv, hw]⟩

/-- If `φ ≫ e` is surjective on stalks at `x` and `e ≫ e' = 𝟙 N`, then `φ` is surjective on stalks
at `x`. -/
theorem SurjStalk.of_comp_right {M N K : X.Modules} (φ : M ⟶ N) {e : N ⟶ K} {e' : K ⟶ N}
    (he : e ≫ e' = 𝟙 N) {x : X} (h : SurjStalk (φ ≫ e) x) : SurjStalk φ x := by
  have hinj : Function.Injective (Stacks.ModuleStalk.mapFun e x) :=
    Function.LeftInverse.injective (g := Stacks.ModuleStalk.mapFun e' x) fun a => by
      rw [← Stacks.ModuleStalk.mapFun_comp, he, Stacks.ModuleStalk.mapFun_id]
  intro z
  obtain ⟨v, hv⟩ := h (Stacks.ModuleStalk.mapFun e x z)
  rw [Stacks.ModuleStalk.mapFun_comp] at hv
  exact ⟨v, hinj hv⟩

/-- If `e ≫ ψ` is surjective on stalks at `x`, then so is `ψ`. -/
theorem SurjStalk.of_comp_left {M N K : X.Modules} {e : M ⟶ N} (ψ : N ⟶ K) {x : X}
    (h : SurjStalk (e ≫ ψ) x) : SurjStalk ψ x := by
  intro z
  obtain ⟨v, hv⟩ := h z
  exact ⟨Stacks.ModuleStalk.mapFun e x v, by
    rw [← Stacks.ModuleStalk.mapFun_comp]; exact hv⟩

/-- Surjectivity on stalks transfers along an equality of morphisms. -/
theorem surjStalk_congr {M N : X.Modules} {φ ψ : M ⟶ N} (h : φ = ψ) {x : X}
    (hφ : SurjStalk φ x) : SurjStalk ψ x := h ▸ hφ

/-- **Sheafification preserves surjectivity on stalks**, in the `Scheme.Modules` spelling. -/
theorem surjStalk_sheafify_map {P Q : PresheafOfModulesOfCommRing.{u} X.presheaf} (φ : P ⟶ Q)
    (x : X) (h : Function.Surjective (pstalkHom φ x)) :
    SurjStalk (M := (sheafify X.presheaf (hStruct X)).obj P)
      (N := (sheafify X.presheaf (hStruct X)).obj Q)
      ((sheafify X.presheaf (hStruct X)).map φ) x :=
  surjective_pstalkHom_sheafify_map φ x h

/-- **Tensoring on the left preserves surjectivity on stalks.** -/
theorem SurjStalk.whiskerLeft (A : X.Modules) {M N : X.Modules} (f : M ⟶ N) {x : X}
    (h : SurjStalk f x) : SurjStalk (A ◁ f) x := by
  set e := Stacks.SheafInternalHom.tensorLeftIso X.presheaf (hStruct X) A with he
  refine SurjStalk.of_comp_right _ (e.hom_inv_id_app N) ?_
  refine surjStalk_congr (e.hom.naturality f).symm ?_
  exact (surjStalk_of_inv (e.inv_hom_id_app M) x).comp
    (surjStalk_sheafify_map (PresheafOfModules.tensorHom (𝟙 A.val) f.val) x
      (pstalkHom_whiskerLeft_surjective A.val f.val x h))

/-- **Tensoring on the right preserves surjectivity on stalks.** -/
theorem SurjStalk.whiskerRight {M N : X.Modules} (f : M ⟶ N) (A : X.Modules) {x : X}
    (h : SurjStalk f x) : SurjStalk (f ▷ A) x := by
  have hb : A ◁ f = (β_ A M).hom ≫ (f ▷ A) ≫ (β_ A N).inv := by
    rw [← Category.assoc, ← BraidedCategory.braiding_naturality_right A f,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact SurjStalk.of_comp_right _ (β_ A N).inv_hom_id
    (SurjStalk.of_comp_left _ (surjStalk_congr hb (h.whiskerLeft A)))

end SheafLevel

/-! ### Multiplication by a section -/

section MulMap

attribute [local instance] Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

/-- **Multiplication by a section is surjective on the stalk at every point where the section
is.** -/
theorem surjStalk_mulMap (L : X.Modules) (n : ℕ) (s : Stacks.GradedSections.powSections L n)
    (x : X) (h : SurjStalk s x) (m : ℕ) :
    SurjStalk (Stacks.GradedSections.mulMap s m) x := by
  induction m with
  | zero => exact h
  | succ m ih => exact SurjStalk.whiskerRight (Stacks.GradedSections.mulMap s m) L ih

end MulMap

end Stacks.SectionProduct

end
