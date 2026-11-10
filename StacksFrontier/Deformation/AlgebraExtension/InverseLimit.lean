module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksFrontier.Deformation.AlgebraExtension.InducedKernelMap

/-!
# The inverse limit of a tower of extensions

Let `F : ℕᵒᵖ ⥤ Sheaf J CommRingCat` be a tower of sheaves of rings with a cone `ρ : F ⟶ const 𝒪`
of reductions, and suppose that each `ρₙ : Fₙ ⟶ 𝒪` is, up to an isomorphism `Fₙ ≅ 𝒪'ₙ` over `𝒪`,
the reduction of an extension `Pₙ` of `𝒪` by an `𝒪`-module `ℳₙ`
(`Deformation.AlgebraExtension`). The transitions `F_{n+1} ⟶ Fₙ` then induce maps of ideals
`ℳ_{n+1} ⟶ ℳₙ` (`Deformation.AlgebraExtension.inducedKernelMap`), and the kernel of the reduction
`lim Fₙ ⟶ F₀ ⟶ 𝒪` is, section by section, the inverse limit `lim ℳₙ` of the ideals.

This is the identification `Ker(lim 𝒪_{Xₙ} → 𝒪_{X₁}) = lim 𝒪_{X₁} ⊗ Iₙ` of the body of the proof
of [Stacks Project, Tag 0D3X]: sections of an inverse limit of sheaves are compatible families of
sections, and the kernel of a limit of maps is the limit of the kernels.

## Main definitions

* `Deformation.AlgebraExtension.InverseLimit.idealSystem`: the tower `n ↦ ℳₙ` of ideals.
* `Deformation.AlgebraExtension.InverseLimit.kernelInclusion`: the inclusion `lim ℳₙ ⟶ lim Fₙ`,
  linear over `lim Fₙ` acting on `lim ℳₙ` through the reduction.

## Main results

* `Deformation.AlgebraExtension.InverseLimit.kernelZero` and
  `Deformation.AlgebraExtension.InverseLimit.kernelUniversal`: `lim ℳₙ` is exactly the kernel of
  the reduction `lim Fₙ ⟶ 𝒪`, uniquely, on every section.
* `CategoryTheory.Functor.map_eq_of_map_succ`: a family over `ℕᵒᵖ` compatible with the successor
  transitions is compatible with all transitions.

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace CategoryTheory.Functor

/-- **A family over `ℕᵒᵖ` compatible with the successor transitions is a section.** For a functor
`G : ℕᵒᵖ ⥤ Type _` and `x n ∈ G(n)` with `G(n + 1 ⟶ n)(x (n + 1)) = x n`, every transition
carries `x j` to `x i`. -/
theorem map_eq_of_map_succ {G : ℕᵒᵖ ⥤ Type*} (x : ∀ n : ℕ, G.obj (op n))
    (hx : ∀ n : ℕ, G.map (homOfLE (Nat.le_succ n)).op (x (n + 1)) = x n) {i j : ℕ}
    (h : i ≤ j) : G.map (homOfLE h).op (x j) = x i := by
  induction j, h using Nat.le_induction with
  | base =>
    rw [show ∀ h : i ≤ i, (homOfLE h).op = 𝟙 (op i) from fun _ => Subsingleton.elim _ _,
      G.map_id, types_id_apply]
  | succ j hij ih =>
    have hc : (homOfLE (hij.trans (Nat.le_succ j))).op =
        (homOfLE (Nat.le_succ j)).op ≫ (homOfLE hij).op := Subsingleton.elim _ _
    rw [hc, G.map_comp, types_comp_apply, hx, ih]

/-- The section of `G : ℕᵒᵖ ⥤ Type _` given by a family compatible with the successor
transitions. -/
def sectionOfMapSucc {G : ℕᵒᵖ ⥤ Type*} (x : ∀ n : ℕ, G.obj (op n))
    (hx : ∀ n : ℕ, G.map (homOfLE (Nat.le_succ n)).op (x (n + 1)) = x n) : G.sections :=
  ⟨fun n => x n.unop, fun {n m} f => by
    obtain ⟨n⟩ := n
    obtain ⟨m⟩ := m
    have hf : f = (homOfLE (leOfHom f.unop)).op := Subsingleton.elim _ _
    rw [hf]
    exact map_eq_of_map_succ x hx _⟩

end CategoryTheory.Functor

namespace Deformation.AlgebraExtension.InverseLimit

/-- Equal morphisms of sheaves of rings agree on sections. -/
private theorem hom_app_congr {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    {X Y : Sheaf J CommRingCat.{u}} {f g : X ⟶ Y} (h : f = g) (U : Cᵒᵖ) (x : X.obj.obj U) :
    f.hom.app U x = g.hom.app U x :=
  congrArg (fun k : X ⟶ Y => k.hom.app U x) h

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {O : Sheaf J CommRingCat.{u}} (F : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{u})
  (ρ : F ⟶ (Functor.const _).obj O)
  {A : ℕ → Sheaf J CommRingCat.{u}} {a : ∀ n, A n ⟶ O}
  {M : ℕ → SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)}
  (P : ∀ n, AlgebraExtension (a n) (M n)) (e : ∀ n, F.obj (op n) ≅ (P n).extension)
  (he : ∀ n, (e n).hom ≫ (P n).reduction = ρ.app (op n))

/-- The transition `F_{n+1} ⟶ Fₙ` read on the middle terms. -/
abbrev transition (n : ℕ) : (P (n + 1)).extension ⟶ (P n).extension :=
  (e (n + 1)).inv ≫ F.map (homOfLE (Nat.le_succ n)).op ≫ (e n).hom

include he in
/-- The transition `F_{n+1} ⟶ Fₙ`, read on the middle terms, is compatible with the reductions
to `𝒪`. -/
theorem transition_reduction (n : ℕ) :
    transition F P e n ≫ (P n).reduction = (P (n + 1)).reduction := by
  rw [Category.assoc, Category.assoc, he, Iso.inv_comp_eq, he]
  exact (ρ.naturality (homOfLE (Nat.le_succ n)).op).trans (Category.comp_id _)

/-- **The tower `n ↦ ℳₙ` of ideals**, with the transitions induced by those of `F`. -/
def idealSystem :
    ℕᵒᵖ ⥤ SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O) :=
  Functor.ofOpSequence (X := M) fun n =>
    inducedKernelMap (P (n + 1)) (P n) (transition F P e n) (transition_reduction F ρ P e he n)

/-- The successor transition of the tower of ideals is the induced kernel map. -/
theorem idealSystem_map_succ (n : ℕ) :
    (idealSystem F ρ P e he).map (homOfLE (Nat.le_succ n)).op =
      inducedKernelMap (P (n + 1)) (P n) (transition F P e n)
        (transition_reduction F ρ P e he n) :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

variable [HasLimit F]

/-- The reduction `lim Fₙ ⟶ F₀ ⟶ 𝒪`. -/
abbrev reduction : limit F ⟶ O := limit.π F (op 0) ≫ ρ.app (op 0)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The reduction factors through every `Fₙ`. -/
theorem π_comp_ρ (n : ℕ) : limit.π F (op n) ≫ ρ.app (op n) = reduction F ρ := by
  rw [reduction, ← limit.w F (homOfLE (Nat.zero_le n)).op, Category.assoc, ρ.naturality]
  simp

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- An isomorphism of sheaves of rings followed by its inverse is the identity on sections. -/
theorem hom_app_inv_app {X Y : Sheaf J CommRingCat.{u}} (g : X ≅ Y) (U : Cᵒᵖ) (y : Y.obj.obj U) :
    g.hom.hom.app U (g.inv.hom.app U y) = y :=
  hom_app_congr g.inv_hom_id U y

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- An isomorphism of sheaves of rings preceded by its inverse is the identity on sections. -/
theorem inv_app_hom_app {X Y : Sheaf J CommRingCat.{u}} (g : X ≅ Y) (U : Cᵒᵖ) (x : X.obj.obj U) :
    g.inv.hom.app U (g.hom.hom.app U x) = x :=
  hom_app_congr g.hom_inv_id U x

variable (U : Cᵒᵖ)

/-- Sections of `lim Fₙ` over `U` are the compatible families of sections. -/
def ringIsLimit : IsLimit ((forget CommRingCat.{u}).mapCone
    (((evaluation _ CommRingCat.{u}).obj U).mapCone
      ((sheafToPresheaf J CommRingCat.{u}).mapCone (limit.cone F)))) :=
  isLimitOfPreserves _ (isLimitOfPreserves _ (isLimitOfPreserves _ (limit.isLimit F)))

omit [HasLimit F] in
/-- Sections of `lim ℳₙ` over `U` are the compatible families of sections. -/
def idealIsLimit : IsLimit ((CategoryTheory.forget (ModuleCat.{u} _)).mapCone
    ((SheafOfModules.evaluation _ U).mapCone (limit.cone (idealSystem F ρ P e he)))) :=
  isLimitOfPreserves _ (isLimitOfPreserves _ (limit.isLimit _))

omit [HasLimit F] in
/-- The component in `ℳₙ` of a section of `lim ℳₙ`. -/
abbrev idealComponent (n : ℕ) (s : (limit (idealSystem F ρ P e he)).val.obj U) : (M n).val.obj U :=
  (limit.π (idealSystem F ρ P e he) (op n)).val.app U s

omit [HasLimit F] in
/-- The section of `Fₙ` attached to a section of `lim ℳₙ`: its component in `ℳₙ`, included in
`𝒪'ₙ ≅ Fₙ`. -/
abbrev ringComponent (n : ℕ) (s : (limit (idealSystem F ρ P e he)).val.obj U) :
    (F.obj (op n)).obj.obj U :=
  (e n).inv.hom.app U ((P n).incl (idealComponent F ρ P e he U n s))

omit [HasLimit F] in
/-- The components in `ℳₙ` of a section of `lim ℳₙ` are compatible with the induced kernel
maps. -/
theorem idealComponent_succ (n : ℕ) (s : (limit (idealSystem F ρ P e he)).val.obj U) :
    inducedKernelSection (P (n + 1)) (P n) (transition F P e n)
        (transition_reduction F ρ P e he n) (idealComponent F ρ P e he U (n + 1) s) =
      idealComponent F ρ P e he U n s := by
  have h := congrArg (fun k => k.val.app U s)
    (limit.w (idealSystem F ρ P e he) (homOfLE (Nat.le_succ n)).op)
  rwa [idealSystem_map_succ] at h

omit [HasLimit F] in
/-- The sections of `Fₙ` attached to a section of `lim ℳₙ` are compatible with the transitions
of `F`. -/
theorem ringComponent_succ (n : ℕ) (s : (limit (idealSystem F ρ P e he)).val.obj U) :
    (F.map (homOfLE (Nat.le_succ n)).op).hom.app U (ringComponent F ρ P e he U (n + 1) s) =
      ringComponent F ρ P e he U n s := by
  have h := incl_inducedKernelSection (P (n + 1)) (P n) (transition F P e n)
    (transition_reduction F ρ P e he n) (idealComponent F ρ P e he U (n + 1) s)
  rw [idealComponent_succ] at h
  refine Eq.trans ?_ (congrArg ((e n).inv.hom.app U) h).symm
  exact (hom_app_congr (e n).hom_inv_id U _).symm

/-- The section of `lim Fₙ` given by a family of sections compatible with the successor
transitions. -/
def ringSection (x : ∀ n : ℕ, (F.obj (op n)).obj.obj U)
    (hx : ∀ n : ℕ, (F.map (homOfLE (Nat.le_succ n)).op).hom.app U (x (n + 1)) = x n) :
    (limit F).obj.obj U :=
  (Types.isLimitEquivSections (ringIsLimit F U)).symm
    (Functor.sectionOfMapSucc (G := ((F ⋙ sheafToPresheaf J CommRingCat.{u}) ⋙
      (evaluation _ CommRingCat.{u}).obj U) ⋙ forget CommRingCat.{u}) x hx)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The component in `Fₙ` of `ringSection F U x hx` is `x n`. -/
theorem π_ringSection (x : ∀ n : ℕ, (F.obj (op n)).obj.obj U)
    (hx : ∀ n : ℕ, (F.map (homOfLE (Nat.le_succ n)).op).hom.app U (x (n + 1)) = x n) (n : ℕ) :
    (limit.π F (op n)).hom.app U (ringSection F U x hx) = x n :=
  Types.isLimitEquivSections_symm_apply (ringIsLimit F U) _ (op n)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Two sections of `lim Fₙ` with the same components in every `Fₙ` are equal. -/
theorem ringSection_ext {y z : (limit F).obj.obj U}
    (h : ∀ n : ℕ, (limit.π F (op n)).hom.app U y = (limit.π F (op n)).hom.app U z) : y = z :=
  (Types.isLimitEquivSections (ringIsLimit F U)).injective (Subtype.ext (funext fun n => h n.unop))

omit [HasLimit F] in
/-- The section of `lim ℳₙ` given by a family of sections compatible with the successor
transitions. -/
def idealSection (m : ∀ n : ℕ, (M n).val.obj U)
    (hm : ∀ n : ℕ, inducedKernelSection (P (n + 1)) (P n) (transition F P e n)
      (transition_reduction F ρ P e he n) (m (n + 1)) = m n) :
    (limit (idealSystem F ρ P e he)).val.obj U :=
  (Types.isLimitEquivSections (idealIsLimit F ρ P e he U)).symm
    (Functor.sectionOfMapSucc (G := (idealSystem F ρ P e he ⋙ SheafOfModules.evaluation _ U) ⋙
      CategoryTheory.forget (ModuleCat.{u} _)) m fun n => by
        change ((idealSystem F ρ P e he).map (homOfLE (Nat.le_succ n)).op).val.app U _ = _
        rw [idealSystem_map_succ]
        exact hm n)

omit [HasLimit F] in
/-- The component in `ℳₙ` of `idealSection F ρ P e he U m hm` is `m n`. -/
theorem idealComponent_idealSection (m : ∀ n : ℕ, (M n).val.obj U)
    (hm : ∀ n : ℕ, inducedKernelSection (P (n + 1)) (P n) (transition F P e n)
      (transition_reduction F ρ P e he n) (m (n + 1)) = m n) (n : ℕ) :
    idealComponent F ρ P e he U n (idealSection F ρ P e he U m hm) = m n :=
  Types.isLimitEquivSections_symm_apply (idealIsLimit F ρ P e he U) _ (op n)

omit [HasLimit F] in
/-- Two sections of `lim ℳₙ` with the same components in every `ℳₙ` are equal. -/
theorem idealSection_ext {s t : (limit (idealSystem F ρ P e he)).val.obj U}
    (h : ∀ n : ℕ, idealComponent F ρ P e he U n s = idealComponent F ρ P e he U n t) : s = t :=
  (Types.isLimitEquivSections (idealIsLimit F ρ P e he U)).injective
    (Subtype.ext (funext fun n => h n.unop))

/-- **The inclusion of `lim ℳₙ` into `lim Fₙ`, on sections.** -/
def kernelSection (s : (limit (idealSystem F ρ P e he)).val.obj U) : (limit F).obj.obj U :=
  ringSection F U (fun n => ringComponent F ρ P e he U n s)
    (fun n => ringComponent_succ F ρ P e he U n s)

/-- The component in `Fₙ` of the inclusion of a section of `lim ℳₙ` is its section of `Fₙ`. -/
theorem π_kernelSection (s : (limit (idealSystem F ρ P e he)).val.obj U) (n : ℕ) :
    (limit.π F (op n)).hom.app U (kernelSection F ρ P e he U s) =
      ringComponent F ρ P e he U n s :=
  π_ringSection F U _ _ n

include he in
/-- The section of `𝒪'ₙ` attached to a section of `lim Fₙ` has reduction the reduction of that
section. -/
theorem reduction_hom_app_π (n : ℕ) (y : (limit F).obj.obj U) :
    (P n).reduction.hom.app U ((e n).hom.hom.app U ((limit.π F (op n)).hom.app U y)) =
      (reduction F ρ).hom.app U y :=
  (hom_app_congr (he n) U _).trans (hom_app_congr (π_comp_ρ F ρ n) U y)

variable {U} in
/-- The inclusion of `lim ℳₙ` into `lim Fₙ` is additive on sections. -/
theorem kernelSection_add (s t : (limit (idealSystem F ρ P e he)).val.obj U) :
    kernelSection F ρ P e he U (s + t) =
      kernelSection F ρ P e he U s + kernelSection F ρ P e he U t := by
  refine ringSection_ext F U fun n => ?_
  rw [map_add, π_kernelSection, π_kernelSection, π_kernelSection]
  simp only [ringComponent, idealComponent, map_add]
  exact (congrArg _ (incl_add _ _ _)).trans (map_add _ _ _)

variable {U} in
/-- The inclusion of `lim ℳₙ` into `lim Fₙ` is linear over `lim Fₙ`, acting on `lim ℳₙ`
through the reduction. -/
theorem kernelSection_smul (r : (limit F).obj.obj U)
    (s : (limit (idealSystem F ρ P e he)).val.obj U) :
    kernelSection F ρ P e he U (scalar ((reduction F ρ).hom.app U r) • s) =
      r * kernelSection F ρ P e he U s := by
  refine ringSection_ext F U fun n => ?_
  rw [map_mul, π_kernelSection, π_kernelSection]
  have key := (P n).mul_incl ((e n).hom.hom.app U ((limit.π F (op n)).hom.app U r))
    (idealComponent F ρ P e he U n s)
  rw [reduction_hom_app_π F ρ P e he U n r] at key
  have hc : idealComponent F ρ P e he U n (scalar ((reduction F ρ).hom.app U r) • s) =
      scalar ((reduction F ρ).hom.app U r) • idealComponent F ρ P e he U n s :=
    map_smul _ _ _
  change (e n).inv.hom.app U ((P n).incl (idealComponent F ρ P e he U n
    (scalar ((reduction F ρ).hom.app U r) • s))) = _
  rw [hc, ← key, map_mul, inv_app_hom_app]

variable {U} in
/-- The inclusion of `lim ℳₙ` into `lim Fₙ` commutes with restriction of sections. -/
theorem kernelSection_naturality {V : Cᵒᵖ} (f : U ⟶ V)
    (s : (limit (idealSystem F ρ P e he)).val.obj U) :
    kernelSection F ρ P e he V ((limit (idealSystem F ρ P e he)).val.map f s) =
      (limit F).obj.map f (kernelSection F ρ P e he U s) := by
  refine ringSection_ext F V fun n => ?_
  refine (π_kernelSection F ρ P e he V _ n).trans ?_
  refine Eq.trans ?_ (NatTrans.naturality_apply (limit.π F (op n)).hom f _).symm
  rw [π_kernelSection]
  change (e n).inv.hom.app V ((P n).incl ((limit.π (idealSystem F ρ P e he) (op n)).val.app V
    ((limit (idealSystem F ρ P e he)).val.map f s))) = _
  rw [PresheafOfModules.naturality_apply (limit.π (idealSystem F ρ P e he) (op n)).val f s]
  exact (congrArg ((e n).inv.hom.app V) ((P n).incl_naturality f _)).trans
    (NatTrans.naturality_apply (e n).inv.hom f _)

/-- **The inclusion `lim ℳₙ ⟶ lim Fₙ`**, linear over `lim Fₙ` acting on `lim ℳₙ` through the
reduction `lim Fₙ ⟶ 𝒪`. -/
def kernelInclusion :
    (SheafOfModules.restrictScalars ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map
      (reduction F ρ))).obj (limit (idealSystem F ρ P e he)) ⟶
      SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj (limit F)) where
  val :=
    { app := fun U => ModuleCat.ofHom
        (X := ((SheafOfModules.restrictScalars ((sheafCompose J
          (forget₂ CommRingCat.{u} RingCat.{u})).map (reduction F ρ))).obj
            (limit (idealSystem F ρ P e he))).val.obj U)
        (Y := (SheafOfModules.unit ((sheafCompose J
          (forget₂ CommRingCat.{u} RingCat.{u})).obj (limit F))).val.obj U)
        { toFun := kernelSection F ρ P e he U
          map_add' := kernelSection_add F ρ P e he
          map_smul' := fun r s => kernelSection_smul F ρ P e he r s }
      naturality := fun f => ModuleCat.hom_ext (LinearMap.ext fun s =>
        kernelSection_naturality F ρ P e he f s) }

/-- On sections, `kernelInclusion` is `kernelSection`. -/
theorem kernelInclusion_val_app (s : (limit (idealSystem F ρ P e he)).val.obj U) :
    ((kernelInclusion F ρ P e he).val.app U s : (limit F).obj.obj U) =
      kernelSection F ρ P e he U s :=
  rfl

/-- **`lim ℳₙ` is killed by the reduction.** -/
theorem kernelZero (s : (limit (idealSystem F ρ P e he)).val.obj U) :
    (reduction F ρ).hom.app U ((kernelInclusion F ρ P e he).val.app U s : (limit F).obj.obj U) =
      0 := by
  rw [kernelInclusion_val_app, ← reduction_hom_app_π F ρ P e he U 0, π_kernelSection,
    ringComponent, hom_app_inv_app]
  exact (P 0).reduction_incl _

/-- **`lim ℳₙ` is the whole kernel of the reduction, uniquely, on every section.** -/
theorem kernelUniversal (y : (limit F).obj.obj U) (hy : (reduction F ρ).hom.app U y = 0) :
    ∃! s : (limit (idealSystem F ρ P e he)).val.obj U,
      ((kernelInclusion F ρ P e he).val.app U s : (limit F).obj.obj U) = y := by
  have hn : ∀ n : ℕ, (P n).reduction.hom.app U
      ((e n).hom.hom.app U ((limit.π F (op n)).hom.app U y)) = 0 := fun n =>
    (reduction_hom_app_π F ρ P e he U n y).trans hy
  choose m hm using fun n => (P n).exists_incl _ (hn n)
  have hcompat : ∀ n : ℕ, inducedKernelSection (P (n + 1)) (P n) (transition F P e n)
      (transition_reduction F ρ P e he n) (m (n + 1)) = m n := fun n => by
    refine inducedKernelSection_eq _ _ _ _ _ _ ?_
    rw [hm, hm]
    change _ = (e n).hom.hom.app U ((F.map (homOfLE (Nat.le_succ n)).op).hom.app U
      ((e (n + 1)).inv.hom.app U ((e (n + 1)).hom.hom.app U
        ((limit.π F (op (n + 1))).hom.app U y))))
    rw [inv_app_hom_app]
    exact congrArg ((e n).hom.hom.app U)
      (hom_app_congr (limit.w F (homOfLE (Nat.le_succ n)).op) U y).symm
  have hcomp : ∀ (s : (limit (idealSystem F ρ P e he)).val.obj U),
      kernelSection F ρ P e he U s = y → ∀ n, idealComponent F ρ P e he U n s = m n :=
    fun s hs n => (P n).incl_injective (by
      rw [hm, ← hs, π_kernelSection, ringComponent, hom_app_inv_app])
  refine ⟨idealSection F ρ P e he U m hcompat, ?_, fun s hs => ?_⟩
  · refine ringSection_ext F U fun n => ?_
    rw [kernelInclusion_val_app, π_kernelSection, ringComponent, idealComponent_idealSection,
      hm, inv_app_hom_app]
  · exact idealSection_ext F ρ P e he U fun n =>
      (hcomp s hs n).trans (idealComponent_idealSection F ρ P e he U m hcompat n).symm

end Deformation.AlgebraExtension.InverseLimit

end
