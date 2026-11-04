module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FlatDeformation.Problem

/-!
# Transporting a first order thickening of a scheme to the space of the scheme

Let `i : X ⟶ X'` be a morphism of schemes whose underlying continuous map is a homeomorphism. This
file carries the structure sheaf of `X'` to the space of `X` along the inverse homeomorphism and
describes there the reduction `𝒪_{X'} ⟶ 𝒪_X`, its kernel, the map from a thickened base and the
maps between transports induced by morphisms of thickenings.

## Main definitions

* `Stacks.Thickenings.FlatDeformation.transported`: the structure sheaf of `X'`, as a sheaf of
  rings on the space of `X`.
* `Stacks.Thickenings.FlatDeformation.transportedReduction`: the reduction `𝒪_{X'} ⟶ 𝒪_X` on the
  space of `X`.
* `Stacks.Thickenings.FlatDeformation.kernelInclusion`: for `i` a closed immersion with
  `i.ker ^ 2 = ⊥` and `M ≅ 𝒞_{X/X'}`, the identification of `M` with the ideal of `X` in `X'`, as
  a morphism of modules over the transported structure sheaf.
* `Stacks.Thickenings.FlatDeformation.transportedBase`: for a commutative square
  `i ≫ f' = f ≫ t`, the map from `𝒪_{S'}` to the pushforward of the transported structure sheaf
  along `f ≫ t` given by `f'`.
* `Stacks.Thickenings.FlatDeformation.transportedMap`: the morphism of transported structure
  sheaves induced by `ψ : X'₂ ⟶ X'` with `i₂ ≫ ψ = i`.

## Main results

* `Stacks.Thickenings.FlatDeformation.isLocallySurjective_transportedReduction`: for `i` a closed
  immersion, the transported reduction is locally surjective.
* `Stacks.Thickenings.FlatDeformation.transportedReduction_ker_sq`: if moreover
  `i.ker ^ 2 = ⊥`, the kernel of the transported reduction on every open has square zero.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

universe u

namespace Stacks.Thickenings.FlatDeformation

/-- Two restrictions of a section of the structure sheaf of a scheme compose. -/
theorem scheme_map_map {Z : Scheme.{u}} {U V W : Z.Opensᵒᵖ} (g : U ⟶ V) (f : V ⟶ W)
    (h : U ⟶ W) (a : Z.presheaf.obj U) :
    Z.presheaf.map f (Z.presheaf.map g a) = Z.presheaf.map h a := by
  rw [Subsingleton.elim h (g ≫ f), Functor.map_comp, ConcreteCategory.comp_apply]

/-- Two successive restrictions of a section of the structure sheaf of a scheme are the restriction
along the composite. -/
theorem scheme_map_comp_apply {Z : Scheme.{u}} {U V W : Z.Opensᵒᵖ} (g : U ⟶ V) (f : V ⟶ W)
    (a : Z.presheaf.obj U) :
    Z.presheaf.map f (Z.presheaf.map g a) = Z.presheaf.map (g ≫ f) a :=
  scheme_map_map g f _ a

/-- Two chains of two restrictions with the same source and target send a section of the structure
sheaf of a scheme to the same section. -/
theorem scheme_map_map' {Z : Scheme.{u}} {U V V' W : Z.Opensᵒᵖ} (g : U ⟶ V) (f : V ⟶ W)
    (g' : U ⟶ V') (f' : V' ⟶ W) (a : Z.presheaf.obj U) :
    Z.presheaf.map f (Z.presheaf.map g a) = Z.presheaf.map f' (Z.presheaf.map g' a) :=
  (scheme_map_map g f (g ≫ f) a).trans (scheme_map_map g' f' (g ≫ f) a).symm

/-- Restricting a section of the structure sheaf of a scheme along an endomorphism of an open gives
the section back. -/
theorem scheme_map_self {Z : Scheme.{u}} {U : Z.Opensᵒᵖ} (g : U ⟶ U) (a : Z.presheaf.obj U) :
    Z.presheaf.map g a = a := by
  rw [Subsingleton.elim g (𝟙 U)]
  simp

/-- Restriction of sections of the structure sheaf of a scheme along an equality of opens is
injective. -/
theorem scheme_map_eqToHom_injective {Z : Scheme.{u}} {U V : Z.Opens} (h : U = V) :
    Function.Injective (Z.presheaf.map (eqToHom h).op) :=
  (ConcreteCategory.bijective_of_isIso _).1

/-- Two restrictions of a section of a sheaf of modules on a scheme compose. -/
theorem modules_map_map {Z : Scheme.{u}} (M : Z.Modules) {U V W : Z.Opensᵒᵖ} (g : U ⟶ V)
    (f : V ⟶ W) (h : U ⟶ W) (a : M.presheaf.obj U) :
    M.presheaf.map f (M.presheaf.map g a) = M.presheaf.map h a := by
  rw [Subsingleton.elim h (g ≫ f), Functor.map_comp, ConcreteCategory.comp_apply]

/-- Restricting a section of a sheaf of modules on a scheme along an endomorphism of an open gives
the section back. -/
theorem modules_map_self {Z : Scheme.{u}} (M : Z.Modules) {U : Z.Opensᵒᵖ} (g : U ⟶ U)
    (a : M.presheaf.obj U) : M.presheaf.map g a = a := by
  rw [Subsingleton.elim g (𝟙 U)]
  simp

/-- Restriction of sections of a sheaf of modules on a scheme along an equality of opens is
injective. -/
theorem scheme_modules_map_eqToHom_injective {Z : Scheme.{u}} (M : Z.Modules) {U V : Z.Opens}
    (h : U = V) : Function.Injective (M.presheaf.map (eqToHom h).op) :=
  (ConcreteCategory.bijective_of_isIso _).1

variable {X X' : Scheme.{u}} (i : X ⟶ X') [IsIso i.base]

/-- The inverse of the underlying homeomorphism of `i`. -/
abbrev invBase : X'.toPresheafedSpace.carrier ⟶ X.toPresheafedSpace.carrier := inv i.base

/-- `invBase i` followed by `i.base` is the identity of the space of `X'`. -/
theorem invBase_comp : invBase i ≫ i.base = 𝟙 _ := IsIso.inv_hom_id _

/-- `i.base` followed by `invBase i` is the identity of the space of `X`. -/
theorem comp_invBase : i.base ≫ invBase i = 𝟙 _ := IsIso.hom_inv_id _

/-- The open of `X'` corresponding to an open of `X`. -/
abbrev toAmbient (U : X.Opens) : X'.Opens := (Opens.map (invBase i)).obj U

/-- The preimage under `i` of `toAmbient i U` is `U`. -/
theorem preimage_toAmbient (U : X.Opens) : i ⁻¹ᵁ toAmbient i U = U := by
  ext x
  show (invBase i) (i.base x) ∈ U ↔ x ∈ U
  rw [← ConcreteCategory.comp_apply, comp_invBase, TopCat.id_app]

/-- `toAmbient i` sends the preimage under `i` of an open `V` of `X'` back to `V`. -/
theorem toAmbient_preimage (V : X'.Opens) : toAmbient i (i ⁻¹ᵁ V) = V := by
  ext x
  show i.base ((invBase i) x) ∈ V ↔ x ∈ V
  rw [← ConcreteCategory.comp_apply, invBase_comp, TopCat.id_app]

/-- `toAmbient i` is monotone. -/
theorem toAmbient_mono {U V : X.Opens} (h : U ≤ V) : toAmbient i U ≤ toAmbient i V :=
  (Opens.map (invBase i)).monotone h

/-- **The structure sheaf of `X'`, carried to the space of `X`.** -/
abbrev transported : TopCat.Sheaf CommRingCat.{u} X :=
  (TopCat.Sheaf.pushforward CommRingCat.{u} (invBase i)).obj X'.sheaf

/-- The comorphism of `i`, read on the transported sheaf. -/
def transportedReductionApp (U : X.Opens) :
    (transported i).presheaf.obj (op U) ⟶ X.presheaf.obj (op U) :=
  i.app (toAmbient i U) ≫ X.presheaf.map (eqToHom (preimage_toAmbient i U).symm).op

/-- **The reduction `𝒪_{X'} ⟶ 𝒪_X`, on the space of `X`.** -/
def transportedReduction : transported i ⟶ X.sheaf :=
  ⟨{ app U := transportedReductionApp i U.unop
     naturality {U V} h := by
       refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
       change (X.presheaf.map _) ((i.app _).hom ((X'.presheaf.map _) a)) =
         (X.presheaf.map h) ((X.presheaf.map _) ((i.app _).hom a))
       have hn := ConcreteCategory.congr_hom
         (i.naturality ((Opens.map (invBase i)).op.map h)) a
       change (i.app _).hom ((X'.presheaf.map _) a) = (X.presheaf.map _) ((i.app _).hom a) at hn
       rw [hn, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp,
         ← Functor.map_comp]
       rfl }⟩

/-- On sections over `U`, the transported reduction is `i.app (toAmbient i U)` followed by the
restriction along `U = i ⁻¹ᵁ toAmbient i U`. -/
theorem transportedReduction_app (U : X.Opens) (a : (transported i).presheaf.obj (op U)) :
    (transportedReduction i).hom.app (op U) a =
      X.presheaf.map (eqToHom (preimage_toAmbient i U).symm).op ((i.app (toAmbient i U)).hom a) :=
  rfl

/-- A section of the transported sheaf over `U` is killed by the transported reduction if and only
if it is killed by `i.app (toAmbient i U)`. -/
theorem transportedReduction_app_eq_zero_iff (U : X.Opens)
    (a : (transported i).presheaf.obj (op U)) :
    (transportedReduction i).hom.app (op U) a = 0 ↔ (i.app (toAmbient i U)).hom a = 0 := by
  rw [transportedReduction_app]
  constructor
  · intro h
    exact scheme_map_eqToHom_injective (preimage_toAmbient i U).symm (h.trans (map_zero _).symm)
  · intro h
    rw [h]
    exact map_zero _

variable [IsClosedImmersion i]

/-- The transported reduction is locally surjective. -/
theorem isLocallySurjective_transportedReduction :
    TopCat.Presheaf.IsLocallySurjective (transportedReduction i).hom := by
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro U b x hx
  obtain ⟨g, hg⟩ := i.stalkMap_surjective x (X.presheaf.germ U x hx b)
  obtain ⟨W, hW, a₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq X'.presheaf g
  rw [Scheme.Hom.germ_stalkMap_apply] at hg
  obtain ⟨M, hxM, i₁, i₂, hM⟩ := TopCat.Presheaf.germ_eq X.presheaf x hW hx _ _ hg
  have hMW : toAmbient i M ≤ W := by
    rw [← toAmbient_preimage i W]
    exact toAmbient_mono i (leOfHom i₁)
  refine ⟨M, leOfHom i₂, ⟨X'.presheaf.map (homOfLE hMW).op a₀, ?_⟩, hxM⟩
  refine (transportedReduction_app i M _).trans ?_
  have hnat := ConcreteCategory.congr_hom (i.naturality (homOfLE hMW).op) a₀
  change (i.app _).hom (X'.presheaf.map _ a₀) = X.presheaf.map _ ((i.app W).hom a₀) at hnat
  refine (congrArg _ hnat).trans ?_
  exact (scheme_map_map _ _ i₁.op _).trans hM

/-- The kernel of the transported reduction has square zero. -/
theorem transportedReduction_ker_sq (hi : i.ker ^ 2 = ⊥) (U : X.Opensᵒᵖ) :
    (RingHom.ker ((transportedReduction i).hom.app U).hom) ^ 2 = ⊥ := by
  rw [pow_two]
  refine le_antisymm (Ideal.mul_le.mpr fun a ha b hb => ?_) bot_le
  rw [RingHom.mem_ker, transportedReduction_app_eq_zero_iff] at ha hb
  have h := Ideal.mul_mem_mul (RingHom.mem_ker.mpr ha) (RingHom.mem_ker.mpr hb)
  have h2 : RingHom.ker (i.app (toAmbient i U.unop)).hom *
      RingHom.ker (i.app (toAmbient i U.unop)).hom = ⊥ := by
    rw [← pow_two]
    exact ker_app_sq_eq_bot i hi _
  rw [h2] at h
  exact h

/-! ### The ideal, identified with a module on `X` -/

section Kernel

variable (hi : i.ker ^ 2 = ⊥) {M : X.Modules} (e : M ≅ conormalModules i)

/-- A section of `M` over `U`, read as a section of `𝒪_{X'}` through `M ≅ 𝒞_{X/X'}`. -/
def kernelSection (U : X.Opens) (m : Γ(M, U)) : Γ(X', toAmbient i U) :=
  conormalSection hi (toAmbient i U) ((e.hom.app (i ⁻¹ᵁ toAmbient i U)).hom
    ((M.presheaf.map (eqToHom (preimage_toAmbient i U)).op).hom m))

/-- `kernelSection` is additive. -/
theorem kernelSection_add (U : X.Opens) (m n : Γ(M, U)) :
    kernelSection i hi e U (m + n) = kernelSection i hi e U m + kernelSection i hi e U n := by
  simp only [kernelSection, map_add, conormalSection_add]

omit [IsClosedImmersion i] in
/-- Restricting the image of a section `a` under the transported reduction along
`i ⁻¹ᵁ toAmbient i U = U` gives `i.app (toAmbient i U) a`. -/
theorem transportedReduction_restrict (U : X.Opens) (a : (transported i).presheaf.obj (op U)) :
    X.presheaf.map (eqToHom (preimage_toAmbient i U)).op
        ((transportedReduction i).hom.app (op U) a) = (i.app (toAmbient i U)).hom a :=
  (scheme_map_map _ _ (𝟙 _) _).trans (scheme_map_self _ _)

/-- `kernelSection` is linear over the transported structure sheaf: a section `a` acting on `M`
through the transported reduction becomes multiplication by `a`. -/
theorem kernelSection_smul (U : X.Opens) (a : (transported i).presheaf.obj (op U))
    (m : Γ(M, U)) :
    kernelSection i hi e U
        ((show Γ(X, U) from (transportedReduction i).hom.app (op U) a) • m) =
      (show Γ(X', toAmbient i U) from a) * kernelSection i hi e U m := by
  simp only [kernelSection]
  have h1 := Scheme.Modules.map_smul M (eqToHom (preimage_toAmbient i U))
    (show Γ(X, U) from (transportedReduction i).hom.app (op U) a) m
  rw [transportedReduction_restrict] at h1
  refine (congrArg (fun z => conormalSection hi (toAmbient i U) ((e.hom.app _).hom z)) h1).trans ?_
  refine (congrArg (conormalSection hi (toAmbient i U))
    (Scheme.Modules.Hom.app_smul e.hom _ _)).trans ?_
  exact conormalSection_smul hi _ _ _

/-- `kernelSection` commutes with restriction to a smaller open. -/
theorem kernelSection_map {U V : X.Opens} (h : V ≤ U) (m : Γ(M, U)) :
    kernelSection i hi e V (M.presheaf.map (homOfLE h).op m) =
      X'.presheaf.map (homOfLE (toAmbient_mono i h)).op (kernelSection i hi e U m) := by
  simp only [kernelSection]
  rw [conormalSection_map]
  congr 1
  have hn := congr($((Scheme.Modules.Hom.mapPresheaf e.hom).naturality
    (homOfLE (i.preimage_mono (toAmbient_mono i h))).op) ((M.presheaf.map
      (eqToHom (preimage_toAmbient i U)).op).hom m))
  refine Eq.trans ?_ hn
  show _ = (e.hom.app _).hom ((M.presheaf.map _).hom ((M.presheaf.map _).hom m))
  have hle : i ⁻¹ᵁ toAmbient i V ≤ U := by rw [preimage_toAmbient]; exact h
  exact congrArg (e.hom.app _).hom ((modules_map_map M _ _ (homOfLE hle).op m).trans
    (modules_map_map M _ _ _ m).symm)

/-- **The identification of a module on `X` with the ideal of `X` in `X'`**, as a morphism of
modules over the transported structure sheaf. -/
def kernelInclusion :
    (SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map
        (transportedReduction i))).obj M ⟶
      SheafOfModules.unit ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj (transported i)) where
  val :=
    { app U := ModuleCat.ofHom
        (X := ((SheafOfModules.restrictScalars
          ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map
            (transportedReduction i))).obj M).val.obj U)
        (Y := (SheafOfModules.unit ((sheafCompose (Opens.grothendieckTopology X)
          (forget₂ CommRingCat.{u} RingCat.{u})).obj (transported i))).val.obj U)
        { toFun := kernelSection i hi e U.unop
          map_add' := kernelSection_add i hi e U.unop
          map_smul' := fun a m => kernelSection_smul i hi e U.unop a m }
      naturality {U V} h := by
        ext m
        exact kernelSection_map i hi e (leOfHom h.unop) m }

/-- On sections over `U`, `kernelInclusion` is `kernelSection`. -/
theorem kernelInclusion_app (U : X.Opens) (m : Γ(M, U)) :
    (kernelInclusion i hi e).val.app (op U) m = kernelSection i hi e U m :=
  rfl

/-- The transported reduction kills every section in the image of `kernelSection`. -/
theorem transportedReduction_kernelSection (U : X.Opens) (m : Γ(M, U)) :
    (transportedReduction i).hom.app (op U) (kernelSection i hi e U m) = 0 :=
  (transportedReduction_app_eq_zero_iff i U _).mpr (conormalSection_mem_ker hi _ _)

/-- `kernelSection` is injective. -/
theorem kernelSection_injective (U : X.Opens) : Function.Injective (kernelSection i hi e U) := by
  intro m n h
  have h1 := conormalSection_injective hi (toAmbient i U) h
  have h2 := ((Scheme.Modules.Hom.isIso_iff_isIso_app (φ := e.hom)).mp inferInstance
    (i ⁻¹ᵁ toAmbient i U))
  exact scheme_modules_map_eqToHom_injective M (preimage_toAmbient i U)
    ((ConcreteCategory.bijective_of_isIso _).1 h1)

/-- Every section of the transported sheaf killed by the transported reduction is in the image of
`kernelSection`. -/
theorem exists_kernelSection_eq (U : X.Opens) (a : (transported i).presheaf.obj (op U))
    (ha : (transportedReduction i).hom.app (op U) a = 0) :
    ∃ m : Γ(M, U), kernelSection i hi e U m = a := by
  rw [transportedReduction_app_eq_zero_iff] at ha
  refine ⟨M.presheaf.map (eqToHom (preimage_toAmbient i U).symm).op ((e.inv.app _).hom
    (Stacks.Conormal.conormalClass i (toAmbient i U) (le_refl _) a ha)), ?_⟩
  simp only [kernelSection]
  have h1 := modules_map_map M (eqToHom (preimage_toAmbient i U).symm).op
    (eqToHom (preimage_toAmbient i U)).op (𝟙 _) ((e.inv.app _).hom
      (Stacks.Conormal.conormalClass i (toAmbient i U) (le_refl _) a ha))
  rw [modules_map_self] at h1
  have h2 : (e.hom.app (i ⁻¹ᵁ toAmbient i U)).hom ((e.inv.app _).hom
      (Stacks.Conormal.conormalClass i (toAmbient i U) (le_refl _) a ha)) =
      Stacks.Conormal.conormalClass i (toAmbient i U) (le_refl _) a ha := by
    show ((e.inv ≫ e.hom).app _).hom _ = _
    rw [e.inv_hom_id]
    rfl
  refine (congrArg (conormalSection hi (toAmbient i U))
    ((congrArg (e.hom.app _).hom h1).trans h2)).trans ?_
  exact (conormalSection_conormalClass_of_le i hi (toAmbient i U) (toAmbient i U) le_rfl a
    ha).trans
    (scheme_map_self _ _)

/-- If `e` sends `m` to the conormal class of a section `r` of the ideal of `X` in `X'` over an
open `L` containing `toAmbient i U`, then `kernelSection` sends `m` to the restriction of `r` to
`toAmbient i U`. -/
theorem kernelSection_eq_of_conormalClass (U : X.Opens) (m : Γ(M, U)) (L : X'.Opens)
    (hL : toAmbient i U ≤ L) (r : Γ(X', L)) (hr : (i.app L).hom r = 0)
    (h : (e.hom.app U).hom m = Stacks.Conormal.conormalClass i L
      (by rw [← preimage_toAmbient i U]; exact i.preimage_mono hL) r hr) :
    kernelSection i hi e U m = X'.presheaf.map (homOfLE hL).op r := by
  simp only [kernelSection]
  have hn := ConcreteCategory.congr_hom ((Scheme.Modules.Hom.mapPresheaf e.hom).naturality
    (eqToHom (preimage_toAmbient i U)).op) m
  change ((e.hom.app _).hom (M.presheaf.map _ m)) =
    ((conormalModules i).presheaf.map _ ((e.hom.app _).hom m)) at hn
  rw [hn, h]
  have h2 := Stacks.Conormal.conormalClass_restrict_target i L
    (by rw [← preimage_toAmbient i U]; exact i.preimage_mono hL) (i.preimage_mono hL)
    (le_of_eq (preimage_toAmbient i U)) r hr
  refine (congrArg (conormalSection hi (toAmbient i U)) ((congrArg (fun g =>
    ((conormalModules i).presheaf.map g).hom (Stacks.Conormal.conormalClass i L _ r hr))
    (Subsingleton.elim _ _)).trans h2)).trans ?_
  exact conormalSection_conormalClass_of_le i hi L _ hL r hr

end Kernel

/-! ### The map from the thickened base -/

section Base

variable {S S' : Scheme.{u}} {t : S ⟶ S'} {f : X ⟶ S} {f' : X' ⟶ S'} (comm : i ≫ f' = f ≫ t)
include comm

omit [IsIso i.base] [IsClosedImmersion i] in
/-- For a commutative square `i ≫ f' = f ≫ t`, the preimage of an open `V` of `S'` under `f ≫ t` is
the preimage of `f' ⁻¹ᵁ V` under `i`. -/
theorem preimage_comm (V : S'.Opens) :
    (Opens.map (f.base ≫ t.base)).obj V = i ⁻¹ᵁ (f' ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_base, ← comm]
  rfl

omit [IsClosedImmersion i] in
/-- For a commutative square `i ≫ f' = f ≫ t`, `toAmbient i` sends the preimage of an open `V` of
`S'` under `f ≫ t` to `f' ⁻¹ᵁ V`. -/
theorem toAmbient_comm (V : S'.Opens) :
    toAmbient i ((Opens.map (f.base ≫ t.base)).obj V) = f' ⁻¹ᵁ V := by
  rw [preimage_comm i comm, toAmbient_preimage]

/-- The comorphism of `f'`, read on the transported sheaf. -/
def transportedBase : S'.sheaf ⟶
    (TopCat.Sheaf.pushforward CommRingCat.{u} (f.base ≫ t.base)).obj (transported i) :=
  ⟨{ app V := f'.app V.unop ≫ X'.presheaf.map (eqToHom (toAmbient_comm i comm V.unop)).op
     naturality {V W} h := by
       refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
       change (X'.presheaf.map _) ((f'.app _).hom ((S'.presheaf.map h) a)) =
         (X'.presheaf.map _) ((X'.presheaf.map _) ((f'.app _).hom a))
       have hn := ConcreteCategory.congr_hom (f'.naturality h) a
       change (f'.app _).hom ((S'.presheaf.map h) a) = (X'.presheaf.map _) ((f'.app _).hom a) at hn
       rw [hn]
       exact scheme_map_map' _ _ _ _ _ }⟩

omit [IsClosedImmersion i] in
/-- On sections over `V`, `transportedBase` is `f'.app V` followed by the restriction along
`toAmbient_comm`. -/
theorem transportedBase_app (V : S'.Opens) (a : Γ(S', V)) :
    (transportedBase i comm).hom.app (op V) a =
      X'.presheaf.map (eqToHom (toAmbient_comm i comm V)).op ((f'.app V).hom a) :=
  rfl

omit [IsClosedImmersion i] in
/-- On sections over `V`, `transportedBase` followed by the transported reduction is
`(f ≫ t).app V`. -/
theorem transportedReduction_transportedBase (V : S'.Opens) (a : Γ(S', V)) :
    (transportedReduction i).hom.app (op ((Opens.map (f.base ≫ t.base)).obj V))
        ((transportedBase i comm).hom.app (op V) a) = ((f ≫ t).app V).hom a := by
  refine (transportedReduction_app i _ _).trans ?_
  have hn := ConcreteCategory.congr_hom (i.naturality
    (eqToHom (toAmbient_comm i comm V)).op) ((f'.app V).hom a)
  change (i.app _).hom ((X'.presheaf.map _) _) = (X.presheaf.map _) ((i.app _).hom _) at hn
  refine (congrArg _ hn).trans ((scheme_map_map _ _ (eqToHom (preimage_comm i comm V)).op
    _).trans ?_)
  have hc := ConcreteCategory.congr_hom (Scheme.Hom.congr_app comm V) a
  change ((i.app _).hom ((f'.app _).hom a)) = (X.presheaf.map _) (((f ≫ t).app _).hom a) at hc
  exact (congrArg _ hc).trans ((scheme_map_map _ _ (𝟙 _) _).trans (scheme_map_self _ _))

omit [IsClosedImmersion i] in
/-- `transportedBase` followed by the pushforward of the transported reduction is the map of
structure sheaves of `f ≫ t`. -/
theorem transportedBase_comp_reduction :
    transportedBase i comm ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} (f.base ≫ t.base)).map
        (transportedReduction i) =
      Stacks.Sheaves.RingedSpaceDifferentials.structureSheafMap
        (f.toLRSHom.toShHom ≫ t.toLRSHom.toShHom) :=
  Sheaf.hom_ext (NatTrans.ext (funext fun V => CommRingCat.hom_ext (RingHom.ext fun a =>
    transportedReduction_transportedBase i comm V.unop a)))

end Base

/-! ### Functoriality of the transport -/

section Map

variable {X'₂ : Scheme.{u}} (i₂ : X ⟶ X'₂) [IsIso i₂.base] [IsClosedImmersion i₂] {ψ : X'₂ ⟶ X'}
  (hψ : i₂ ≫ ψ = i)
include hψ

omit [IsClosedImmersion i] [IsClosedImmersion i₂] in
/-- If `i₂ ≫ ψ = i`, then `ψ.base` followed by `invBase i` is `invBase i₂`. -/
theorem base_comp_invBase : ψ.base ≫ invBase i = invBase i₂ := by
  simp only [invBase]
  rw [IsIso.comp_inv_eq, IsIso.eq_inv_comp, ← Scheme.Hom.comp_base, hψ]

omit [IsClosedImmersion i] [IsClosedImmersion i₂] in
/-- If `i₂ ≫ ψ = i`, the preimage under `ψ` of `toAmbient i U` is `toAmbient i₂ U`. -/
theorem preimage_toAmbient_map (U : X.Opens) : ψ ⁻¹ᵁ toAmbient i U = toAmbient i₂ U := by
  ext x
  show (invBase i) (ψ.base x) ∈ U ↔ (invBase i₂) x ∈ U
  rw [← ConcreteCategory.comp_apply, base_comp_invBase i i₂ hψ]

/-- **The morphism `transported i ⟶ transported i₂` induced by a morphism `ψ : X'₂ ⟶ X'` with
`i₂ ≫ ψ = i`.** -/
def transportedMap : transported i ⟶ transported i₂ :=
  ⟨{ app U := ψ.app (toAmbient i U.unop) ≫
       X'₂.presheaf.map (eqToHom (preimage_toAmbient_map i i₂ hψ U.unop).symm).op
     naturality {U V} h := by
       refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
       change (X'₂.presheaf.map _) ((ψ.app _).hom ((X'.presheaf.map _) a)) =
         (X'₂.presheaf.map _) ((X'₂.presheaf.map _) ((ψ.app _).hom a))
       have hn := ConcreteCategory.congr_hom (ψ.naturality ((Opens.map (invBase i)).op.map h)) a
       change (ψ.app _).hom ((X'.presheaf.map _) a) = (X'₂.presheaf.map _) ((ψ.app _).hom a) at hn
       rw [hn]
       exact scheme_map_map' _ _ _ _ _ }⟩

omit [IsClosedImmersion i] [IsClosedImmersion i₂] in
/-- On sections over `U`, `transportedMap` is `ψ.app (toAmbient i U)` followed by the restriction
along `preimage_toAmbient_map`. -/
theorem transportedMap_app (U : X.Opens) (a : (transported i).presheaf.obj (op U)) :
    (transportedMap i i₂ hψ).hom.app (op U) a =
      X'₂.presheaf.map (eqToHom (preimage_toAmbient_map i i₂ hψ U).symm).op ((ψ.app _).hom a) :=
  rfl

omit [IsClosedImmersion i] [IsClosedImmersion i₂] in
/-- `transportedMap` commutes with the transported reductions. -/
theorem transportedMap_comp_reduction :
    transportedMap i i₂ hψ ≫ transportedReduction i₂ = transportedReduction i := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U =>
    CommRingCat.hom_ext (RingHom.ext fun a => ?_)))
  show (transportedReduction i₂).hom.app (op U.unop) ((transportedMap i i₂ hψ).hom.app U a) =
    (transportedReduction i).hom.app (op U.unop) a
  refine (transportedReduction_app i₂ U.unop _).trans ?_
  refine Eq.trans ?_ (transportedReduction_app i U.unop _).symm
  have hn := ConcreteCategory.congr_hom (i₂.naturality
    (eqToHom (preimage_toAmbient_map i i₂ hψ U.unop).symm).op) ((ψ.app _).hom a)
  change (i₂.app _).hom ((X'₂.presheaf.map _) _) = (X.presheaf.map _) ((i₂.app _).hom _) at hn
  refine (congrArg _ hn).trans ((scheme_map_comp_apply _ _ _).trans ?_)
  have hc := ConcreteCategory.congr_hom (Scheme.Hom.congr_app hψ (toAmbient i U.unop)) a
  change ((i₂.app _).hom ((ψ.app _).hom a)) = (X.presheaf.map _) ((i.app _).hom a) at hc
  refine (congrArg _ hc).trans ?_
  exact (scheme_map_comp_apply _ _ _).trans
    (congrArg (fun g => (X.presheaf.map g).hom _) (Subsingleton.elim _ _))

variable {S S' : Scheme.{u}} {t : S ⟶ S'} {f : X ⟶ S} {f' : X' ⟶ S'} {f'₂ : X'₂ ⟶ S'}
  (comm : i ≫ f' = f ≫ t) (comm₂ : i₂ ≫ f'₂ = f ≫ t) (hψf : ψ ≫ f' = f'₂)
include hψf

omit [IsClosedImmersion i] [IsClosedImmersion i₂] in
/-- If moreover `ψ ≫ f' = f'₂`, `transportedMap` commutes with the maps `transportedBase` from the
thickened base. -/
theorem transportedMap_transportedBase (V : S'.Opens) (a : Γ(S', V)) :
    (transportedMap i i₂ hψ).hom.app (op ((Opens.map (f.base ≫ t.base)).obj V))
        ((transportedBase i comm).hom.app (op V) a) =
      (transportedBase i₂ comm₂).hom.app (op V) a := by
  refine (transportedMap_app i i₂ hψ _ _).trans ?_
  refine Eq.trans ?_ (transportedBase_app i₂ comm₂ V a).symm
  refine (congrArg _ (congrArg (ψ.app _).hom (transportedBase_app i comm V a))).trans ?_
  have hn := ConcreteCategory.congr_hom (ψ.naturality
    (eqToHom (toAmbient_comm i comm V)).op) ((f'.app V).hom a)
  change (ψ.app _).hom ((X'.presheaf.map _) _) = (X'₂.presheaf.map _) ((ψ.app _).hom _) at hn
  refine (congrArg _ hn).trans ((scheme_map_comp_apply _ _ _).trans ?_)
  have hc := ConcreteCategory.congr_hom (Scheme.Hom.congr_app hψf V) a
  change ((ψ.app _).hom ((f'.app _).hom a)) = (X'₂.presheaf.map _) ((f'₂.app _).hom a) at hc
  refine (congrArg _ hc).trans ?_
  exact (scheme_map_comp_apply _ _ _).trans
    (congrArg (fun g => (X'₂.presheaf.map g).hom _) (Subsingleton.elim _ _))

omit hψf in
omit comm comm₂ in
omit [IsClosedImmersion i] [IsClosedImmersion i₂] in
/-- `transportedMap` is compatible with composition of morphisms of thickenings. -/
theorem transportedMap_comp {X'₃ : Scheme.{u}} (i₃ : X ⟶ X'₃) [IsIso i₃.base] [IsClosedImmersion i₃]
    {ψ' : X'₃ ⟶ X'₂} (hψ' : i₃ ≫ ψ' = i₂) :
    transportedMap i i₂ hψ ≫ transportedMap i₂ i₃ hψ' =
      transportedMap i i₃ (show i₃ ≫ ψ' ≫ ψ = i by rw [← Category.assoc, hψ', hψ]) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U =>
    CommRingCat.hom_ext (RingHom.ext fun a => ?_)))
  show (transportedMap i₂ i₃ hψ').hom.app (op U.unop) ((transportedMap i i₂ hψ).hom.app
    (op U.unop) a) = (transportedMap i i₃ _).hom.app (op U.unop) a
  refine (transportedMap_app i₂ i₃ hψ' _ _).trans ?_
  refine Eq.trans ?_ (transportedMap_app i i₃ _ _ _).symm
  refine (congrArg _ (congrArg (ψ'.app _).hom (transportedMap_app i i₂ hψ _ _))).trans ?_
  have hn := ConcreteCategory.congr_hom (ψ'.naturality
    (eqToHom (preimage_toAmbient_map i i₂ hψ U.unop).symm).op) ((ψ.app _).hom a)
  change (ψ'.app _).hom ((X'₂.presheaf.map _) _) = (X'₃.presheaf.map _) ((ψ'.app _).hom _) at hn
  refine (congrArg _ hn).trans ((scheme_map_comp_apply _ _ _).trans ?_)
  show _ = (X'₃.presheaf.map _) (((ψ' ≫ ψ).app _).hom a)
  exact congrArg (fun g => (X'₃.presheaf.map g).hom _) (Subsingleton.elim _ _)

omit hψf in
omit comm comm₂ in
omit hψ in
omit [IsClosedImmersion i] in
/-- `transportedMap` along the identity of `X'` is the identity. -/
theorem transportedMap_id : transportedMap i i (Category.comp_id i) = 𝟙 _ := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U =>
    CommRingCat.hom_ext (RingHom.ext fun a => ?_)))
  show (transportedMap i i (Category.comp_id i)).hom.app (op U.unop) a = a
  refine (transportedMap_app i i _ _ _).trans ?_
  show (X'.presheaf.map _) ((Scheme.Hom.app (𝟙 X') _).hom a) = a
  exact scheme_map_self _ _

end Map

end Stacks.Thickenings.FlatDeformation
