module

public import StacksFrontier.Deformation.ToposThickening.TrivialSquareZeroReduction

/-!
# A split square-zero extension of sheaves of rings is trivial

Let `A` be a sheaf of commutative rings on a site with ring maps `s : O₀ ⟶ A` and `r : A ⟶ O₀`,
`s ≫ r = 𝟙`, whose kernel `I = ker r` has square zero. Then `I` is a sheaf of `O₀`-modules
through `s` (`Deformation.ComplexLift.splitIdeal`) and `A` is the trivial square-zero extension
`O₀[I] = O₀ ⊕ I`, by `(a, m) ↦ s(a) + m` (`Deformation.ComplexLift.splitSqZeroExtIso`), compatibly
with the projections to `O₀` and the inclusions of `O₀`.

In the proof of Stacks 0DLL, `A` is the structure sheaf of `X_V = X₀ ×_{Spec k} Spec k[V]`
carried to the small étale site of `X₀`, `s` is pullback along the projection `X_V ⟶ X₀` and `r`
is restriction to `X₀`.

Nothing here is registered.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
* [Stacks Project, Tag 08RR](https://stacks.math.columbia.edu/tag/08RR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits PresheafOfModules

universe u

namespace Deformation.ComplexLift

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O₀ A : Sheaf J CommRingCat.{u}} (s : O₀ ⟶ A) (r : A ⟶ O₀)

/-- **The kernel of `r : A ⟶ O₀`, as a sheaf of `O₀`-modules through `s : O₀ ⟶ A`.** Its
sections over `U` are the sections of `A` over `U` killed by `r`, and a section `a` of `O₀`
acts by multiplication by `s(a)`. -/
abbrev splitIdeal : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀) :=
  (SheafOfModules.restrictScalars (ringSheafMapOf J s)).obj (kernelModule r)

/-- The underlying section of `A` of a section of the kernel. -/
abbrev splitIdealVal {U : Cᵒᵖ} (m : (splitIdeal s r).val.obj U) : A.obj.obj U :=
  (show (kernelModule r).val.obj U from m).val

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- A section of the kernel is killed by `r`. -/
theorem splitIdealVal_mem {U : Cᵒᵖ} (m : (splitIdeal s r).val.obj U) :
    r.hom.app U (splitIdealVal s r m) = 0 :=
  (structureModuleMap_val_app r U _).symm.trans
    (show (kernelModule r).val.obj U from m).2

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The underlying section of `A` of a sum of sections of the kernel is the sum. -/
theorem splitIdealVal_add {U : Cᵒᵖ} (m n : (splitIdeal s r).val.obj U) :
    splitIdealVal s r (m + n) = splitIdealVal s r m + splitIdealVal s r n := rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- A section `a` of `O₀` acts on the kernel by multiplication by `s(a)`. -/
theorem splitIdealVal_smul {U : Cᵒᵖ} (a : O₀.obj.obj U) (m : (splitIdeal s r).val.obj U) :
    splitIdealVal s r (a • m) = s.hom.app U a * splitIdealVal s r m := rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Taking the underlying section of `A` commutes with restriction. -/
theorem splitIdealVal_restrict {U V : Cᵒᵖ} (i : U ⟶ V) (m : (splitIdeal s r).val.obj U) :
    splitIdealVal s r ((splitIdeal s r).val.map i m) = A.obj.map i (splitIdealVal s r m) := rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- A section of the kernel is determined by its underlying section of `A`. -/
theorem splitIdealVal_injective {U : Cᵒᵖ} :
    Function.Injective (splitIdealVal s r (U := U)) :=
  fun _ _ h => Subtype.ext h

/-- A section of `A` killed by `r` is a section of the kernel. -/
def splitIdealMk {U : Cᵒᵖ} (a : A.obj.obj U) (ha : r.hom.app U a = 0) :
    (splitIdeal s r).val.obj U :=
  show (kernelModule r).val.obj U from
    ⟨a, (structureModuleMap_val_app r U a).trans ha⟩

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The underlying section of `splitIdealMk s r a ha` is `a`. -/
@[simp]
theorem splitIdealVal_mk {U : Cᵒᵖ} (a : A.obj.obj U) (ha : r.hom.app U a = 0) :
    splitIdealVal s r (splitIdealMk s r a ha) = a := rfl

variable (hsr : s ≫ r = 𝟙 O₀)
  (hsq : ∀ (U : Cᵒᵖ) (a b : A.obj.obj U), r.hom.app U a = 0 → r.hom.app U b = 0 → a * b = 0)

include hsr in
omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- If `s ≫ r = 𝟙`, then `r(s(a)) = a` for every section `a` of `O₀`. -/
theorem split_app_apply (U : Cᵒᵖ) (a : O₀.obj.obj U) : r.hom.app U (s.hom.app U a) = a := by
  have h := congrArg (fun φ : O₀ ⟶ O₀ => φ.hom.app U a) hsr
  exact h

/-- If an additive map `f` sends `b` to `a` and `m` to `0`, it sends `b + m` to `a`. -/
private theorem map_add_eq_of_map_eq_zero {R S : Type*} [AddZeroClass R] [AddZeroClass S]
    (f : S → R) (hf : ∀ x y, f (x + y) = f x + f y) {a : R} {b m : S} (hb : f b = a)
    (hm : f m = 0) : f (b + m) = a := by
  rw [hf, hb, hm, add_zero]

/-- The ring map `O₀[I] ⟶ A`, `(a, m) ↦ s(a) + m`, over one object. -/
def splitSqZeroExtHomApp (U : Cᵒᵖ) :
    (sqZeroExtSheafAnySite O₀ (splitIdeal s r)).obj.obj U ⟶ A.obj.obj U :=
  CommRingCat.ofHom
    { toFun := fun x => s.hom.app U (sqZeroExtFstAnySite (M := (splitIdeal s r).val) x) +
        splitIdealVal s r (sqZeroExtSndAnySite (M := (splitIdeal s r).val) x)
      map_one' := by
        change s.hom.app U 1 + splitIdealVal s r 0 = 1
        rw [map_one]
        exact add_zero 1
      map_mul' := fun x y => by
        have hx := splitIdealVal_mem s r (sqZeroExtSndAnySite (M := (splitIdeal s r).val) x)
        have hy := splitIdealVal_mem s r (sqZeroExtSndAnySite (M := (splitIdeal s r).val) y)
        change s.hom.app U (sqZeroExtFstAnySite (M := (splitIdeal s r).val) x *
            sqZeroExtFstAnySite (M := (splitIdeal s r).val) y) +
          splitIdealVal s r (sqZeroExtFstAnySite (M := (splitIdeal s r).val) x •
              sqZeroExtSndAnySite (M := (splitIdeal s r).val) y +
            sqZeroExtFstAnySite (M := (splitIdeal s r).val) y •
              sqZeroExtSndAnySite (M := (splitIdeal s r).val) x) = _
        rw [splitIdealVal_add, splitIdealVal_smul, splitIdealVal_smul, map_mul]
        have h0 := hsq U _ _ hx hy
        set a := s.hom.app U (sqZeroExtFstAnySite (M := (splitIdeal s r).val) x)
        set b := s.hom.app U (sqZeroExtFstAnySite (M := (splitIdeal s r).val) y)
        set m := splitIdealVal s r (sqZeroExtSndAnySite (M := (splitIdeal s r).val) x)
        set n := splitIdealVal s r (sqZeroExtSndAnySite (M := (splitIdeal s r).val) y)
        change a * b + (a * n + b * m) = (a + m) * (b + n)
        linear_combination (-1 : A.obj.obj U) * h0
      map_zero' := by
        change s.hom.app U 0 + splitIdealVal s r 0 = 0
        rw [map_zero]
        exact add_zero 0
      map_add' := fun x y => by
        change s.hom.app U (sqZeroExtFstAnySite (M := (splitIdeal s r).val) x +
            sqZeroExtFstAnySite (M := (splitIdeal s r).val) y) +
          splitIdealVal s r (sqZeroExtSndAnySite (M := (splitIdeal s r).val) x +
            sqZeroExtSndAnySite (M := (splitIdeal s r).val) y) = _
        rw [splitIdealVal_add, map_add]
        abel }

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The map `splitSqZeroExtHomApp` sends `(a, m)` to `s(a) + m`. -/
theorem splitSqZeroExtHomApp_apply (U : Cᵒᵖ)
    (x : (sqZeroExtSheafAnySite O₀ (splitIdeal s r)).obj.obj U) :
    (splitSqZeroExtHomApp s r hsq U).hom x =
      s.hom.app U (sqZeroExtFstAnySite (M := (splitIdeal s r).val) x) +
        splitIdealVal s r (sqZeroExtSndAnySite (M := (splitIdeal s r).val) x) := rfl

/-- **The ring map `O₀[I] ⟶ A`, `(a, m) ↦ s(a) + m`.** -/
def splitSqZeroExtHom : sqZeroExtSheafAnySite O₀ (splitIdeal s r) ⟶ A :=
  ObjectProperty.homMk
    { app U := splitSqZeroExtHomApp s r hsq U
      naturality {U V} i := by
        ext x
        change s.hom.app V ((O₀.obj.map i).hom
              (sqZeroExtFstAnySite (M := (splitIdeal s r).val) x)) +
            splitIdealVal s r ((splitIdeal s r).val.map i
              (sqZeroExtSndAnySite (M := (splitIdeal s r).val) x)) =
          (A.obj.map i).hom (s.hom.app U (sqZeroExtFstAnySite (M := (splitIdeal s r).val) x) +
            splitIdealVal s r (sqZeroExtSndAnySite (M := (splitIdeal s r).val) x))
        rw [map_add, splitIdealVal_restrict]
        congr 1
        change (O₀.obj.map i ≫ s.hom.app V) (sqZeroExtFstAnySite (M := (splitIdeal s r).val) x) =
          (s.hom.app U ≫ A.obj.map i) (sqZeroExtFstAnySite (M := (splitIdeal s r).val) x)
        rw [s.hom.naturality] }

include hsr in
/-- The inverse ring map `A ⟶ O₀[I]`, `a ↦ (r(a), a - s(r(a)))`, over one object. -/
def splitSqZeroExtInvApp (U : Cᵒᵖ) :
    A.obj.obj U → (sqZeroExtSheafAnySite O₀ (splitIdeal s r)).obj.obj U :=
  fun a => sqZeroExtMkAnySite (M := (splitIdeal s r).val) (r.hom.app U a)
    (splitIdealMk s r (a - s.hom.app U (r.hom.app U a)) (by
      rw [map_sub, split_app_apply s r hsr, sub_self]))

include hsr in
omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- If `s ≫ r = 𝟙`, the map `O₀[I] ⟶ A`, `(a, m) ↦ s(a) + m`, is bijective over each object. -/
theorem splitSqZeroExtHomApp_bijective (U : Cᵒᵖ) :
    Function.Bijective (splitSqZeroExtHomApp s r hsq U).hom := by
  refine Function.bijective_iff_has_inverse.2 ⟨splitSqZeroExtInvApp s r hsr U, ?_, ?_⟩
  · intro x
    refine sqZeroExt_ext_anySite ?_ ?_
    · exact map_add_eq_of_map_eq_zero _ (map_add _) (split_app_apply s r hsr _ _)
        (splitIdealVal_mem s r _)
    · apply splitIdealVal_injective s r
      change _ - s.hom.app U (r.hom.app U (_ + _)) = _
      rw [splitSqZeroExtHomApp_apply, map_add_eq_of_map_eq_zero _ (map_add _)
        (split_app_apply s r hsr _ _) (splitIdealVal_mem s r _)]
      abel
  · intro a
    show s.hom.app U (r.hom.app U a) + (a - s.hom.app U (r.hom.app U a)) = a
    abel

/-- **A split square-zero extension is trivial**: `(a, m) ↦ s(a) + m` is an isomorphism
`O₀[I] ≅ A` of sheaves of commutative rings, `I` the kernel of `r` read as an `O₀`-module through
`s`. -/
def splitSqZeroExtIso : sqZeroExtSheafAnySite O₀ (splitIdeal s r) ≅ A :=
  haveI : IsIso ((sheafToPresheaf J CommRingCat.{u}).map (splitSqZeroExtHom s r hsq)) := by
    have : ∀ U : Cᵒᵖ, IsIso (((sheafToPresheaf J CommRingCat.{u}).map
        (splitSqZeroExtHom s r hsq)).app U) := fun U =>
      (ConcreteCategory.isIso_iff_bijective _).2 (splitSqZeroExtHomApp_bijective s r hsr hsq U)
    exact NatIso.isIso_of_isIso_app _
  haveI : IsIso (splitSqZeroExtHom s r hsq) :=
    isIso_of_reflects_iso _ (sheafToPresheaf J CommRingCat.{u})
  asIso (splitSqZeroExtHom s r hsq)

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The isomorphism `O₀[I] ≅ A` sends `(a, m)` to `s(a) + m`. -/
@[simp]
theorem splitSqZeroExtIso_hom_app_apply (U : Cᵒᵖ)
    (x : (sqZeroExtSheafAnySite O₀ (splitIdeal s r)).obj.obj U) :
    (splitSqZeroExtIso s r hsr hsq).hom.hom.app U x =
      s.hom.app U (sqZeroExtFstAnySite (M := (splitIdeal s r).val) x) +
        splitIdealVal s r (sqZeroExtSndAnySite (M := (splitIdeal s r).val) x) := rfl

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The isomorphism `O₀[I] ≅ A` is compatible with the projections to `O₀`. -/
theorem splitSqZeroExtIso_hom_comp :
    (splitSqZeroExtIso s r hsr hsq).hom ≫ r = sqZeroExtSheafAnySiteProj (splitIdeal s r) := by
  ext U x
  show r.hom.app U (s.hom.app U (sqZeroExtFstAnySite (M := (splitIdeal s r).val) x) +
    splitIdealVal s r (sqZeroExtSndAnySite (M := (splitIdeal s r).val) x)) = _
  rw [map_add_eq_of_map_eq_zero _ (map_add _) (split_app_apply s r hsr _ _)
        (splitIdealVal_mem s r _)]
  rfl

end Deformation.ComplexLift

end
