module

public import StacksFrontier.Homology.Eta.Complex
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The décalage commutes with restriction of scalars

Let `B` be an `A`-algebra, let `c ∈ A`, and let `C^•` be a cochain complex of `B`-modules.
Restricting scalars to `A` turns `C^•` into a complex of `A`-modules, on which `c` acts as its
image in `B`.  The décalage of More on Algebra, Tag 0F7N, taken with respect to `c` over `A`, is
the restriction of scalars of the décalage taken with respect to the image of `c` over `B`:

`η_c (C^•|_A) ≅ (η_c C^•)|_A`.

The two décalages live in two different localizations — of the `A`-module `C^i` at the powers of
`c`, and of the `B`-module `C^i` at the powers of the image of `c` — and the comparison is the
canonical identification of these two localizations
(`IsLocalizedModule.restrictScalars_powers`), which takes the submodules `cⁱ C^i` to one another
and commutes with the localized differentials.

## Main definitions

* `EtaComplex.locRestrictScalarsEquiv`: the identification of the two localizations.
* `EtaComplex.etaObjectRestrictScalarsIso`: the isomorphism of complexes
  `η_c (C^•|_A) ≅ (η_c C^•)|_A`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace EtaComplex

section Module

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (c : A)
  (M : Type u) [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]

/-- **The two localizations agree.**  The localization at the powers of `c` of the `A`-module `M`
is the localization at the powers of the image of `c` of the `B`-module `M`. -/
def locRestrictScalarsEquiv : EtaPow.Loc c M ≃ₗ[A] EtaPow.Loc (algebraMap A B c) M :=
  haveI := IsLocalizedModule.restrictScalars_powers c
    (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap A B c)) M)
  IsLocalizedModule.iso (Submonoid.powers c)
    ((LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap A B c)) M).restrictScalars A)

/-- The localization map at the powers of the image of `c`, read over `A`, is a localization map at
the powers of `c`. -/
private instance isLocalizedModule_restrictScalars_mk :
    IsLocalizedModule (Submonoid.powers c)
      ((LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap A B c)) M).restrictScalars A) :=
  IsLocalizedModule.restrictScalars_powers c _

/-- The comparison of localizations sends the image `m / 1` of `m ∈ M` in the localization at the
powers of `c` to its image `m / 1` in the localization at the powers of the image of `c`. -/
@[simp]
theorem locRestrictScalarsEquiv_toLoc (m : M) :
    locRestrictScalarsEquiv (B := B) c M (EtaPow.toLoc c M m) =
      EtaPow.toLoc (algebraMap A B c) M m := by
  exact IsLocalizedModule.iso_mk_one _ _ m

/-- The powers of `c` act invertibly on the localization at the powers of its image. -/
private theorem isUnit_algebraMap_loc (s : Submonoid.powers c) :
    IsUnit ((algebraMap A (Module.End A (EtaPow.Loc (algebraMap A B c) M))) s) := by
  exact IsLocalizedModule.map_units
    ((LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap A B c)) M).restrictScalars A) s

variable {M} {N : Type u} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]

/-- **The comparison of localizations commutes with the localized maps.**  For a `B`-linear map
`d`, read as an `A`-linear map `d'`, localizing `d'` at the powers of `c` and localizing `d` at the
powers of the image of `c` agree under the comparison. -/
@[ega "0 1.5.2" "partial"]
theorem locRestrictScalarsEquiv_fLoc (d : M →ₗ[B] N) (d' : M →ₗ[A] N) (hd : ∀ x, d' x = d x)
    (x : EtaPow.Loc c M) :
    locRestrictScalarsEquiv (B := B) c N (EtaPow.fLoc c d' x) =
      EtaPow.fLoc (algebraMap A B c) d (locRestrictScalarsEquiv (B := B) c M x) := by
  let j : EtaPow.Loc c M →ₗ[A] EtaPow.Loc (algebraMap A B c) N :=
    (locRestrictScalarsEquiv (B := B) c N).toLinearMap ∘ₗ EtaPow.fLoc c d'
  let k : EtaPow.Loc c M →ₗ[A] EtaPow.Loc (algebraMap A B c) N :=
    (EtaPow.fLoc (algebraMap A B c) d).restrictScalars A ∘ₗ
      (locRestrictScalarsEquiv (B := B) c M).toLinearMap
  have hjk : j = k := by
    refine IsLocalizedModule.ext (Submonoid.powers c)
      (LocalizedModule.mkLinearMap (Submonoid.powers c) M)
      (isUnit_algebraMap_loc c N) (LinearMap.ext fun m => ?_)
    change locRestrictScalarsEquiv (B := B) c N (EtaPow.fLoc c d' (EtaPow.toLoc c M m)) =
      EtaPow.fLoc (algebraMap A B c) d (locRestrictScalarsEquiv (B := B) c M (EtaPow.toLoc c M m))
    rw [EtaPow.fLoc_toLoc, locRestrictScalarsEquiv_toLoc, locRestrictScalarsEquiv_toLoc,
      EtaPow.fLoc_toLoc, hd]
  exact LinearMap.congr_fun hjk x

/-- A natural power of the unit `f ∈ R_f` acts on `M_f` as the same power of the scalar `f`. -/
private theorem awayUnit_natPow_smul {R : Type u} [CommRing R] (f : R) {P : Type u}
    [AddCommGroup P] [Module R P] (n : ℕ) (x : EtaPow.Loc f P) :
    (Stacks.GradedLaurent.awayUnit f ^ (n : ℤ)) • x = f ^ n • x := by
  rw [zpow_natCast]
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', mul_smul, ih, EtaPow.fUnit_units_smul, ← mul_smul, ← pow_succ']

variable (M) in
/-- **The comparison of localizations intertwines the integer powers of the two units.** -/
theorem locRestrictScalarsEquiv_zpow_smul (i : ℤ) (x : EtaPow.Loc c M) :
    locRestrictScalarsEquiv (B := B) c M ((Stacks.GradedLaurent.awayUnit c ^ i) • x) =
      (Stacks.GradedLaurent.awayUnit (algebraMap A B c) ^ i) •
        locRestrictScalarsEquiv (B := B) c M x := by
  have hnat : ∀ (n : ℕ) (x : EtaPow.Loc c M),
      locRestrictScalarsEquiv (B := B) c M ((Stacks.GradedLaurent.awayUnit c ^ (n : ℤ)) • x) =
        (Stacks.GradedLaurent.awayUnit (algebraMap A B c) ^ (n : ℤ)) •
          locRestrictScalarsEquiv (B := B) c M x := fun n x => by
    rw [awayUnit_natPow_smul, awayUnit_natPow_smul, map_smul, ← map_pow, algebraMap_smul]
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg i
  · exact hnat n x
  · have key := hnat n ((Stacks.GradedLaurent.awayUnit c ^ (-(n : ℤ))) • x)
    rw [EtaPow.fUnit_zpow_smul_smul, add_neg_cancel, zpow_zero, one_smul] at key
    rw [key, EtaPow.fUnit_zpow_smul_smul, neg_add_cancel, zpow_zero, one_smul]

/-- The comparison of localizations maps the submodule `cⁱ M` onto the submodule `cⁱ M`. -/
theorem mem_fpowSub_locRestrictScalarsEquiv_iff (i : ℤ) (x : EtaPow.Loc c M) :
    locRestrictScalarsEquiv (B := B) c M x ∈ EtaPow.fpowSub (algebraMap A B c) M i ↔
      x ∈ EtaPow.fpowSub c M i := by
  rw [EtaPow.mem_fpowSub, EtaPow.mem_fpowSub]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, (locRestrictScalarsEquiv (B := B) c M).injective ?_⟩
    rw [locRestrictScalarsEquiv_zpow_smul, locRestrictScalarsEquiv_toLoc, hm]
  · rintro ⟨m, rfl⟩
    exact ⟨m, by rw [locRestrictScalarsEquiv_zpow_smul, locRestrictScalarsEquiv_toLoc]⟩

/-- The comparison of localizations maps the décalage term of `d'` with respect to `c` onto the
décalage term of `d` with respect to the image of `c`. -/
theorem mem_fetaTerm_locRestrictScalarsEquiv_iff (d : M →ₗ[B] N) (d' : M →ₗ[A] N)
    (hd : ∀ x, d' x = d x) (i : ℤ) (x : EtaPow.Loc c M) :
    locRestrictScalarsEquiv (B := B) c M x ∈ EtaPow.fetaTerm (algebraMap A B c) d i ↔
      x ∈ EtaPow.fetaTerm c d' i := by
  rw [EtaPow.mem_fetaTerm, EtaPow.mem_fetaTerm, mem_fpowSub_locRestrictScalarsEquiv_iff,
    ← locRestrictScalarsEquiv_fLoc c d d' hd, mem_fpowSub_locRestrictScalarsEquiv_iff]

end Module

section Complex

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (c : A)

/-- Restriction of scalars from `B` to `A`, on complexes. -/
abbrev restrictScalarsComplex : CochainComplex (ModuleCat.{u} B) ℤ ⥤
    CochainComplex (ModuleCat.{u} A) ℤ :=
  (ModuleCat.restrictScalars (algebraMap A B)).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The restriction of scalars to `A` of a `B`-module `N`, with its `B`-module structure, is a
scalar tower over `A` and `B`. -/
instance isScalarTower_restrictScalars (N : ModuleCat.{u} B) :
    IsScalarTower A B ((ModuleCat.restrictScalars (algebraMap A B)).obj N) where
  smul_assoc a b x := by
    rw [Algebra.smul_def, mul_smul]
    rfl

/-- Each term of the restriction of scalars to `A` of a complex of `B`-modules is a `B`-module. -/
instance (C : CochainComplex (ModuleCat.{u} B) ℤ) (i : ℤ) :
    Module B (((restrictScalarsComplex (A := A)).obj C).X i) :=
  inferInstanceAs (Module B (C.X i))

/-- Each term of the restriction of scalars to `A` of a complex of `B`-modules is a scalar tower
over `A` and `B`. -/
instance (C : CochainComplex (ModuleCat.{u} B) ℤ) (i : ℤ) :
    IsScalarTower A B (((restrictScalarsComplex (A := A)).obj C).X i) :=
  isScalarTower_restrictScalars (C.X i)

/-- The differential of a complex of `B`-modules, read between the terms of its restriction of
scalars. -/
abbrev restrictedD (C : CochainComplex (ModuleCat.{u} B) ℤ) (i : ℤ) :
    ((restrictScalarsComplex (A := A)).obj C).X i →ₗ[B]
      ((restrictScalarsComplex (A := A)).obj C).X (i + 1) :=
  (C.d i (i + 1)).hom

/-- **The décalage terms of a complex and of its restriction of scalars agree.** -/
def etaTermRestrictScalarsEquiv (C : CochainComplex (ModuleCat.{u} B) ℤ) (i : ℤ) :
    term c ((restrictScalarsComplex (A := A)).obj C) i ≃ₗ[A]
      (ModuleCat.restrictScalars (algebraMap A B)).obj
        (ModuleCat.of B (term (algebraMap A B c) C i)) where
  toFun x := ⟨locRestrictScalarsEquiv (B := B) c
      (((restrictScalarsComplex (A := A)).obj C).X i) x.1,
    (mem_fetaTerm_locRestrictScalarsEquiv_iff c (restrictedD (A := A) C i)
      ((restrictScalarsComplex (A := A)).obj C |>.d i (i + 1)).hom (fun _ => rfl) i x.1).mpr x.2⟩
  invFun y := ⟨(locRestrictScalarsEquiv (B := B) c
      (((restrictScalarsComplex (A := A)).obj C).X i)).symm
      (show term (algebraMap A B c) C i from y).1, by
    refine (mem_fetaTerm_locRestrictScalarsEquiv_iff c (restrictedD (A := A) C i)
      ((restrictScalarsComplex (A := A)).obj C |>.d i (i + 1)).hom (fun _ => rfl) i _).mp ?_
    exact (congrArg (fun z => z ∈ EtaPow.fetaTerm (algebraMap A B c) (restrictedD (A := A) C i) i)
      (LinearEquiv.apply_symm_apply _ (show term (algebraMap A B c) C i from y).1)).mpr
        (show term (algebraMap A B c) C i from y).2⟩
  left_inv x := Subtype.ext (LinearEquiv.symm_apply_apply _ _)
  right_inv y := Subtype.ext (LinearEquiv.apply_symm_apply _ _)
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' a x := Subtype.ext
    (((locRestrictScalarsEquiv (B := B) c (((restrictScalarsComplex (A := A)).obj C).X i)).map_smul
      a x.1).trans (algebraMap_smul B a _).symm)

/-- **The décalage commutes with restriction of scalars.**  For an `A`-algebra `B`, `c ∈ A` and a
complex `C^•` of `B`-modules, the décalage with respect to `c` of `C^•` read over `A` is the
décalage with respect to the image of `c` of `C^•`, read over `A`. -/
def etaObjectRestrictScalarsIso (C : CochainComplex (ModuleCat.{u} B) ℤ) :
    etaObject c ((restrictScalarsComplex (A := A)).obj C) ≅
      (restrictScalarsComplex (A := A)).obj (etaObject (algebraMap A B c) C) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (etaTermRestrictScalarsEquiv c C i).toModuleIso) (by
      intro i j (hij : i + 1 = j)
      subst hij
      rw [etaObject_d, Functor.mapHomologicalComplex_obj_d, etaObject_d]
      ext x
      apply Subtype.ext
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
      exact (etaDifferential_val _ _ _ _).trans
        ((locRestrictScalarsEquiv_fLoc c (restrictedD (A := A) C i)
          ((restrictScalarsComplex (A := A)).obj C |>.d i (i + 1)).hom (fun _ => rfl)
          x.1).symm.trans
          (congrArg (locRestrictScalarsEquiv (B := B) c
            (((restrictScalarsComplex (A := A)).obj C).X (i + 1)))
            (etaDifferential_val _ _ _ _).symm)))

end Complex

end EtaComplex

end
