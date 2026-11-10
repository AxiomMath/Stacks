module

public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionCorrespondence
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeProperties
public import StacksFrontier.AlgebraicGeometry.SectionExtension.Nilpotent

/-!
# The zero scheme of a power of a section is the power of its zero scheme

Let `X` be a scheme, `L` an invertible `𝒪_X`-module and `s` a global section of `L^{⊗ m}`. The
`k`-th power `s^k` is a global section of `L^{⊗ (m k)}`, and its zero scheme is cut out by the
`k`-th power of the ideal of the zero scheme of `s`:

`Z(s^k) = Z(s)^k` as quasi-coherent ideal sheaves.

The powers of sections are the sectionwise ones, `Stacks.SheafOfModules.Invertible.sectionPow'`.

## Main definitions

* `Stacks.SheafOfModules.Invertible.sectionPowOverGenerator`: the `k`-th power of a local
  generator of `L^{⊗ m}`, again a local generator, of `L^{⊗ (m k)}`.
* `Stacks.SheafOfModules.Invertible.sectionsDegreeOne`: a global section of `L` read as a global
  section of `L^{⊗ 1}`, which is the degree the sectionwise powers are indexed from.

## Main results

* `AlgebraicGeometry.zeroScheme_pow_eq_of_cover`: `Z(t) = Z(s)^n` whenever `X` is covered by
  affine opens on which `s` is a generator times `a` and `t` is a generator times `a ^ n`.
* `AlgebraicGeometry.zeroScheme_eval_sectionPow'`: **`Z(s^k) = Z(s)^k`** for a global section `s`
  of `L^{⊗ m}`.
* `AlgebraicGeometry.zeroScheme_sectionPow'_degreeOne`: the same for a global section of `L`
  itself, through `sectionsDegreeOne`.

## References

* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules.Invertible

variable {X : RingedSpace.{u, u}} (L : _root_.SheafOfModules.{u} (structureSheafRing X))
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
    (structureSheafRing X).property L]

local notation "Lpow[" n "]" => tensorPowerModule' L ((n : ℕ) : ℤ)

/-- The product of a local generator of `L^{⊗ a}` and one of `L^{⊗ b}`, a local generator of
`L^{⊗ (a + b)}`: the elementary tensor of the two, read through the multiplication isomorphism. -/
def sectionMulOverGenerator (a b : ℕ) (U : Opens X.carrier)
    (g : GeneratorSections X Lpow[a] U) (w : GeneratorSections X Lpow[b] U) :
    GeneratorSections X Lpow[a + b] U :=
  generatorMapIso (tensorSheafPowerMulIso' L a b) U (tmulGenerator g w)

/-- The product of two local generators is the sectionwise product of their sections. -/
theorem sectionMulOverGenerator_val (a b : ℕ) (U : Opens X.carrier)
    (g : GeneratorSections X Lpow[a] U) (w : GeneratorSections X Lpow[b] U) :
    (sectionMulOverGenerator L a b U g w).val = sectionMulOver L a b (op U) g.val w.val := rfl

/-- The `k`-th power of a local generator of `L^{⊗ m}`, a local generator of `L^{⊗ (m k)}`. -/
def sectionPowOverGenerator {m : ℕ} (U : Opens X.carrier) (g : GeneratorSections X Lpow[m] U) :
    (k : ℕ) → GeneratorSections X Lpow[m * k] U
  | 0 => generatorOfIso Lpow[0] (Iso.refl _)
  | k + 1 => sectionMulOverGenerator L (m * k) m U (sectionPowOverGenerator U g k) g

/-- The `k`-th power of a local generator is the `k`-th sectionwise power of its section. -/
theorem sectionPowOverGenerator_val {m : ℕ} (U : Opens X.carrier)
    (g : GeneratorSections X Lpow[m] U) (k : ℕ) :
    (sectionPowOverGenerator L U g k).val = sectionPowOver L (op U) g.val k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change sectionMulOver L (m * k) m (op U) (sectionPowOverGenerator L U g k).val g.val = _
      rw [ih, sectionPowOver_succ]

/-- Multiplication by the section of a local generator is bijective on its open. -/
private theorem bijective_smul_generator_val {N : _root_.SheafOfModules.{u} (structureSheafRing X)}
    (U : Opens X.carrier) (g : GeneratorSections X N U) :
    Function.Bijective (fun r : X.presheaf.obj (op U) => r • g.val) := by
  have h := g.property U le_rfl
  rwa [generator_restrict_self N U g] at h

/-- **A power of a local generator generates**: multiplication by the `k`-th sectionwise power of
a generator of `L^{⊗ m}` is bijective on the sections of `L^{⊗ (m k)}`. -/
theorem bijective_smul_sectionPowOver {m : ℕ} (U : Opens X.carrier)
    (g : GeneratorSections X Lpow[m] U) (k : ℕ) :
    Function.Bijective
      (fun r : X.presheaf.obj (op U) => r • sectionPowOver L (op U) g.val k) := by
  simpa only [sectionPowOverGenerator_val] using
    bijective_smul_generator_val U (sectionPowOverGenerator L U g k)

/-- A global section of `L` read as a global section of `L^{⊗ 1}`, the degree from which the
sectionwise powers of a section of `L` are taken. -/
def sectionsDegreeOne (s : L.val.obj (op ⊤)) : Lpow[1].sections :=
  _root_.SheafOfModules.sectionsMap (tensorPowerOneIso X.presheaf
    (structureSheafRing X).property L).inv (sectionsOfTop L s)

/-- Reading a global section of `L` in degree one and back recovers it. -/
theorem app_tensorPowerOneIso_sectionsDegreeOne (s : L.val.obj (op ⊤)) :
    ((tensorPowerOneIso X.presheaf (structureSheafRing X).property L).hom.val.app (op ⊤))
        ((sectionsDegreeOne L s).eval (op ⊤)) = s := by
  set e := tensorPowerOneIso X.presheaf (structureSheafRing X).property L
  have hcomp : e.inv.val.app (op ⊤) ≫ e.hom.val.app (op ⊤) = CategoryStruct.id _ :=
    congrArg (fun φ => φ.val.app (op ⊤)) e.inv_hom_id
  have heval : (sectionsDegreeOne L s).eval (op ⊤) =
      (e.inv.val.app (op ⊤)) ((sectionsOfTop L s).eval (op ⊤)) := rfl
  rw [heval, sectionsOfTop_eval_top]
  exact ConcreteCategory.congr_hom hcomp s

end Stacks.SheafOfModules.Invertible

namespace AlgebraicGeometry

open Stacks.SheafOfModules Stacks.SheafOfModules.Invertible

/-- An invertible module in the spelling whose presheaf of rings is written
`X.toRingedSpace.presheaf` is invertible in the spelling written `X.sheaf.obj`. -/
instance isInvertible_sheafObj_of_isInvertible_toRingedSpace {X : Scheme.{u}}
    (L : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    [h : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L := h

/-- Every tensor power of an invertible module on a scheme is invertible in the spelling whose
presheaf of rings is written `X.sheaf.obj`. -/
instance isInvertible_sheafObj_tensorPowerModule' {X : Scheme.{u}}
    (L : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L] (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (tensorPowerModule' L n) :=
  tensorPower_isInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L n

/-- **The local equation of the zero scheme at a local generator.** On an affine open where the
section is the coefficient `a` times a generator of the invertible module, the defining ideal of
the zero scheme is generated by `a`. -/
theorem zeroScheme_ideal_eq_span_singleton_of_bijective_smul (X : Scheme.{u}) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (U : X.affineOpens) (g : Γ(L, U.1))
    (hg : Function.Bijective (fun c : Γ(X, U.1) => c • g)) (a : Γ(X, U.1))
    (hs : L.presheaf.map (homOfLE le_top).op s = a • g) :
    (zeroScheme X L s).ideal U = Ideal.span ({a} : Set Γ(X, U.1)) :=
  let e := LinearEquiv.ofBijective (LinearMap.toSpanSingleton Γ(X, U.1) Γ(L, U.1) g) hg
  zeroScheme_ideal_of_trivialization X L s U e.symm a (by rw [hs]; exact e.symm_apply_apply a)

/-- **The zero scheme of a locally `n`-th power is the `n`-th power of a zero scheme.** If `X` is
covered by affine opens on which `s` is `a` times a generator of `L` and `t` is `a ^ n` times a
generator of `M`, then `Z(t) = Z(s)^n`. -/
theorem zeroScheme_pow_eq_of_cover {X : Scheme.{u}} (L M : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    (s : Γ(L, ⊤)) (t : Γ(M, ⊤)) (n : ℕ) {ι : Type*} (U : ι → X.affineOpens)
    (hU : ⨆ i, (U i).1 = ⊤)
    (h : ∀ i, ∃ (g : Γ(L, (U i).1)) (w : Γ(M, (U i).1)) (a : Γ(X, (U i).1)),
      Function.Bijective (fun r : Γ(X, (U i).1) => r • g) ∧
      Function.Bijective (fun r : Γ(X, (U i).1) => r • w) ∧
      L.presheaf.map (homOfLE le_top).op s = a • g ∧
      M.presheaf.map (homOfLE le_top).op t = a ^ n • w) :
    zeroScheme X M t = zeroScheme X L s ^ n := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top U hU fun i => ?_
  obtain ⟨g, w, a, hg, hw, hsa, hta⟩ := h i
  rw [zeroScheme_ideal_eq_span_singleton_of_bijective_smul X M t (U i) w hw (a ^ n) hta,
    show (zeroScheme X L s ^ n).ideal (U i) = (zeroScheme X L s).ideal (U i) ^ n from rfl,
    zeroScheme_ideal_eq_span_singleton_of_bijective_smul X L s (U i) g hg a hsa,
    Ideal.span_singleton_pow]

/-- Every point of a scheme lies in an affine open carrying a local generator of a given
invertible module. -/
theorem exists_affineOpens_generator {X : Scheme.{u}}
    (L : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L] (x : X) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ Nonempty (GeneratorSections X.toRingedSpace L U.1) := by
  have hLinv : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L := isInvertible_of_tensorInvertible L
  obtain ⟨W, hxW, a, ha⟩ := exists_bijective_smul_of_isInvertible L x
  obtain ⟨V, hVaff, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset hxW
  exact ⟨⟨V, hVaff⟩, hxV, ⟨generatorRestrict L (hVW : V ≤ W) ⟨a, fun V' h => ha V' h⟩⟩⟩

/-- **The zero scheme of a power of a section is the power of its zero scheme.** For a global
section `s` of `L^{⊗ m}` with `L` invertible, the zero scheme of the `k`-th sectionwise power
`s^k`, a global section of `L^{⊗ (m k)}`, is cut out by the `k`-th power of the ideal of the zero
scheme of `s`. -/
theorem zeroScheme_eval_sectionPow' {X : Scheme.{u}}
    (L : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    {m : ℕ} (s : (tensorPowerModule' L ((m : ℕ) : ℤ)).sections) (k : ℕ) :
    zeroScheme X (tensorPowerModule' L ((m * k : ℕ) : ℤ)) ((sectionPow' L s k).eval (op ⊤))
      = zeroScheme X (tensorPowerModule' L ((m : ℕ) : ℤ)) (s.eval (op ⊤)) ^ k := by
  classical
  choose U hxU hgen using exists_affineOpens_generator L
  have hUtop : ⨆ x : X, (U x).1 = ⊤ :=
    le_antisymm le_top fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hxU y⟩
  refine zeroScheme_pow_eq_of_cover (tensorPowerModule' L ((m : ℕ) : ℤ))
    (tensorPowerModule' L ((m * k : ℕ) : ℤ)) (s.eval (op ⊤)) ((sectionPow' L s k).eval (op ⊤))
    k U hUtop fun x => ?_
  set V : X.Opens := (U x).1
  let g : GeneratorSections X.toRingedSpace (tensorPowerModule' L ((m : ℕ) : ℤ)) V :=
    tensorPowerGenerator L (hgen x).some m
  have hbij := bijective_smul_generator_val V g
  obtain ⟨a, ha⟩ : ∃ a : Γ(X, V), s.eval (op V) = a • g.val :=
    (hbij.surjective (s.eval (op V))).imp fun _ h => h.symm
  have hkey : sectionPowOver L (op V) (s.eval (op V)) k
      = a ^ k • sectionPowOver L (op V) g.val k := by
    rw [ha, sectionPowOver_smul]
  refine ⟨g.val, sectionPowOver L (op V) g.val k, a, hbij,
    bijective_smul_sectionPowOver L V g k, ?_, ?_⟩
  · exact (PresheafOfModules.sections_property s (homOfLE (le_top (a := V))).op).trans ha
  · exact (PresheafOfModules.sections_property (sectionPow' L s k)
      (homOfLE (le_top (a := V))).op).trans ((eval_sectionPow' L s (op V) k).trans hkey)

/-- **The zero scheme of a power of a section of an invertible module itself.** For a global
section `s` of `L`, read in degree one by `sectionsDegreeOne`, the zero scheme of its `k`-th
sectionwise power is cut out by the `k`-th power of the ideal of `Z(s)`. -/
theorem zeroScheme_sectionPow'_degreeOne {X : Scheme.{u}}
    (L : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L] (s : Γ(L, ⊤)) (k : ℕ) :
    zeroScheme X (tensorPowerModule' L ((1 * k : ℕ) : ℤ))
        ((sectionPow' L (sectionsDegreeOne L s) k).eval (op ⊤))
      = zeroScheme X L s ^ k :=
  (zeroScheme_eval_sectionPow' L (sectionsDegreeOne L s) k).trans <|
    congrArg (fun I : X.IdealSheafData => I ^ k) <| zeroScheme_eq_of_iso
      (tensorPowerOneIso X.presheaf (structureSheafRing X.toRingedSpace).property L)
      (app_tensorPowerOneIso_sectionsDegreeOne L s)

end AlgebraicGeometry

end
