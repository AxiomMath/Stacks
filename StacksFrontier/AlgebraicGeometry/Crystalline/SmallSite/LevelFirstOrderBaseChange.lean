module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelThickeningRingHom

/-!
# `Ω ⊗_D Γ(T_e, ℱ) = Γ(T_e, Ω) ⊗_{Γ(T_e, 𝒪)} Γ(T_e, ℱ)`, and the base change of a crystal

Two of the five unconstructed fields of
`Crystalline.GlobalCrystallineSituation.SmallSite.LevelReduction07JG` are the base change

`Θ_e : (D ⊕ Ω) ⊗_D M ⟶ Γ(T'_e, ℱ)`,  `b ⊗ m ↦ ψ_e(b) · p₀^* m`,

and its value on a pure tensor.  The map itself needs only the ring map `ψ_e` of the level, which
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/LevelThickeningRingHom.lean` constructs; what
the datum of [Stacks, Lemma 60.17.3, Tag 07JG] runs on is that it is **bijective**, because the
comparison map of a crystal at the level is the restriction `p₁^* s` read back through it.

This module proves that bijectivity, from two inputs, and the first of them is the identification
the tree did not have:

`Ω ⊗_D Γ(T_e, ℱ) ≅ Γ(T_e, Ω_{T_e/S,δ}) ⊗_{Γ(T_e, 𝒪)} Γ(T_e, ℱ)`.

Everything the site offers about a crystal at the object `T_e` is stated over the level's own ring
`Γ(T_e, 𝒪)` and its own differentials; the datum of the tag is stated over `D` and `Ω`.  The
identification is what crosses between them, and it is
`...SmallSite.LevelForms07JG.levelOmegaTensorEquiv`.  It costs exactly one hypothesis: that the
reduction `Ω ⟶ Γ(T_e, Ω_{T_e/S,δ})` of `...SmallSite.LevelForms07JG.omegaMap` carries a basis of
`Ω` over `D` to a basis of the differentials of the level over `Γ(T_e, 𝒪)` — the statement that
the differentials of the level are the base change of `Ω`.  The algebra is
`Stacks.TensorProduct.semilinearBasisTensorEquiv`, and no finiteness of the index is used for it.

Applied to `D ⊕ Ω` instead of `Ω` — the two bases being the unit together with the basis of the
square-zero summand, on both sides — the same lemma identifies the algebraic base change with the
geometric one,

`(D ⊕ Ω) ⊗_D Γ(T_e, ℱ) ≅ Γ(T'_e, 𝒪_{T'_e}) ⊗_{Γ(T_e, 𝒪)} Γ(T_e, ℱ)`,

so `Θ_e` factors through `...SmallSite.crysExtensionSectionsMap` and is bijective exactly when
that base change of scalars is.  That second input is the affine content of
[Stacks, Tag 07J6] and **this module does not prove it**.

## Main definitions

* `...SmallSite.LevelScalars07JG.levelExtensionSectionsMap` and
  `...LevelScalars07JG.levelSectionsP₀` — the base change of scalars and the restriction along
  `p₀` at a level, written over the type synonym
  `...SmallSite.LevelScalars07JG.levelSections`.
* `...SmallSite.LevelForms07JG.levelOmegaTensorEquiv` — **the tensor identification of the
  differentials.**
* `...SmallSite.LevelForms07JG.levelRingTensorMap` — the comparison of the algebraic base change
  along `D ⊕ Ω` with the geometric one along `p₀`.
* `...SmallSite.LevelForms07JG.levelBaseChange` — **the base change `Θ_e`**, the field
  `...SmallSite.LevelReduction07JG.baseChange` at one level.

## Main results

* `...SmallSite.LevelForms07JG.crysFirstOrderSectionsBasis_eq` — the ring map of the level carries
  the basis of `D ⊕ Ω` to the basis of `Γ(T'_e, 𝒪_{T'_e})`.
* `...SmallSite.LevelForms07JG.bijective_levelRingTensorMap` — the comparison of the two base
  changes is an isomorphism.
* `...SmallSite.LevelForms07JG.levelBaseChange_eq` — `Θ_e` factors as the base change of scalars
  after that comparison.
* `...SmallSite.LevelForms07JG.bijective_levelBaseChange` — **`Θ_e` is bijective**, from the
  tensor identification and bijectivity of the base change of scalars at the level.

## What is and is not proved

**No `@[stacks]` attribute is placed and no tag is proved.**  Bijectivity of
`...SmallSite.crysExtensionSectionsMap` at a level is carried, and it is a genuine input: it is
the small-site form of the global-sections statement that
`StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderIdealAffine.lean` reduces
[Stacks, Tag 07J6] to on the big site, where
`...GlobalCrystallineSituation.bijective_firstOrderSectionsMap_iff_bijective_extensionSectionsMap`
shows it equivalent to bijectivity of
`...GlobalCrystallineSituation.firstOrderSectionsMap`.  It is false on a general object — the ℙ¹
counterexample is recorded in the module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderIdealSheaf.lean` — and the reason it is an
affine question at the levels of [Stacks, Proposition 60.21.1, Tag 07JN] is that every level of
`...SmallSite.wholeSpaceSystem` is affine, by
`...SmallSite.isAffine_wholeSpaceSystem_target`.

The two statements are written for the same ring, the same first-order thickening and the same two
restriction maps; what separates them is only that one is read on a sheaf of modules on
`Cris(X/S)` and the other on a sheaf of modules on `CRIS(X/S)`.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07J9](https://stacks.math.columbia.edu/tag/07J9)
* [Stacks Project, Proposition 60.21.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct

universe u uI

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} {A : Type u} [CommRing A]
  {D : DividedPowerRing.{u}} {g : A →+* D} {Omega : Type u} [AddCommGroup Omega]
  [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
  {d : DividedPowerDerivation A D g Omega} {ι : Type uI}

/-! ### The two spellings of the scalars on the sections over a level -/

/-- The sections of a crystal over a level, as a module over the section ring of that level in
the big-site spelling `Crystalline.GlobalCrystallineSituation.crysSheafRing`, which is the one
that carries a `CommRing` instance. -/
instance instModuleCrysLevelSections (L : LevelScalars07JG S D) (F : QuasiCoherentCrystal S)
    (e : ℕ) :
    Module (crysSheafRing S (L.levelSystem.obj e).obj) (L.levelSections F e) :=
  inferInstanceAs (Module ((structureSheaf S).obj.obj (op (L.levelSystem.obj e)))
    (L.levelSections F e))

/-- **The base change of the sections of a crystal over a level along `p₀`**, the map of
`...SmallSite.crysExtensionSectionsMap` written over the type synonym
`...SmallSite.LevelScalars07JG.levelSections`.  It is the same map. -/
abbrev LevelScalars07JG.levelExtensionSectionsMap (L : LevelScalars07JG S D)
    (F : QuasiCoherentCrystal S) (e : ℕ) :
    crysSheafRing S (firstOrderThickeningObject S (L.levelSystem.obj e).obj)
        ⊗[crysSheafRing S (L.levelSystem.obj e).obj] L.levelSections F e →+
      F.obj.val.obj (op (firstOrderThickeningCrysObject S (L.levelSystem.obj e))) :=
  crysExtensionSectionsMap F.obj (L.levelSystem.obj e)

/-- **The restriction along `p₀` of the sections of a crystal over a level**, written over the
type synonym `...SmallSite.LevelScalars07JG.levelSections`.  It is
`...SmallSite.crysSectionsP₀`. -/
abbrev LevelScalars07JG.levelSectionsP₀ (L : LevelScalars07JG S D) (F : QuasiCoherentCrystal S)
    (e : ℕ) :
    L.levelSections F e →
      F.obj.val.obj (op (firstOrderThickeningCrysObject S (L.levelSystem.obj e))) :=
  crysSectionsP₀ F.obj (L.levelSystem.obj e)

/-- The restriction along `p₀` of the sections of a crystal over a level is additive. -/
theorem LevelScalars07JG.levelSectionsP₀_add (L : LevelScalars07JG S D)
    (F : QuasiCoherentCrystal S) (e : ℕ) (m m' : L.levelSections F e) :
    L.levelSectionsP₀ F e (m + m') = L.levelSectionsP₀ F e m + L.levelSectionsP₀ F e m' :=
  crysSectionsP₀_add F.obj (L.levelSystem.obj e) m m'

/-- The restriction along `p₀` of the sections of a crystal over a level is semilinear for the
ring map `Γ(T_e, 𝒪) ⟶ Γ(T'_e, 𝒪_{T'_e})` induced by `p₀`. -/
theorem LevelScalars07JG.levelSectionsP₀_smul (L : LevelScalars07JG S D)
    (F : QuasiCoherentCrystal S) (e : ℕ) (a : crysSheafRing S (L.levelSystem.obj e).obj)
    (m : L.levelSections F e) :
    L.levelSectionsP₀ F e (a • m) =
      crysSheafRingMap (firstOrderThickeningSiteP₀ S (L.levelSystem.obj e).obj) a •
        L.levelSectionsP₀ F e m :=
  crysSectionsP₀_smul F.obj (L.levelSystem.obj e) a m

/-! ### The tensor identification of the differentials -/

namespace LevelForms07JG

variable {L : LevelScalars07JG S D} (R : LevelForms07JG S A D g Omega d L)

/-- **The identification `Ω ⊗_D Γ(T_e, ℱ) ≅ Γ(T_e, Ω_{T_e/S,δ}) ⊗_{Γ(T_e, 𝒪)} Γ(T_e, ℱ)`.**

This is the step that reads the comparison datum of a crystal at a level — which the site gives
over the level's own ring `Γ(T_e, 𝒪)` and its own differentials `Γ(T_e, Ω_{T_e/S,δ})` — over the
ring `D` and the module `Ω` of [Stacks, Lemma 60.17.3, Tag 07JG].

It costs exactly one hypothesis: that the reduction `Ω ⟶ Γ(T_e, Ω_{T_e/S,δ})` of
`...SmallSite.LevelForms07JG.omegaMap` carries a basis of `Ω` over `D` to a basis of the
differentials of the level over `Γ(T_e, 𝒪)`, which is the statement that the differentials of the
level are the base change of `Ω`.  No finiteness of the index is used here; see
`Stacks.TensorProduct.semilinearBasisTensorEquiv`. -/
def levelOmegaTensorEquiv (F : QuasiCoherentCrystal S) (e : ℕ)
    (b : Module.Basis ι (D : Type u) Omega)
    (cw : Module.Basis ι (crysSheafRing S (L.levelSystem.obj e).obj)
      (crysDiffSections (L.levelSystem.obj e).obj))
    (hcw : ∀ i, cw i = R.omegaMap e (b i)) :
    Omega ⊗[(D : Type u)] L.levelSections F e ≃+
      crysDiffSections (L.levelSystem.obj e).obj
        ⊗[crysSheafRing S (L.levelSystem.obj e).obj] L.levelSections F e :=
  Stacks.TensorProduct.semilinearBasisTensorEquiv (u := R.omegaMap e) b cw (R.omegaMap_smul e)
    (fun _ _ ↦ rfl) hcw

/-- The identification `...SmallSite.LevelForms07JG.levelOmegaTensorEquiv` sends `w ⊗ m` to the
reduction of `w` tensored with `m`. -/
@[simp] theorem levelOmegaTensorEquiv_tmul (F : QuasiCoherentCrystal S) (e : ℕ)
    (b : Module.Basis ι (D : Type u) Omega)
    (cw : Module.Basis ι (crysSheafRing S (L.levelSystem.obj e).obj)
      (crysDiffSections (L.levelSystem.obj e).obj))
    (hcw : ∀ i, cw i = R.omegaMap e (b i)) (w : Omega) (m : L.levelSections F e) :
    R.levelOmegaTensorEquiv F e b cw hcw (w ⊗ₜ[(D : Type u)] m) =
      R.omegaMap e w ⊗ₜ[crysSheafRing S (L.levelSystem.obj e).obj] m :=
  rfl

/-! ### The same identification for the whole first-order thickening -/

/-- **The ring map of the level carries the basis of `D ⊕ Ω` to a basis of
`Γ(T'_e, 𝒪_{T'_e})`**, given that it carries the basis of `Ω` to a basis of the differentials of
the level: the two bases are the unit together with the basis of the square-zero summand, on both
sides. -/
theorem crysFirstOrderSectionsBasis_eq (e : ℕ) (b : Module.Basis ι (D : Type u) Omega)
    (cw : Module.Basis ι (crysSheafRing S (L.levelSystem.obj e).obj)
      (crysDiffSections (L.levelSystem.obj e).obj))
    (hcw : ∀ i, cw i = R.omegaMap e (b i)) (j : Unit ⊕ ι) :
    crysFirstOrderSectionsBasis (L.levelSystem.obj e).obj cw j =
      R.thickeningRingHom e (firstOrderExtensionBasis b j) := by
  cases j with
  | inl x => rw [crysFirstOrderSectionsBasis_inl, firstOrderExtensionBasis_inl, map_one]
  | inr i =>
      rw [crysFirstOrderSectionsBasis_inr, firstOrderExtensionBasis_inr, hcw i,
        thickeningRingHom_apply, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, map_zero,
        map_zero, zero_add]

/-- **The comparison of the algebraic base change with the geometric one**, the map

`(D ⊕ Ω) ⊗_D Γ(T_e, ℱ) ⟶ Γ(T'_e, 𝒪_{T'_e}) ⊗_{Γ(T_e, 𝒪)} Γ(T_e, ℱ)`,  `b ⊗ m ↦ ψ_e(b) ⊗ m`,

for `ψ_e` the ring map of the level.  No basis is needed to write it down. -/
def levelRingTensorMap (F : QuasiCoherentCrystal S) (e : ℕ) :
    firstOrderExtension D Omega ⊗[(D : Type u)] L.levelSections F e →+
      crysSheafRing S (firstOrderThickeningObject S (L.levelSystem.obj e).obj)
        ⊗[crysSheafRing S (L.levelSystem.obj e).obj] L.levelSections F e :=
  Stacks.TensorProduct.semilinearTensorMap (u := (R.thickeningRingHom e).toAddMonoidHom)
    (R.thickeningRingHom_smul e) (fun _ _ ↦ rfl)

/-- The comparison `...SmallSite.LevelForms07JG.levelRingTensorMap` sends `b ⊗ m` to
`ψ_e(b) ⊗ m`. -/
@[simp] theorem levelRingTensorMap_tmul (F : QuasiCoherentCrystal S) (e : ℕ)
    (b : firstOrderExtension D Omega) (m : L.levelSections F e) :
    R.levelRingTensorMap F e (b ⊗ₜ[(D : Type u)] m) =
      R.thickeningRingHom e b ⊗ₜ[crysSheafRing S (L.levelSystem.obj e).obj] m :=
  rfl

/-- **That comparison is an isomorphism.**  It is
`Stacks.TensorProduct.semilinearBasisTensorEquiv` for the basis of `D ⊕ Ω` of
`Crystalline.firstOrderExtensionBasis` and the basis of `Γ(T'_e, 𝒪_{T'_e})` of
`...SmallSite.crysFirstOrderSectionsBasis`, which the ring map of the level carries onto one
another by `...SmallSite.LevelForms07JG.crysFirstOrderSectionsBasis_eq`.

So the only content beyond the datum is the hypothesis `hcw`: the differentials of the level are
the base change of `Ω`. -/
theorem bijective_levelRingTensorMap (F : QuasiCoherentCrystal S) (e : ℕ)
    (b : Module.Basis ι (D : Type u) Omega)
    (cw : Module.Basis ι (crysSheafRing S (L.levelSystem.obj e).obj)
      (crysDiffSections (L.levelSystem.obj e).obj))
    (hcw : ∀ i, cw i = R.omegaMap e (b i)) :
    Function.Bijective (R.levelRingTensorMap F e) :=
  Stacks.TensorProduct.bijective_semilinearTensorMap (u := (R.thickeningRingHom e).toAddMonoidHom)
    (firstOrderExtensionBasis b) (crysFirstOrderSectionsBasis (L.levelSystem.obj e).obj cw)
    (R.thickeningRingHom_smul e) (fun _ _ ↦ rfl)
    (R.crysFirstOrderSectionsBasis_eq e b cw hcw)

/-! ### The base change of the sections of a crystal -/

/-- The bilinear datum of `...SmallSite.LevelForms07JG.levelBaseChange`. -/
def levelBaseChangeAux (F : QuasiCoherentCrystal S) (e : ℕ) :
    firstOrderExtension D Omega →+
      (L.levelSections F e →+
        F.obj.val.obj (op (firstOrderThickeningCrysObject S (L.levelSystem.obj e)))) :=
  AddMonoidHom.mk'
    (fun b ↦ AddMonoidHom.mk'
      (fun m ↦ R.thickeningRingHom e b • L.levelSectionsP₀ F e m)
      fun m m' ↦ by rw [L.levelSectionsP₀_add, smul_add])
    fun b b' ↦ by
      refine AddMonoidHom.ext fun m ↦ ?_
      show R.thickeningRingHom e (b + b') • L.levelSectionsP₀ F e m =
        R.thickeningRingHom e b • L.levelSectionsP₀ F e m +
          R.thickeningRingHom e b' • L.levelSectionsP₀ F e m
      rw [map_add, add_smul]

/-- **The base change of the sections of a crystal over the first-order thickening of a level**,
the map

`(D ⊕ Ω) ⊗_D Γ(T_e, ℱ) ⟶ Γ(T'_e, ℱ)`,  `b ⊗ m ↦ ψ_e(b) · p₀^* m`,

which is the field `...SmallSite.LevelReduction07JG.baseChange` at one level.  It is well defined
because the ring map of the level is semilinear for the reduction of `D`. -/
def levelBaseChange (F : QuasiCoherentCrystal S) (e : ℕ) :
    firstOrderExtension D Omega ⊗[(D : Type u)] L.levelSections F e →+
      F.obj.val.obj (op (firstOrderThickeningCrysObject S (L.levelSystem.obj e))) :=
  TensorProduct.liftAddHom (R.levelBaseChangeAux F e) fun a b m ↦ by
    change R.thickeningRingHom e (a • b) • L.levelSectionsP₀ F e m =
      R.thickeningRingHom e b • L.levelSectionsP₀ F e (a • m)
    rw [R.thickeningRingHom_smul, show (a • m : L.levelSections F e) =
        L.levelCrysRingHom e a • m from rfl, L.levelSectionsP₀_smul, crysSheafRing_smul_def,
      smul_smul, crysSheafRing_mul_comm]

/-- The base change `...SmallSite.LevelForms07JG.levelBaseChange` sends `b ⊗ m` to
`ψ_e(b) · p₀^* m`. -/
@[simp] theorem levelBaseChange_tmul (F : QuasiCoherentCrystal S) (e : ℕ)
    (b : firstOrderExtension D Omega) (m : L.levelSections F e) :
    R.levelBaseChange F e (b ⊗ₜ[(D : Type u)] m) =
      R.thickeningRingHom e b • L.levelSectionsP₀ F e m :=
  rfl

/-- **The base change factors through the geometric one.**  The algebraic base change along
`D ⊕ Ω` followed by the base change of scalars along `p₀` of
`...SmallSite.crysExtensionSectionsMap` is the map above; both send `b ⊗ m` to
`ψ_e(b) · p₀^* m`. -/
theorem levelBaseChange_eq (F : QuasiCoherentCrystal S) (e : ℕ)
    (z : firstOrderExtension D Omega ⊗[(D : Type u)] L.levelSections F e) :
    R.levelBaseChange F e z =
      L.levelExtensionSectionsMap F e (R.levelRingTensorMap F e z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul b m =>
      exact (crysExtensionSectionsMap_tmul F.obj (L.levelSystem.obj e)
        (R.thickeningRingHom e b) m).symm
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/-- **The base change of the sections over the first-order thickening of a level is bijective**,
given the two inputs it genuinely needs:

* `hcw`, that the differentials of the level are the base change of `Ω` — the tensor
  identification of `...SmallSite.LevelForms07JG.levelOmegaTensorEquiv`;
* `hext`, bijectivity of the base change of scalars along `p₀` at the level, which is the affine
  input of [Stacks, Tag 07J6] and is **proved nowhere in this module**.

Every level of `...SmallSite.wholeSpaceSystem` is affine, by
`...SmallSite.isAffine_wholeSpaceSystem_target`, which is what makes `hext` an affine question;
on the big crystalline site it is equivalent to bijectivity of
`Crystalline.GlobalCrystallineSituation.firstOrderSectionsMap`, by
`...GlobalCrystallineSituation.bijective_firstOrderSectionsMap_iff_bijective_extensionSectionsMap`.
-/
theorem bijective_levelBaseChange (F : QuasiCoherentCrystal S) (e : ℕ)
    (b : Module.Basis ι (D : Type u) Omega)
    (cw : Module.Basis ι (crysSheafRing S (L.levelSystem.obj e).obj)
      (crysDiffSections (L.levelSystem.obj e).obj))
    (hcw : ∀ i, cw i = R.omegaMap e (b i))
    (hext : Function.Bijective (L.levelExtensionSectionsMap F e)) :
    Function.Bijective (R.levelBaseChange F e) := by
  have hfun : (R.levelBaseChange F e : _ → _) =
      (L.levelExtensionSectionsMap F e) ∘ (R.levelRingTensorMap F e) :=
    funext fun z ↦ R.levelBaseChange_eq F e z
  rw [hfun]
  exact hext.comp (R.bijective_levelRingTensorMap F e b cw hcw)

end LevelForms07JG

end Crystalline.GlobalCrystallineSituation.SmallSite

end
