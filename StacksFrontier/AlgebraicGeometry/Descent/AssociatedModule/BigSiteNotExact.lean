module

public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
import StacksCore.Tactic.StacksAttribute

/-!
# `𝓕 ↦ 𝓕^a` is not exact on a big site

Descent, Lemma 06VE (6) says that the functor
`QCoh(𝒪_S) → Mod((Sch/S)_τ, 𝒪)`, `𝓕 ↦ 𝓕^a`, of Proposition 03DX is **not** exact in general.
It is right exact at every `τ` — that is clause (4), proved in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/Descent/BaseAssociatedModuleColimits.lean`
— so the content of clause (6) is that it fails to be *left* exact, and a faithful formalization
of it has to exhibit the failure.

This file does exactly what the source's proof does.  Take `S = Spec(ℤ)`.  Then
`2 : 𝒪_S → 𝒪_S` is injective, because every ring of sections of `𝒪_{Spec(ℤ)}` over a nonempty
open is a domain in which `2 ≠ 0`; but `Spec(𝔽₂)` is an object of `(Sch/S)_τ` for every `τ`, the
sections of `𝒪` there are `𝔽₂`, and `2 : 𝔽₂ → 𝔽₂` is not injective.  So the monomorphism
`2 : 𝒪_S → 𝒪_S` of `QCoh(𝒪_S)` is carried to a morphism of `Mod((Sch/S)_τ, 𝒪)` that is not a
monomorphism, and a functor preserving finite limits would preserve monomorphisms.

Nothing is assumed about the big site beyond its existence: the statements below hold for
**every** `B : AlgebraicGeometry.BigFppfSite` and **every** `τ : AlgebraicGeometry.SiteKind`,
`Spec(ℤ)` and `Spec(𝔽₂)` being small enough to lie in any of them
(`AlgebraicGeometry.BigFppfSite.aleph0_lt_cutoff`).

## Main definitions

* `AlgebraicGeometry.AssociatedModuleNotExact.specInt` and
  `AlgebraicGeometry.AssociatedModuleNotExact.specFTwo`: `Spec(ℤ)` and `Spec(𝔽₂)`, with the rings
  placed in the universe of the schemes of the site.
* `AlgebraicGeometry.AssociatedModuleNotExact.ftwoObject`: `Spec(𝔽₂) → Spec(ℤ)` as an object of
  `(Sch/Spec(ℤ))_τ`.
* `AlgebraicGeometry.AssociatedModuleNotExact.unitQcoh`: `𝒪_{Spec(ℤ)}` as an object of
  `QCoh(𝒪_{Spec(ℤ)})`.

## Main results

* `AlgebraicGeometry.AssociatedModuleNotExact.mono_two_nsmul_unitQcoh`: `2 : 𝒪_S → 𝒪_S` is a
  monomorphism of `QCoh(𝒪_S)` for `S = Spec(ℤ)`.
* `AlgebraicGeometry.AssociatedModuleNotExact.not_mono_map_two_nsmul_qcoh`: **Stacks 06VE (6),
  the witness** — its image under `𝓕 ↦ 𝓕^a` is not a monomorphism of `Mod((Sch/S)_τ, 𝒪)`, at
  every `τ` and on every big site.
* `AlgebraicGeometry.AssociatedModuleNotExact.not_preservesMonomorphisms_baseAssociatedModuleQcoh`
  and
  `AlgebraicGeometry.AssociatedModuleNotExact.not_preservesFiniteLimits_baseAssociatedModuleQcoh`:
  **Stacks 06VE (6)** — `𝓕 ↦ 𝓕^a` does not preserve monomorphisms, hence does not preserve
  finite limits, so it is not exact.

## Implementation notes

`𝒪_S^a = 𝒪` is `AlgebraicGeometry.BigFppfOver.isIso_basePullbackObjUnitToUnit`, and the sections
of `𝒪` over the object `Spec(𝔽₂) → Spec(ℤ)` are `Γ(Spec(𝔽₂), 𝒪)` on the nose
(`AlgebraicGeometry.FibredSite.baseRingStructureSheaf_obj` and
`AlgebraicGeometry.FibredSite.baseStructureSheaf_obj` are both `rfl`), which
`AlgebraicGeometry.Scheme.ΓSpecIso` identifies with `𝔽₂`.

The morphism "multiplication by `2`" is `2 • 𝟙`, the `ℕ`-action of the preadditive structure.
That the associated-module functor carries it to `2 • 𝟙` is additivity, which is not an instance
here and is supplied by `AlgebraicGeometry.AssociatedModuleNotExact.additive_associatedModule`:
the functor is a left adjoint
(`AlgebraicGeometry.BigFppfOver.isLeftAdjoint_baseAssociatedModule`), hence preserves binary
coproducts, hence binary biproducts, hence is additive.

The injectivity of `2` on `Γ(U, 𝒪_{Spec(ℤ)})` is read off integrality of `Spec(ℤ)`:
`AlgebraicGeometry.IsIntegral.component_integral` makes the sections over a nonempty open a
domain, `AlgebraicGeometry.map_injective_of_isIntegral` carries `2 ≠ 0` from the global sections
to them, and over the empty open the sections are subsingleton.

## References

* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AssociatedModuleNotExact

/-! ### The two schemes -/

/-- `Spec(ℤ)`, with `ℤ` placed in the universe of the schemes of a big site. -/
public def specInt : Scheme.{u} := Spec (.of (ULift.{u} ℤ))

/-- `Spec(𝔽₂)`, with `𝔽₂` placed in the universe of the schemes of a big site. -/
public def specFTwo : Scheme.{u} := Spec (.of (ULift.{u} (ZMod 2)))

/-- `Spec(ℤ)` lies in every big fppf site: its size is `ℵ₀`, below every cutoff. -/
public theorem contains_specInt (B : BigFppfSite.{u}) : B.Contains specInt.{u} := by
  rw [BigFppfSite.Contains, specInt, Scheme.size_Spec]
  refine max_lt B.aleph0_lt_cutoff ?_
  have h : Cardinal.mk ↥(CommRingCat.of (ULift.{u} ℤ)) = Cardinal.aleph0.{u} := by
    simp
  rw [h]
  exact B.aleph0_lt_cutoff

/-- `Spec(𝔽₂)` lies in every big fppf site: it is finite. -/
public theorem contains_specFTwo (B : BigFppfSite.{u}) : B.Contains specFTwo.{u} := by
  rw [BigFppfSite.Contains, specFTwo, Scheme.size_Spec]
  refine max_lt B.aleph0_lt_cutoff (lt_trans ?_ B.aleph0_lt_cutoff)
  exact Cardinal.lt_aleph0_of_finite _

/-- The reduction `ℤ → 𝔽₂`, between the universe-lifted rings. -/
public def intToFTwo : CommRingCat.of (ULift.{u} ℤ) ⟶ CommRingCat.of (ULift.{u} (ZMod 2)) :=
  CommRingCat.ofHom
    (((ULift.ringEquiv (R := ZMod 2)).symm : ZMod 2 →+* ULift.{u} (ZMod 2)).comp
      ((Int.castRingHom (ZMod 2)).comp (ULift.ringEquiv (R := ℤ) : ULift.{u} ℤ →+* ℤ)))

/-- `Spec(𝔽₂) → Spec(ℤ)`. -/
public def specFTwoOver : specFTwo.{u} ⟶ specInt.{u} := Spec.map intToFTwo.{u}

/-- `Spec(𝔽₂) → Spec(ℤ)` as an object of the big site over `Spec(ℤ)`.  This is the object the
source's proof evaluates the sheaves at. -/
public abbrev ftwoObject (B : BigFppfSite.{u}) :
    BigFppfOver B specInt.{u} (contains_specInt B) :=
  siteObject B specInt.{u} (contains_specInt B) (contains_specFTwo B) specFTwoOver.{u}

/-- An additive functor carries `2 • 𝟙 X` to `2 • 𝟙 (F.obj X)`. -/
private theorem map_two_nsmul_id {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] (F : C ⥤ D) [F.Additive] (X : C) :
    F.map (2 • 𝟙 X) = 2 • 𝟙 (F.obj X) := by
  rw [F.map_nsmul, F.map_id]

/-! ### `2` is a monomorphism on `𝒪_{Spec(ℤ)}` -/

/-- The universe lift of `ℤ` is a domain. -/
public theorem isDomain_uliftInt : IsDomain (ULift.{u} ℤ) := Equiv.isDomain Equiv.ulift

/-- `Spec(ℤ)` is an integral scheme. -/
public instance isIntegral_specInt : IsIntegral specInt.{u} := by
  have := isDomain_uliftInt.{u}
  rw [specInt]
  infer_instance

/-- The global sections of `𝒪_{Spec(ℤ)}` are `ℤ`. -/
public def gammaTopRingEquiv : (Γ(specInt.{u}, ⊤) : Type u) ≃+* ℤ := by
  rw [specInt]
  exact (Scheme.ΓSpecIso (CommRingCat.of (ULift.{u} ℤ))).commRingCatIsoToRingEquiv.trans
    (ULift.ringEquiv (R := ℤ))

/-- `2 ≠ 0` in the global sections of `𝒪_{Spec(ℤ)}`. -/
public theorem two_ne_zero_gammaTop : (2 : (Γ(specInt.{u}, ⊤) : Type u)) ≠ 0 := by
  intro h
  have h' := congrArg gammaTopRingEquiv.{u} h
  rw [map_ofNat, map_zero] at h'
  exact two_ne_zero h'

/-- `2 ≠ 0` in the sections of `𝒪_{Spec(ℤ)}` over a nonempty open, restriction from the global
sections being injective on an integral scheme. -/
public theorem two_ne_zero_sections (U : specInt.{u}.Opens) (x : specInt.{u}) (hx : x ∈ U) :
    (2 : (Γ(specInt.{u}, U) : Type u)) ≠ 0 := by
  have : Nonempty U := ⟨⟨x, hx⟩⟩
  intro h
  refine two_ne_zero_gammaTop.{u} (map_injective_of_isIntegral
    (X := specInt.{u}) (homOfLE (le_top (a := U))) ?_)
  rw [map_ofNat, map_zero]
  exact h

/-- **Multiplication by `2` is injective on every ring of sections of `𝒪_{Spec(ℤ)}`.**  Over a
nonempty open those sections are a domain in which `2 ≠ 0`; over the empty open they are
subsingleton. -/
public theorem injective_two_sections (U : specInt.{u}.Opens) :
    Function.Injective (fun x : (Γ(specInt.{u}, U) : Type u) => x + x) := by
  rcases isEmpty_or_nonempty U with hU | hU
  · have : Subsingleton (Γ(specInt.{u}, U) : Type u) := by
      have hb : U = ⊥ := by
        rw [← TopologicalSpace.Opens.not_nonempty_iff_eq_bot]
        rintro ⟨x, hx⟩
        exact hU.false ⟨x, hx⟩
      rw [hb]
      infer_instance
    exact fun a b _ => Subsingleton.elim a b
  · intro a b hab
    refine mul_left_cancel₀ (two_ne_zero_sections.{u} U hU.some.1 hU.some.2) ?_
    rw [two_mul, two_mul]
    exact hab

/-- `𝒪_{Spec(ℤ)}` as an object of `Mod(𝒪_{Spec(ℤ)})`, in the `AlgebraicGeometry.Scheme.Modules`
spelling that the associated-module functor takes its source in. -/
public abbrev unitModule : specInt.{u}.Modules :=
  SheafOfModules.unit specInt.{u}.ringCatSheaf

/-- **`2 : 𝒪_S → 𝒪_S` is a monomorphism of `𝒪_S`-modules, for `S = Spec(ℤ)`.** -/
public theorem mono_two_nsmul_unitModule : Mono (2 • 𝟙 unitModule.{u}) := by
  rw [two_nsmul]
  refine (SheafOfModules.forget specInt.{u}.ringCatSheaf).mono_of_mono_map ?_
  refine PresheafOfModules.mono_of_injective ?_
  intro X
  exact injective_two_sections.{u} X.unop

/-- `𝒪_{Spec(ℤ)}` as an object of `QCoh(𝒪_{Spec(ℤ)})`, the source category of the functor
Stacks 06VE is about. -/
public abbrev unitQcoh :
    (SheafOfModules.isQuasicoherent specInt.{u}.ringCatSheaf).FullSubcategory :=
  ⟨unitModule.{u}, inferInstance⟩

section

variable (B : BigFppfSite.{u}) (τ : SiteKind)

/-! ### `2` is not a monomorphism on `𝒪` over the big site -/

/-- The structure sheaf of `(Sch/Spec(ℤ))_τ`, as a sheaf of rings. -/
public abbrev bigStructureSheaf :=
  FibredSite.baseRingStructureSheaf B specInt.{u} (contains_specInt B) τ

/-- **The sections of `𝒪` over `Spec(𝔽₂) → Spec(ℤ)` are `𝔽₂`.**  They are `Γ(Spec(𝔽₂), 𝒪)` by
definition of the big-site structure sheaf, and `AlgebraicGeometry.Scheme.ΓSpecIso` identifies
that with `𝔽₂`. -/
public def sectionsRingEquiv :
    ((bigStructureSheaf B τ).obj.obj (op (ftwoObject B)) : Type u) ≃+* ULift.{u} (ZMod 2) :=
  ((forget₂ CommRingCat.{u} RingCat.{u}).mapIso
      (Scheme.ΓSpecIso (CommRingCat.of (ULift.{u} (ZMod 2))))).ringCatIsoToRingEquiv

/-- **`2 : 𝒪 → 𝒪` is not a monomorphism of `𝒪`-modules on `(Sch/Spec(ℤ))_τ`.**  A monomorphism of
sheaves of modules is injective on the sections over every object of the site, and over
`Spec(𝔽₂) → Spec(ℤ)` the sections are `𝔽₂`, on which `x ↦ x + x` is the zero map. -/
public theorem not_mono_two_nsmul_unitBig :
    ¬ Mono (2 • 𝟙 (SheafOfModules.unit (bigStructureSheaf B τ))) := by
  rw [two_nsmul]
  intro h
  have : (SheafOfModules.evaluation (bigStructureSheaf B τ) (op (ftwoObject B))).Additive :=
    ⟨rfl⟩
  have h2 : Mono ((SheafOfModules.evaluation (bigStructureSheaf B τ)
      (op (ftwoObject B))).map
      (𝟙 (SheafOfModules.unit (bigStructureSheaf B τ)) + 𝟙 _)) := inferInstance
  rw [CategoryTheory.Functor.map_add, CategoryTheory.Functor.map_id,
    ModuleCat.mono_iff_injective] at h2
  simp only [ModuleCat.hom_add, ModuleCat.hom_id] at h2
  have h2' : ∀ a b : ((bigStructureSheaf B τ).obj.obj (op (ftwoObject B)) : Type u),
      a + a = b + b → a = b := fun a b hab => h2 hab
  have : Nontrivial ((bigStructureSheaf B τ).obj.obj (op (ftwoObject B)) : Type u) :=
    (sectionsRingEquiv B τ).toEquiv.nontrivial
  have hz : (1 : ((bigStructureSheaf B τ).obj.obj (op (ftwoObject B)) : Type u)) + 1 = 0 + 0 := by
    apply (sectionsRingEquiv B τ).injective
    simp only [map_add, map_one, map_zero, add_zero]
    decide
  exact one_ne_zero (h2' 1 0 hz)

/-! ### The failure of exactness -/

/-- The associated-module functor `Mod(𝒪_{Spec(ℤ)}) ⥤ Mod((Sch/Spec(ℤ))_τ, 𝒪)`. -/
public abbrev associatedModule :=
  BigFppfOver.baseAssociatedModule B specInt.{u} (contains_specInt B) τ

/-- The associated-module functor is additive: it is a left adjoint, hence preserves binary
coproducts, hence binary biproducts. -/
public theorem additive_associatedModule : (associatedModule B τ).Additive := by
  have := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts (associatedModule B τ)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- `𝒪_S^a = 𝒪`, from
`AlgebraicGeometry.BigFppfOver.isIso_basePullbackObjUnitToUnit`. -/
public def associatedModuleUnitIso :
    (associatedModule B τ).obj unitModule.{u} ≅ SheafOfModules.unit (bigStructureSheaf B τ) :=
  @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit.{u}
      (BigFppfOver.baseStructureMap B specInt.{u} (contains_specInt B) τ))
    (BigFppfOver.isIso_basePullbackObjUnitToUnit B specInt.{u} (contains_specInt B) τ)

/-- The image of `2 : 𝒪_S → 𝒪_S` under `𝓕 ↦ 𝓕^a` is not a monomorphism of
`Mod((Sch/Spec(ℤ))_τ, 𝒪)`.  Additivity carries `2 • 𝟙` to `2 • 𝟙`, and `𝒪_S^a = 𝒪`. -/
public theorem not_mono_map_two_nsmul :
    ¬ Mono ((associatedModule B τ).map (2 • 𝟙 unitModule.{u})) := by
  intro h
  have := additive_associatedModule B τ
  refine not_mono_two_nsmul_unitBig B τ ?_
  have hmap := map_two_nsmul_id (associatedModule B τ) unitModule.{u}
  have hcomp : (associatedModuleUnitIso B τ).inv ≫
      (2 • 𝟙 ((associatedModule B τ).obj unitModule.{u})) ≫ (associatedModuleUnitIso B τ).hom
      = 2 • 𝟙 (SheafOfModules.unit (bigStructureSheaf B τ)) := by
    rw [Preadditive.nsmul_comp, Category.id_comp, Preadditive.comp_nsmul, Iso.inv_hom_id]
  rw [hmap] at h
  rw [← hcomp]
  exact @mono_comp _ _ _ _ _ _ (IsIso.mono_of_iso (associatedModuleUnitIso B τ).inv) _
    (@mono_comp _ _ _ _ _ _ h _ (IsIso.mono_of_iso (associatedModuleUnitIso B τ).hom))

/-- The functor of Stacks 06VE, `QCoh(𝒪_{Spec(ℤ)}) ⥤ Mod((Sch/Spec(ℤ))_τ, 𝒪)`. -/
public abbrev associatedModuleQcoh :=
  BigFppfOver.baseAssociatedModuleQcoh B specInt.{u} (contains_specInt B) τ

end

/-- The inclusion `QCoh(𝒪_S) ⥤ Mod(𝒪_S)` carries `2 : 𝒪_S → 𝒪_S` to `2 : 𝒪_S → 𝒪_S`. -/
public theorem iota_map_two_nsmul :
    (SheafOfModules.isQuasicoherent specInt.{u}.ringCatSheaf).ι.map (2 • 𝟙 unitQcoh.{u})
      = 2 • 𝟙 unitModule.{u} := by
  have : ((SheafOfModules.isQuasicoherent specInt.{u}.ringCatSheaf).ι).Additive := ⟨rfl⟩
  exact map_two_nsmul_id _ _

/-- **`2 : 𝒪_S → 𝒪_S` is a monomorphism of `QCoh(𝒪_S)`, for `S = Spec(ℤ)`.**  This is the
monomorphism whose image Stacks 06VE (6) shows is not one. -/
public theorem mono_two_nsmul_unitQcoh : Mono (2 • 𝟙 unitQcoh.{u}) := by
  refine (SheafOfModules.isQuasicoherent specInt.{u}.ringCatSheaf).ι.mono_of_mono_map ?_
  rw [iota_map_two_nsmul]
  exact mono_two_nsmul_unitModule

section

variable (B : BigFppfSite.{u}) (τ : SiteKind)

/-- **Stacks 06VE (6), the witness.**  For `S = Spec(ℤ)`, every big fppf site containing it and
every `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`, the monomorphism `2 : 𝒪_S → 𝒪_S` of
`QCoh(𝒪_S)` is carried by `𝓕 ↦ 𝓕^a` to a morphism of `Mod((Sch/S)_τ, 𝒪)` that is **not** a
monomorphism.

This is the example the source gives: `2 : 𝔽₂ → 𝔽₂` is not injective and `Spec(𝔽₂)` is an object
of `(Sch/S)_τ`.  Paired with
`AlgebraicGeometry.AssociatedModuleNotExact.mono_two_nsmul_unitQcoh`, which says the source
morphism *is* a monomorphism, it is the whole of clause (6). -/
@[stacks 06VE "part (6), the witness: at S = Spec(ℤ), on every big site and at every τ, the \
monomorphism 2 : 𝒪_S → 𝒪_S of QCoh(𝒪_S) has non-monomorphic image"]
public theorem not_mono_map_two_nsmul_qcoh :
    ¬ Mono ((associatedModuleQcoh B τ).map (2 • 𝟙 unitQcoh.{u})) := by
  have he : (associatedModuleQcoh B τ).map (2 • 𝟙 unitQcoh.{u})
      = (associatedModule B τ).map (2 • 𝟙 unitModule.{u}) :=
    congrArg (associatedModule B τ).map iota_map_two_nsmul.{u}
  rw [he]
  exact not_mono_map_two_nsmul B τ

/-- **Stacks 06VE (6), as the failure to preserve monomorphisms.** -/
@[stacks 06VE "part (6), as the failure to preserve monomorphisms, at S = Spec(ℤ) on every big \
site and at every τ"]
public theorem not_preservesMonomorphisms_baseAssociatedModuleQcoh :
    ¬ (associatedModuleQcoh B τ).PreservesMonomorphisms := by
  intro h
  have := h
  have := mono_two_nsmul_unitQcoh.{u}
  exact not_mono_map_two_nsmul_qcoh B τ inferInstance

/-- **Stacks 06VE (6).**  The functor `QCoh(𝒪_S) → Mod((Sch/S)_τ, 𝒪)`, `𝓕 ↦ 𝓕^a`, is **not**
exact in general: at `S = Spec(ℤ)` it does not preserve finite limits, on every big fppf site
and at every `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`.

By clause (4) the functor is always right exact, so this is exactly the failure of exactness the
source asserts.  A functor preserving finite limits preserves pullbacks, hence monomorphisms,
which `not_preservesMonomorphisms_baseAssociatedModuleQcoh` of this namespace rules out. -/
@[stacks 06VE "part (6): the functor QCoh(𝒪_S) → Mod((Sch/S)_τ, 𝒪) is not left exact, at \
S = Spec(ℤ), on every big site and at every τ; with part (4) this is the failure of exactness"]
public theorem not_preservesFiniteLimits_baseAssociatedModuleQcoh :
    ¬ Limits.PreservesFiniteLimits (associatedModuleQcoh B τ) := by
  intro h
  have := h
  exact not_preservesMonomorphisms_baseAssociatedModuleQcoh B τ inferInstance

end

end AlgebraicGeometry.AssociatedModuleNotExact

end

end
