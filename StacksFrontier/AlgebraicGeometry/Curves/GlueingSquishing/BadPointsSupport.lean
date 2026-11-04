module

public import StacksFrontier.AlgebraicGeometry.AlgebraImageSurjective.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.BadPointsAdditivity
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.LowerProperSubalgebra
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.PushforwardMono
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.SpreadOutSubalgebra
public import StacksFrontier.AlgebraicGeometry.DevissageNoetherian.EmptySupportVanishing
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.AlgebraSheafMultiplication

/-!
# From a proper subalgebra over an open to a point of the support of the quotient

The strict drop of the measure of [Stacks, Tag 0C1L] at the upper end,
`Stacks.GlueSquishFactor.sheafMultiplicity_cokernel_structureUnitHom_lt_of_mem_supp_right`, is
stated at a **point** `x` of `Stacks.Chow.supp` of the quotient `f_*𝒪_{X'}/𝒜`, whereas the
producer of the subalgebra,
`Stacks.GlueSquishFactor.exists_isFinite_subalg_ne_top`, yields a **section-level** inequality:
the subring `C.obj U` of `Γ(f_*𝒪_{X'}, U)` is not everything. This file is the bridge between
the two.

## Main results

* `Stacks.GlueSquishFactor.nonempty_supp_cokernel_of_not_surjective` — **the bridge, in its
  general form**: for a monomorphism `b : F ⟶ G` of `𝒪_X`-modules which is not surjective on
  the sections over a single open, the support of `cokernel b` is nonempty.
* `Stacks.GlueSquishFactor.nonempty_supp_cokernel_underlyingModuleMap_incl` — the same for the
  inclusion of a concrete subalgebra whose sections over an open are a proper subring.
* `Stacks.GlueSquishFactor.exists_isFinite_subalg_mem_supp_cokernel` — **the producer with the
  point**: the subalgebra of `Stacks.GlueSquishFactor.exists_isFinite_subalg_ne_top` together
  with a point at which `f_*𝒪_{X'}/𝒜` does not vanish.

## Implementation notes

**No affineness and no quasi-coherence are used, and that is the point of the argument.** The
obvious route — read both sides on an affine open, where the sections of the quotient are the
quotient of the sections and a nonzero finite module over a Noetherian ring has a point in its
support — needs exactness of `Γ(-, U)` on quasi-coherent modules over an affine open, and the
transport `AlgebraicGeometry.Scheme.Modules.mem_support_sections_iff_mem_supp` of
[Stacks, Tag 056I] on top of it. None of that is necessary. In the abelian category `X.Modules`
the three steps

* `SheafOfModules.supp (cokernel b) = ∅` gives `IsZero (cokernel b)`
  (`SheafOfModules.isZero_of_supp_eq_empty`), hence `Epi b`;
* `Mono b` and `Epi b` give `IsIso b`, an abelian category being balanced;
* an isomorphism of sheaves of modules *is* bijective on the sections over every open

compose to the contrapositive, and the middle step is exactly what an epimorphism of sheaves
alone would not give: epimorphy is a local condition and does not imply sectionwise
surjectivity, while invertibility does.

**Why `Mono b` is not an extra hypothesis at the use site.** For the inclusion of a concrete
subalgebra it is `Stacks.AlgebraicGeometry.AlgebraImageSurjective.mono_underlyingModuleMap_of_mono`
applied to `Stacks.RelativeSpec.AlgebraSheaf.Subalg.mono_incl`, which is itself
`Subtype.val_injective`; and the hypothesis of the strict drop
`Stacks.GlueSquishFactor.sheafMultiplicity_cokernel_structureUnitHom_lt_of_mem_supp_right`
carries `Mono b` already.

## No stacks attribute

**No `@[stacks]` attribute is attached, and none is earned.** This is an input to the splitting
hypothesis `hsplit` of `Stacks.GlueSquishFactor.isElementaryChain_of_isAlmostIso`, which is
still unproved; on its own it asserts no part of the lemma.

## References

* [Stacks Project, Tag 0C1L](https://stacks.math.columbia.edu/tag/0C1L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence
open Stacks.AlgebraicGeometry.SubalgebraGeneratedByModule
open Stacks.AlgebraicGeometry.IdealPowerSmul

universe u

namespace Stacks.GlueSquishFactor

/-! ### The bridge -/

/-- **A monomorphism of modules which is not surjective on the sections over some open has a
cokernel with a point in its support.** If the support were empty the cokernel would be a zero
object (`SheafOfModules.isZero_of_supp_eq_empty`), so `b` would be an epimorphism, hence — the
category of modules on a scheme being abelian, therefore balanced — an isomorphism, and an
isomorphism of sheaves of modules is bijective on the sections over every open. -/
theorem nonempty_supp_cokernel_of_not_surjective {X : Scheme.{u}} {F G : X.Modules} (b : F ⟶ G)
    [Mono b] {U : X.Opens} (hb : ¬ Function.Surjective (b.val.app (op U)).hom) :
    (SheafOfModules.supp (cokernel b)).Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro hsupp
  have hz : IsZero (cokernel b) := SheafOfModules.isZero_of_supp_eq_empty _ hsupp
  have : Epi b := Abelian.epi_of_cokernel_π_eq_zero b (hz.eq_zero_of_tgt _)
  have : IsIso b := isIso_of_mono_of_epi b
  refine hb fun y => ⟨((inv b).val.app (op U)).hom y, ?_⟩
  exact congrArg (fun φ : G ⟶ G => (φ.val.app (op U)).hom y) (IsIso.inv_hom_id b)

/-- **The bridge for the inclusion of a concrete subalgebra.** If the sections of `C` over an
open `U` are a proper subring of the sections of `A`, then the quotient `A/C` of underlying
`𝒪_X`-modules has a point in its support.

The inclusion is injective on the sections over every open, so it is a monomorphism of algebra
sheaves and its underlying morphism of modules is a monomorphism of modules; on sections it is
`Subtype.val`, which is surjective exactly when the subring is everything. -/
theorem nonempty_supp_cokernel_underlyingModuleMap_incl {X : Scheme.{u}} {A : AlgebraSheaf X}
    (C : AlgebraSheaf.Subalg A) {U : X.Opens} (hC : C.obj U ≠ ⊤) :
    (SheafOfModules.supp
        (cokernel (AlgebraSheaf.underlyingModuleMap (AlgebraSheaf.Subalg.incl C)))).Nonempty := by
  have : Mono (AlgebraSheaf.underlyingModuleMap (AlgebraSheaf.Subalg.incl C)) :=
    Stacks.AlgebraImageSurjective.mono_underlyingModuleMap_of_mono
      (AlgebraSheaf.Subalg.incl C) inferInstance
  refine nonempty_supp_cokernel_of_not_surjective _ (U := U) fun hsurj => hC ?_
  refine top_unique fun a _ => ?_
  obtain ⟨c, hc⟩ := hsurj a
  exact hc ▸ c.2

/-! ### The producer with the point -/

/-- **The spreading-out of [Stacks, Tag 0C1L], with a point of the support of the quotient.**
Under the hypotheses of `Stacks.GlueSquishFactor.exists_isFinite_subalg_ne_top` there is a
finite quasi-coherent `𝒪_X`-subalgebra `𝒜` of `f_*𝒪_{X'}` which is proper over `U` *and* a
point at which `f_*𝒪_{X'}/𝒜` does not vanish.

The last clause is the hypothesis `hb` of
`Stacks.GlueSquishFactor.sheafMultiplicity_cokernel_structureUnitHom_lt_of_mem_supp_right`, so
with this statement the strict drop of the measure at the upper end is available for the
subalgebra the spreading-out produces. -/
theorem exists_isFinite_subalg_mem_supp_cokernel {X' X : Scheme.{u}} (f : X' ⟶ X) [IsFinite f]
    [IsLocallyNoetherian X] [AlgebraSheaf.IsQuasicoherent (pushforwardAlgebra f)]
    [(AlgebraSheaf.underlyingModule (pushforwardAlgebra f) : X.Modules).IsCoherent]
    {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) (hcl : IsClosed ({x} : Set X))
    (hne : letI : Algebra (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x) :=
        ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map f.c).hom.toAlgebra
      (⊥ : Subalgebra (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x)) ≠ ⊤) :
    ∃ C : AlgebraSheaf.Subalg (pushforwardAlgebra f),
      (AlgebraSheaf.Subalg.toAlgebraSheaf C).IsQuasicoherent ∧
        (AlgebraSheaf.Subalg.toAlgebraSheaf C).IsFinite ∧ C.obj U ≠ ⊤ ∧
          ∃ z : X, z ∈ SheafOfModules.supp
            (cokernel (AlgebraSheaf.underlyingModuleMap (AlgebraSheaf.Subalg.incl C))) := by
  obtain ⟨C, hCqc, hCfin, hCne⟩ := exists_isFinite_subalg_ne_top f hU hx hcl hne
  exact ⟨C, hCqc, hCfin, hCne, nonempty_supp_cokernel_underlyingModuleMap_incl C hCne⟩

/-! ### The factorization `𝒪_X ⟶ 𝒜 ⟶ f_*𝒪_{X'}` of the unit -/

/-- **`Stacks.GlueSquishFactor.structureUnitHom` is the structure morphism of the pushforward
algebra, read through `Stacks.RelativeSpec.AlgebraSheaf.unitModuleMap`.** The two are built
differently — one as the canonical map out of a unit module along a change of rings, the other as
`r ↦ r · 1` on sections — and agree because a map out of a unit module carries `r` to `r • 1`. -/
theorem structureUnitHom_eq_unitModuleMap {X' X : Scheme.{u}} (f : X' ⟶ X) :
    structureUnitHom f = AlgebraSheaf.unitModuleMap (pushforwardAlgebra f) := by
  apply SheafOfModules.hom_ext
  refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun r => ?_)
  exact Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit_val_app
    (AlgebraSheaf.structureMap (pushforwardAlgebra f)) U r

/-- **The unit `𝒪_X ⟶ f_*𝒪_{X'}` factors through any concrete subalgebra**, as the structure
morphism of the subalgebra followed by the inclusion. This is the hypothesis `hab` of
`Stacks.GlueSquishFactor.sheafMultiplicity_cokernel_structureUnitHom_add` and of its strict-drop
companion, and it is the functoriality
`Stacks.RelativeSpec.AlgebraSheaf.unitModuleMap_comp` read through
`Stacks.GlueSquishFactor.structureUnitHom_eq_unitModuleMap`. -/
theorem unitModuleMap_comp_underlyingModuleMap_incl {X' X : Scheme.{u}} (f : X' ⟶ X)
    (C : AlgebraSheaf.Subalg (pushforwardAlgebra f)) :
    AlgebraSheaf.unitModuleMap (AlgebraSheaf.Subalg.toAlgebraSheaf C) ≫
        AlgebraSheaf.underlyingModuleMap (AlgebraSheaf.Subalg.incl C) = structureUnitHom f :=
  (AlgebraSheaf.unitModuleMap_comp (AlgebraSheaf.Subalg.incl C)).trans
    (structureUnitHom_eq_unitModuleMap f).symm

/-- The unit module map of an algebra sheaf is a monomorphism once it is injective on sections. -/
private theorem mono_unitModuleMap_of_injective {X : Scheme.{u}} (A : AlgebraSheaf X)
    (hinj : ∀ ⦃U : (X.Opens)ᵒᵖ⦄, Function.Injective ((AlgebraSheaf.unitPresheafMap A).app U)) :
    Mono (AlgebraSheaf.unitModuleMap A) :=
  (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map (PresheafOfModules.mono_of_injective hinj)

/-- **`𝒪_X ⟶ f_*𝒪_{X'}` is a monomorphism of modules** when it is one of sheaves of rings: on
sections both are `f.app U`, and a morphism of sheaves of modules injective on sections is a
monomorphism. -/
theorem mono_structureUnitHom {X' X : Scheme.{u}} (f : X' ⟶ X)
    (hmono : Mono (pushforwardAlgebra f).hom) : Mono (structureUnitHom f) :=
  (structureUnitHom_eq_unitModuleMap f) ▸
    mono_unitModuleMap_of_injective _ fun U =>
      injective_app_of_mono_hom_pushforwardAlgebra f hmono U.unop

/-- **`𝒪_X ⟶ 𝒜` is a monomorphism of modules** for every concrete subalgebra `𝒜` of
`f_*𝒪_{X'}`, as soon as `𝒪_X ⟶ f_*𝒪_{X'}` is one of sheaves of rings: on sections the structure
map of `𝒜` is the corestriction of `f.app U`, and `Subtype.val` is injective. -/
theorem mono_unitModuleMap_subalg {X' X : Scheme.{u}} (f : X' ⟶ X)
    (hmono : Mono (pushforwardAlgebra f).hom)
    (C : AlgebraSheaf.Subalg (pushforwardAlgebra f)) :
    Mono (AlgebraSheaf.unitModuleMap (AlgebraSheaf.Subalg.toAlgebraSheaf C)) :=
  mono_unitModuleMap_of_injective _ fun U _ _ hab =>
    injective_app_of_mono_hom_pushforwardAlgebra f hmono U.unop (congrArg Subtype.val hab)

/-! ### The lower end: a section of `𝒜` which is not a section of `𝒪_X` -/

/-- **The bridge at the lower end.** If a concrete subalgebra `𝒜` of `f_*𝒪_{X'}` has a section
over an open `U` which is not the image of a section of `𝒪_X`, then the quotient `𝒜/𝒪_X` has a
point in its support.

This is the lower-end analogue of
`Stacks.GlueSquishFactor.nonempty_supp_cokernel_underlyingModuleMap_incl`, and it is the shape
`Stacks.GlueSquishFactor.sheafMultiplicity_cokernel_lt_of_mem_supp_left` consumes. The
monomorphy of `𝒪_X ⟶ 𝒜` is not an extra hypothesis: it is `CategoryTheory.mono_of_mono` applied
to the factorization `Stacks.GlueSquishFactor.unitModuleMap_comp_underlyingModuleMap_incl` of the
monomorphism `𝒪_X ⟶ f_*𝒪_{X'}`. -/
theorem nonempty_supp_cokernel_unitModuleMap_of_notMem_range {X' X : Scheme.{u}} (f : X' ⟶ X)
    (hmono : Mono (pushforwardAlgebra f).hom)
    (C : AlgebraSheaf.Subalg (pushforwardAlgebra f)) {U : X.Opens}
    {s : AlgebraSheaf.sections (pushforwardAlgebra f) U} (hsC : s ∈ C.obj U)
    (hsnot : s ∉ Set.range (f.app U).hom) :
    (SheafOfModules.supp (cokernel (AlgebraSheaf.unitModuleMap
        (AlgebraSheaf.Subalg.toAlgebraSheaf C)))).Nonempty := by
  refine @nonempty_supp_cokernel_of_not_surjective _ _ _ _
    (mono_unitModuleMap_subalg f hmono C) U fun hsurj => hsnot ?_
  obtain ⟨r, hr⟩ := hsurj ⟨s, hsC⟩
  exact ⟨r, congrArg Subtype.val hr⟩

/-- **The spreading-out of [Stacks, Tag 0C1L], proper at *both* ends.** Under the hypotheses of
`Stacks.GlueSquishFactor.exists_isFinite_subalg_ne_top`, strengthened to the hypothesis `hb` of
`Stacks.GlueSquishFactor.exists_mem_map_primeIdealOf_notMem_range` — some element of
`m_x·(f_*𝒪_{X'})_x` is not a germ of `𝒪_{X,x}`, which is the branch of
`Stacks.GlueSquishFactor.forall_exists_algebraMap_eq_or_exists_subalgebra` in which an
intermediate subalgebra exists — the subalgebra `𝒪_X + ℐ_x · f_*𝒪_{X'}` is finite,
quasi-coherent, and **both** quotients `𝒜/𝒪_X` and `f_*𝒪_{X'}/𝒜` have a point in their support.

The two clauses are the hypotheses of
`Stacks.GlueSquishFactor.sheafMultiplicity_cokernel_lt_of_mem_supp_left` and
`...._right` for the factorization
`Stacks.GlueSquishFactor.unitModuleMap_comp_underlyingModuleMap_incl`, so the measure of
[Stacks, Tag 0C1L] drops strictly at both ends of this splitting. No hypothesis `hne` is needed:
`hb` already witnesses `𝒪_{X,x} ≠ (f_*𝒪_{X'})_x`. -/
theorem exists_isFinite_subalg_mem_supp_cokernel_both {X' X : Scheme.{u}} (f : X' ⟶ X)
    [IsFinite f] [IsLocallyNoetherian X] [AlgebraSheaf.IsQuasicoherent (pushforwardAlgebra f)]
    [(AlgebraSheaf.underlyingModule (pushforwardAlgebra f) : X.Modules).IsCoherent]
    (hmono : Mono (pushforwardAlgebra f).hom)
    {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) (hcl : IsClosed ({x} : Set X))
    (hb : letI : Algebra (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x) :=
        ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map f.c).hom.toAlgebra
      ∃ b ∈ (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).map
          (algebraMap (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x)),
        ∀ a : X.presheaf.stalk x,
          algebraMap (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x) a ≠ b) :
    ∃ C : AlgebraSheaf.Subalg (pushforwardAlgebra f),
      (AlgebraSheaf.Subalg.toAlgebraSheaf C).IsQuasicoherent ∧
        (AlgebraSheaf.Subalg.toAlgebraSheaf C).IsFinite ∧
          (SheafOfModules.supp (cokernel (AlgebraSheaf.unitModuleMap
            (AlgebraSheaf.Subalg.toAlgebraSheaf C)))).Nonempty ∧
          (SheafOfModules.supp (cokernel (AlgebraSheaf.underlyingModuleMap
            (AlgebraSheaf.Subalg.incl C)))).Nonempty := by
  let : Algebra (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x) :=
    ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map f.c).hom.toAlgebra
  have hne : (⊥ : Subalgebra (X.presheaf.stalk x)
      ((f.base _* X'.presheaf).stalk x)) ≠ ⊤ := by
    intro htop
    obtain ⟨b, -, hbnot⟩ := hb
    obtain ⟨a, ha⟩ := (Algebra.mem_bot (R := X.presheaf.stalk x)
      (A := (f.base _* X'.presheaf).stalk x)).mp (htop ▸ Algebra.mem_top (x := b))
    exact hbnot a ha
  have hAint : (pushforwardAlgebra f).IsIntegral :=
    (AlgebraicGeometry.isFinite_pushforwardAlgebra f).isIntegral
  obtain ⟨s, hsC, hsnot⟩ := exists_mem_obj_idealSmulSubalg_notMem_range f hU hx hcl hb
  refine ⟨idealSmulSubalg (pushforwardAlgebra f) (closedIdeal (⟨{x}, hcl⟩ : Closeds X)),
    isQuasicoherent_idealSmulSubalg _ _, isFinite_idealSmulSubalg _ _ hAint,
    nonempty_supp_cokernel_unitModuleMap_of_notMem_range f hmono _ hsC hsnot,
    nonempty_supp_cokernel_underlyingModuleMap_incl _
      (ne_top_obj_idealSmulSubalg f _ hU hx ?_ hne)⟩
  exact (mem_closed_iff_vanishingIdeal_le ⟨{x}, hcl⟩ ⟨U, hU⟩ x hx).mp rfl

end Stacks.GlueSquishFactor

end
