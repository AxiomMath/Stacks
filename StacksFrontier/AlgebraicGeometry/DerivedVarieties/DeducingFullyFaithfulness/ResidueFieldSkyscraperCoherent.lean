module

public import StacksFrontier.AlgebraicGeometry.Duality.ClosedPointMatlisDuality
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.DeducingFullyFaithfulness.ResidueFieldSkyscraperPushforward
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.StructureSheafCoherent
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.Coherence
public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Basic
public import StacksFrontier.AlgebraicGeometry.PushforwardCoherent
public import StacksFrontier.RingTheory.Dualizing.Complexes.InvertibleImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.IsIsoLocalCriterion
public import StacksFrontier.Topology.Sheaves.Modules.SkyscraperSupport
public import StacksFrontier.Topology.Sheaves.Modules.StalkSkyscraperAdjunction
public import StacksFrontier.Topology.Sheaves.Modules.UnitStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The residue-field skyscraper at a closed point: coherence, support and Matlis self-duality

Let `X` be a scheme and `x ∈ X` a closed point. This file supplies the three facts about the
skyscraper `𝒪_x = AlgebraicGeometry.residueFieldSkyscraperSheaf X x` with value `κ(x)` that
[Stacks, Tag 0G02] asks of a module supported at `x`, so that it can be applied to `F = F' = 𝒪_x`
in the proof of [Stacks, Tag 0G03] (1):

* `𝒪_x` is coherent when `X` is locally Noetherian;
* `𝒪_x` is supported on `{x}`;
* the stalk `κ(x)` of `𝒪_x` is Matlis dual to itself.

## Main results

* `Dualizing.isMatlisDualPair_of_isSimpleModule`: two simple modules over a local ring are Matlis
  dual to each other.
* `AlgebraicGeometry.isIso_unitToResidueFieldSkyscraperSheaf`: on a reduced scheme with one point
  the residue-field skyscraper is the structure sheaf.
* `AlgebraicGeometry.isCoherent_residueFieldSkyscraperSheaf`: coherence at a closed point of a
  locally Noetherian scheme.
* `AlgebraicGeometry.supp_residueFieldSkyscraperSheaf_subset`: the support is `{x}`.
* `AlgebraicGeometry.isMatlisDualPair_stalk_residueFieldSkyscraperSheaf`: the stalk at `x` is
  Matlis dual to itself.

## Implementation notes

*Matlis duality of simple modules.* For an injective hull `i : κ ⟶ E` of the residue field and a
simple module `N`, every map `N ⟶ E` lands in the image of `i`, since that image is a simple
submodule meeting every nonzero submodule of `E`. So `Hom(N, E) ≅ Hom(N, κ) ≅ End(κ) ≅ κ` is
simple, and two simple modules over a local ring are both isomorphic to `κ`.

*Coherence.* The closed immersion `i : Spec κ(x) ⟶ X` is finite, and `i_*` of the
residue-field skyscraper of `Spec κ(x)` is `𝒪_x`
(`AlgebraicGeometry.pushforwardResidueFieldSkyscraperIso`).
On the reduced one-point scheme `Spec κ(x)` the stalk ring is a field, so the map from the
structure sheaf to the residue-field skyscraper adjoint to the quotient map is an isomorphism on
the only stalk, hence an isomorphism; and the direct image of a coherent quasi-coherent module
along a finite morphism into a locally Noetherian scheme is coherent ([Stacks, Tag 01Y6]).

## References

* [Stacks Project, Tag 0G02](https://stacks.math.columbia.edu/tag/0G02)
* [Stacks Project, Tag 0G03](https://stacks.math.columbia.edu/tag/0G03)
* [Stacks Project, Tag 08Y2](https://stacks.math.columbia.edu/tag/08Y2)
* [Stacks Project, Tag 01Y6](https://stacks.math.columbia.edu/tag/01Y6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Dualizing

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- A simple module over a local ring is the residue field. -/
@[sga "3 VIIB 0.2.1" "special case"]
theorem nonempty_linearEquiv_residueField_of_isSimpleModule
    (M : Type*) [AddCommGroup M] [Module A M] [IsSimpleModule A M] :
    Nonempty (M ≃ₗ[A] IsLocalRing.ResidueField A) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp
    (inferInstance : IsSimpleModule A M)
  rw [IsLocalRing.eq_maximalIdeal hI] at e
  exact ⟨e⟩

/-- The residue field is a simple module over the local ring. -/
@[sga "3 VIIB 0.2.1" "simplicity of S_m"]
theorem isSimpleModule_localRingResidueField : IsSimpleModule A (IsLocalRing.ResidueField A) :=
  (isSimpleModule_iff_isCoatom).2
    (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal A))

/-- Evaluation at `1` identifies the endomorphisms of the residue field with the residue field. -/
def residueFieldEndEvalOne :
    (IsLocalRing.ResidueField A →ₗ[A] IsLocalRing.ResidueField A) ≃ₗ[A]
      IsLocalRing.ResidueField A :=
  LinearEquiv.ofBijective
    { toFun := fun f => f 1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    (by
      refine ⟨fun f g h => ?_, fun x => ⟨LinearMap.mulLeft A x, by simp⟩⟩
      ext x
      obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
      have hx : IsLocalRing.residue A r = r • (1 : IsLocalRing.ResidueField A) := by
        simp [Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq]
      rw [hx, map_smul, map_smul]
      exact congrArg (fun y : IsLocalRing.ResidueField A => r • y) h)

variable {A}

omit [IsLocalRing A] in
/-- In an essential extension `i : S ⟶ E`, every nonzero submodule of `E` meets the image of
`i`. -/
theorem inf_range_ne_bot_of_isInjectiveHull {S E : ModuleCat.{u} A} (i : S ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) (N : Submodule A E) (hN : N ≠ ⊥) :
    N ⊓ LinearMap.range i.hom ≠ ⊥ := by
  let e := ModuleCat.subobjectModule E
  have hS : e.symm N ≠ ⊥ := fun h => hN (by rw [← e.apply_symm_apply N, h, e.map_bot])
  have h := hi.2 (e.symm N) hS
  intro hz
  apply h
  apply e.injective
  rw [e.map_inf, e.map_bot, e.apply_symm_apply]
  change N ⊓ (ModuleCat.subobjectModule E) (Subobject.mk i) = ⊥
  rwa [subobjectModule_mk_eq_range i]

omit [IsLocalRing A] in
/-- For an injective hull `i : S ⟶ E` of a simple module and a simple module `N`, every linear
map `N ⟶ E` lands in the image of `i`. -/
theorem range_le_range_of_isInjectiveHull {S E N : ModuleCat.{u} A} [IsSimpleModule A S]
    [IsSimpleModule A N] (i : S ⟶ E) [Mono i] (hi : Module.IsInjectiveHull i)
    (f : N →ₗ[A] E) : LinearMap.range f ≤ LinearMap.range i.hom := by
  by_cases hf : f = 0
  · simp [hf]
  have hfatom : IsAtom (LinearMap.range f) := isSimpleModule_iff_isAtom.mp
    (IsSimpleModule.congr (LinearEquiv.ofInjective f (LinearMap.injective_of_ne_zero hf)).symm)
  have hmeet := inf_range_ne_bot_of_isInjectiveHull i hi (LinearMap.range f)
    (fun h => hf (LinearMap.range_eq_bot.mp h))
  rcases hfatom.le_iff.mp (inf_le_left : LinearMap.range f ⊓ LinearMap.range i.hom ≤ _) with h | h
  · exact absurd h hmeet
  · exact h ▸ inf_le_right

/-- For an injective hull `i : S ⟶ E` of a simple module and a simple module `N`, composition
with `i` identifies `Hom(N, S)` with `Hom(N, E)`. -/
def linearMapEquivOfIsInjectiveHull {S E N : ModuleCat.{u} A} [IsSimpleModule A S]
    [IsSimpleModule A N] (i : S ⟶ E) [Mono i] (hi : Module.IsInjectiveHull i) :
    (N →ₗ[A] S) ≃ₗ[A] (N →ₗ[A] E) :=
  LinearEquiv.ofBijective (LinearMap.compRight A i.hom) (by
    have hinj : Function.Injective i.hom := (ModuleCat.mono_iff_injective i).mp inferInstance
    refine ⟨fun f g h => LinearMap.ext fun x => hinj (LinearMap.congr_fun h x), fun f => ?_⟩
    have hle := range_le_range_of_isInjectiveHull i hi f
    refine ⟨(LinearEquiv.ofInjective i.hom hinj).symm.toLinearMap ∘ₗ
      f.codRestrict (LinearMap.range i.hom) (fun c => hle (LinearMap.mem_range_self f c)), ?_⟩
    ext x
    exact congrArg Subtype.val ((LinearEquiv.ofInjective i.hom hinj).apply_symm_apply
      ⟨f x, hle (LinearMap.mem_range_self f x)⟩))

/-- For an injective hull `i : S ⟶ E` of a simple module over a local ring and a simple module
`N`, the module `Hom(N, E)` is simple. -/
theorem isSimpleModule_hom_of_isInjectiveHull {S E N : ModuleCat.{u} A} [IsSimpleModule A S]
    [IsSimpleModule A N] (i : S ⟶ E) [Mono i] (hi : Module.IsInjectiveHull i) :
    IsSimpleModule A (N ⟶ E) := by
  obtain ⟨eN⟩ := nonempty_linearEquiv_residueField_of_isSimpleModule A N
  obtain ⟨eS⟩ := nonempty_linearEquiv_residueField_of_isSimpleModule A S
  have := isSimpleModule_localRingResidueField A
  let e : (N ⟶ E) ≃ₗ[A] IsLocalRing.ResidueField A :=
    ModuleCat.homLinearEquiv ≪≫ₗ (linearMapEquivOfIsInjectiveHull i hi).symm ≪≫ₗ
      LinearEquiv.arrowCongr eN eS ≪≫ₗ residueFieldEndEvalOne A
  exact IsSimpleModule.congr e

/-- **The Matlis dual of a simple module over a local ring is simple**: two simple modules are
Matlis dual to each other. -/
theorem isMatlisDualPair_of_isSimpleModule (N N' : ModuleCat.{u} A) [IsSimpleModule A N]
    [IsSimpleModule A N'] : IsMatlisDualPair A N N' := by
  let K : ModuleCat.{u} A := (ModuleCat.uliftFunctor.{0} A).obj
    (ModuleCat.of A (IsLocalRing.ResidueField A))
  have := isSimpleModule_localRingResidueField A
  have : IsSimpleModule A K :=
    IsSimpleModule.congr (ULift.moduleEquiv : K ≃ₗ[A] IsLocalRing.ResidueField A)
  obtain ⟨E, i, hmono, hi⟩ := Module.exists_isInjectiveHull.{u, u} A K
  have := isSimpleModule_hom_of_isInjectiveHull (N := N) i hi
  obtain ⟨e₁⟩ := nonempty_linearEquiv_residueField_of_isSimpleModule A N'
  obtain ⟨e₂⟩ := nonempty_linearEquiv_residueField_of_isSimpleModule A (N ⟶ E)
  exact ⟨E, i, hmono, hi, ⟨(e₁ ≪≫ₗ e₂.symm).toModuleIso⟩⟩

end Dualizing

namespace AlgebraicGeometry

/-- The quotient map from a ring onto the residue field at a prime ideal, as a morphism of
modules. -/
def toResidueFieldModuleCat {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] :
    ModuleCat.of R R ⟶ residueFieldModuleCat p :=
  ModuleCat.ofHom (Algebra.linearMap R p.ResidueField)

/-- At a maximal ideal which is zero, the quotient map onto the residue field is bijective. -/
theorem bijective_toResidueFieldModuleCat {R : Type u} [CommRing R] (p : Ideal R) [p.IsMaximal]
    (hp : p = ⊥) : Function.Bijective (toResidueFieldModuleCat p).hom := by
  have h := Ideal.bijective_algebraMap_quotient_residueField p
  have hmk : Function.Bijective (Ideal.Quotient.mk p) := by
    refine ⟨fun a b hab => ?_, Ideal.Quotient.mk_surjective⟩
    rw [Ideal.Quotient.eq, hp, Ideal.mem_bot, sub_eq_zero] at hab
    exact hab
  exact h.comp hmk

/-- At a maximal ideal which is zero, the quotient map onto the residue field is an isomorphism
of modules. -/
theorem isIso_toResidueFieldModuleCat {R : Type u} [CommRing R] (p : Ideal R) [p.IsMaximal]
    (hp : p = ⊥) : IsIso (toResidueFieldModuleCat p) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_toResidueFieldModuleCat p hp)

/-- The quotient map from the stalk ring at `x` onto the residue field `κ(x)`, as a linear map. -/
def stalkRingToResidueField (X : Scheme.{u}) (x : X) :
    ModuleCat.of (ToType (StacksDraft.StalkRingComparison.stalkRing X x))
        (ToType (StacksDraft.StalkRingComparison.stalkRing X x)) ⟶
      residueFieldStalkModule X x :=
  toResidueFieldModuleCat _

/-- The morphism `𝒪_X ⟶ 𝒪_x` from the structure sheaf to the residue-field skyscraper at `x`,
adjoint to the quotient map of the stalk at `x` onto `κ(x)`. -/
def unitToResidueFieldSkyscraperSheaf (X : Scheme.{u}) (x : X) :
    SheafOfModules.unit X.ringCatSheaf ⟶ residueFieldSkyscraperSheaf X x :=
  SheafOfModules.stalkSkyscraperUp X.ringCatSheaf x _ (residueFieldStalkModule X x)
    ((SheafOfModules.unitStalkIso X.ringCatSheaf x).hom ≫ stalkRingToResidueField X x)

/-- On a reduced scheme with one point the stalk ring at that point is a field, so its maximal
ideal is zero. -/
theorem maximalIdeal_stalkRing_eq_bot (Z : Scheme.{u}) [Subsingleton Z] [IsReduced Z] (z : Z) :
    IsLocalRing.maximalIdeal (ToType (StacksDraft.StalkRingComparison.stalkRing Z z)) = ⊥ := by
  have hmax : IsMax z := fun b _ => (Subsingleton.elim b z).le
  have hfield : IsField (Z.presheaf.stalk z) := isField_stalk_of_isMax hmax
  have hfield' : IsField (ToType (StacksDraft.StalkRingComparison.stalkRing Z z)) :=
    MulEquiv.isField hfield (StacksDraft.StalkRingComparison.stalkRingEquiv Z z).toMulEquiv
  exact (IsLocalRing.isField_iff_maximalIdeal_eq).mp hfield'

/-- **On a reduced scheme with one point the residue-field skyscraper is the structure sheaf**:
the map `𝒪_Z ⟶ 𝒪_z` adjoint to the quotient map onto `κ(z)` is an isomorphism, because there is
only the one stalk to check and there the stalk ring is a field. -/
theorem isIso_unitToResidueFieldSkyscraperSheaf (Z : Scheme.{u}) [Subsingleton Z] [IsReduced Z]
    (z : Z) : IsIso (unitToResidueFieldSkyscraperSheaf Z z) := by
  rw [SheafOfModules.isIso_iff_isIso_stalkMap]
  intro y
  obtain rfl : y = z := Subsingleton.elim _ _
  have : IsIso (stalkRingToResidueField Z y) :=
    isIso_toResidueFieldModuleCat _ (maximalIdeal_stalkRing_eq_bot Z y)
  have h : SheafOfModules.stalkMap Z.ringCatSheaf y (unitToResidueFieldSkyscraperSheaf Z y) =
      ((SheafOfModules.unitStalkIso Z.ringCatSheaf y).hom ≫ stalkRingToResidueField Z y) ≫
        (SheafOfModules.skyscraperStalkIsoObj Z.ringCatSheaf y _).inv :=
    (Iso.eq_comp_inv _).mpr (SheafOfModules.stalkSkyscraperDown_up Z.ringCatSheaf y _ _ _)
  rw [h]
  exact IsIso.comp_isIso' (IsIso.comp_isIso' (Iso.isIso_hom _) this) (Iso.isIso_inv _)

/-- **The residue-field skyscraper at a closed point of a locally Noetherian scheme is
coherent.** It is the direct image of the residue-field skyscraper on `Spec κ(x)` along the
closed immersion `Spec κ(x) ⟶ X`, and on the one-point reduced scheme `Spec κ(x)` that skyscraper
is the structure sheaf; the direct image of a coherent module along a finite morphism into a
locally Noetherian scheme is coherent ([Stacks, Tag 01Y6]). -/
@[ega "IV 11.9.11" "special case", ega "IV 3.2.9" "special case"]
theorem isCoherent_residueFieldSkyscraperSheaf (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X)
    (hx : IsClosed ({x} : Set X)) : (residueFieldSkyscraperSheaf X x).IsCoherent := by
  have : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have : Subsingleton (Spec (X.residueField x)) := by
    have : Subsingleton (PrimeSpectrum (X.residueField x)) := inferInstance
    infer_instance
  let p : Spec (X.residueField x) := IsLocalRing.closedPoint (X.residueField x)
  have hp : (X.fromSpecResidueField x).base p = x := Scheme.fromSpecResidueField_apply x p
  have := isIso_unitToResidueFieldSkyscraperSheaf (Spec (X.residueField x)) p
  have : (SheafOfModules.unit (Spec (X.residueField x)).ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit _
  let e : residueFieldSkyscraperSheaf X x ≅
      (Scheme.Modules.pushforward (X.fromSpecResidueField x)).obj
        (SheafOfModules.unit (Spec (X.residueField x)).ringCatSheaf) :=
    eqToIso (by rw [hp]) ≪≫
      (pushforwardResidueFieldSkyscraperIso (X.fromSpecResidueField x) p).symm ≪≫
      (Scheme.Modules.pushforward (X.fromSpecResidueField x)).mapIso
        (asIso (unitToResidueFieldSkyscraperSheaf (Spec (X.residueField x)) p)).symm
  have : IsFinite (X.fromSpecResidueField x) := inferInstance
  have : ((Scheme.Modules.pushforward (X.fromSpecResidueField x)).obj
      (SheafOfModules.unit (Spec (X.residueField x)).ringCatSheaf)).IsCoherent :=
    Stacks.AlgebraicGeometry.PushforwardCoherent.pushforward_isCoherent_of_isFinite
      (X.fromSpecResidueField x) _
  exact Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso e

/-- The residue-field skyscraper at a closed point `x` is supported on `{x}`. -/
theorem supp_residueFieldSkyscraperSheaf_subset (X : Scheme.{u}) (x : X)
    (hx : IsClosed ({x} : Set X)) :
    SheafOfModules.supp (R := X.ringCatSheaf) (residueFieldSkyscraperSheaf X x) ⊆ {x} := by
  intro y hy
  by_contra hyx
  have hz := SheafOfModules.isZero_stalk_skyscraperObj_of_notMem_closure X.ringCatSheaf x
    (residueFieldStalkModule X x) y (by rwa [hx.closure_eq])
  obtain ⟨a, ha⟩ := hy
  exact ha ((AddCommGrpCat.isZero_iff_subsingleton.mp hz).elim a 0)

section MatlisAtPoint

attribute [local instance] Stacks.Cohomology.DerivedInternalHomStalk.stalkCommRing

/-- The `RingCat`-valued stalk of the structure sheaf is a local ring. -/
local instance isLocalRing_stalkRing' (X : Scheme.{u}) (x : X) :
    IsLocalRing (Stacks.Cohomology.DerivedInternalHomStalk.stalkRing X.toRingedSpace x) :=
  (ringCatStalkRingEquiv (X := X) x).symm.isLocalRing

/-- **The stalk at `x` of the residue-field skyscraper is Matlis dual to itself**: it is the
residue field `κ(x)` of the local ring `𝒪_{X,x}`, whose Matlis dual is `κ(x)`. -/
theorem isMatlisDualPair_stalk_residueFieldSkyscraperSheaf (X : Scheme.{u}) (x : X) :
    Dualizing.IsMatlisDualPair
      (Stacks.Cohomology.DerivedInternalHomStalk.stalkRing X.toRingedSpace x)
      (SheafOfModules.stalkObjStalkRing x (residueFieldSkyscraperSheaf X x))
      (SheafOfModules.stalkObjStalkRing x (residueFieldSkyscraperSheaf X x)) := by
  have : IsSimpleModule (Stacks.Cohomology.DerivedInternalHomStalk.stalkRing X.toRingedSpace x)
      (residueFieldStalkModule X x) :=
    Dualizing.isSimpleModule_residueField _
  have h : IsSimpleModule (Stacks.Cohomology.DerivedInternalHomStalk.stalkRing X.toRingedSpace x)
      (SheafOfModules.stalkObjStalkRing x (residueFieldSkyscraperSheaf X x)) :=
    IsSimpleModule.congr (SheafOfModules.skyscraperStalkIsoObj X.ringCatSheaf x
      (residueFieldStalkModule X x)).toLinearEquiv
  exact @Dualizing.isMatlisDualPair_of_isSimpleModule _ _ _ _ _ h h

end MatlisAtPoint

end AlgebraicGeometry

end
