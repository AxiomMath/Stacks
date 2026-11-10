module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Abelian sheaves annihilated by `m` as modules over the constant sheaf of rings `ℤ/mℤ`

An abelian group annihilated by `m` is the same thing as a `ℤ/mℤ`-module, and an abelian sheaf
on a site all of whose sections are annihilated by `m` is the same thing as a sheaf of modules
over the constant sheaf of rings `ℤ/mℤ`. This module builds the half of that identification
which is needed to resolve an `m`-torsion abelian sheaf by injective sheaves of
`ℤ/mℤ`-modules: the constant sheaf of rings `ℤ/mℤ`, the sheaf of modules over it attached to an
`m`-torsion abelian sheaf, and the identification of its underlying abelian sheaf with the
original sheaf.

Injectivity as a sheaf of `ℤ/mℤ`-modules is strictly stronger than acyclicity for the direct
image and strictly weaker than injectivity as an abelian sheaf, and it is the notion
[Stacks, Tag 0F03] uses: an injective abelian hull of an `m`-torsion sheaf is not `m`-torsion,
so neither it nor its quotient would be available to a statement about `m`-torsion sheaves.

## Main definitions

* `Stacks.Cohomology.ZModSheaf.zmodPresheaf` — the constant presheaf of rings `ℤ/mℤ`.
* `Stacks.Cohomology.ZModSheaf.uliftZModModule` — the module structure over the constant ring
  `ℤ/mℤ` on an abelian group annihilated by `m`.
* `Stacks.Cohomology.ZModSheaf.torsionPresheafToModules` — an abelian presheaf whose sections
  are annihilated by `m`, read as a presheaf of modules over the constant presheaf of rings
  `ℤ/mℤ`.
* `Stacks.Cohomology.ZModSheaf.zmodCommRingSheaf` and
  `Stacks.Cohomology.ZModSheaf.zmodRingSheaf` — the constant sheaf of rings `ℤ/mℤ` on a site,
  as a sheaf of commutative rings and as a sheaf of rings, with
  `Stacks.Cohomology.ZModSheaf.zmodRingMap` the sheafification map out of the constant
  presheaf.
* `Stacks.Cohomology.ZModSheaf.torsionSheafToModules` — **an abelian sheaf annihilated by `m`,
  read as a sheaf of modules over the constant sheaf of rings `ℤ/mℤ`.**

## Main results

* `Stacks.Cohomology.ZModSheaf.smul_eq_zsmul_cast` and
  `Stacks.Cohomology.ZModSheaf.map_smul_of_isAddHom` — an action of the constant ring `ℤ/mℤ` is
  an integer action, so every additive map between two such modules is automatically linear.
  This is why no linearity has to be checked anywhere below.
* `Stacks.Cohomology.ZModSheaf.torsionSheafToModulesIso` — **the underlying abelian sheaf of
  the sheaf of modules attached to an `m`-torsion abelian sheaf is that sheaf itself.**
* `Stacks.Cohomology.ZModSheaf.nsmul_toSheaf_eq_zero` — conversely, the sections of the
  underlying abelian sheaf of *any* sheaf of modules over the constant sheaf of rings `ℤ/mℤ`
  are annihilated by `m`.
* `Stacks.Cohomology.ZModSheaf.natAbs_nsmul_eq_zero_iff` — annihilation by an integer is
  annihilation by its natural absolute value, which is what lets a hypothesis stated with an
  integer feed a construction stated with a natural number.
* `Stacks.Cohomology.ZModSheaf.zsmul_id_eq_zero_iff` — an abelian sheaf is annihilated by `n`
  exactly when `n` times its identity morphism is the zero morphism, and
  `Stacks.Cohomology.ZModSheaf.zsmul_eq_zero_of_epi` — hence a quotient of an abelian sheaf
  annihilated by `n` is annihilated by `n`.

## Implementation notes

The ring of scalars is `ULift (ZMod m)`, so that the universe of the sections of the sheaf of
rings stays independent of the universes of the site; `m = 0` is allowed, `ZMod 0` being `ℤ`
and the torsion hypothesis then vacuous.

Two facts make the construction cheap. First, an action of `ULift (ZMod m)` on an abelian
group is determined: a scalar is the image of an integer, because `ℤ → ZMod m` is surjective,
so the action is the integer action and every additive map is linear
(`map_smul_of_isAddHom`). Second, `m` vanishes in the constant *sheaf* of rings `ℤ/mℤ` for the
cheapest possible reason — the sheafification map out of the constant presheaf is a ring
homomorphism and `m = 0` already in `ℤ/mℤ` — so `nsmul_toSheaf_eq_zero` needs no sheaf-theoretic
argument and in particular no description of the sections of the sheafification.

The constant sheaf of rings is built through commutative rings, so that
`Stacks.SheafifyCommRing.hasSheafifyCommRingCat` supplies sheafification in a coefficient
universe strictly larger than the universes of the site, and is then composed with
`forget₂ CommRingCat RingCat` using `Stacks.hasSheafCompose_forget₂_commRingCat`. Local
bijectivity of `zmodRingMap` is local bijectivity of the sheafification map of commutative
rings, which needs `J.WEqualsLocallyBijective CommRingCat`; that is left as an instance
hypothesis rather than derived, Mathlib's criterion being restricted to coefficients in
`Type (max u v)`.

`torsionSheafToModulesIso` is Mathlib's `CategoryTheory.sheafificationIso`, assigned to its
goal by definitional equality: `PresheafOfModules.sheafificationCompToSheaf` is `Iso.refl`, and
`torsionPresheafToModules M hM` has `M` as its underlying presheaf on the nose, so the
underlying abelian sheaf of `torsionSheafToModules F hF` *is* the abelian sheafification of
`F.obj`. Stating the iso at `(presheafToSheaf J AddCommGrpCat).obj F.obj` and letting the two
sides be identified by `rfl` is what makes it a one-liner; `asIso` applied to the counit at the
spelling of the goal does not elaborate.

## References

* [Stacks Project, Tag 0F03](https://stacks.math.columbia.edu/tag/0F03)
* [Stacks Project, Tag 0DD8](https://stacks.math.columbia.edu/tag/0DD8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t s v u

namespace Stacks.Cohomology.ZModSheaf

/-! ### The constant presheaf of rings `ℤ/mℤ` -/

/-- The constant presheaf of rings `ℤ/mℤ` on a category. -/
public def zmodPresheaf (C : Type u) [Category.{v} C] (m : ℕ) : Cᵒᵖ ⥤ RingCat.{s} :=
  (Functor.const Cᵒᵖ).obj (RingCat.of (ULift.{s, 0} (ZMod m)))

section Scalars

variable {m : ℕ}

/-- Every module action of the constant ring `ℤ/mℤ` on an abelian group is an integer action. -/
public lemma smul_eq_zsmul_cast {A : Type*} [AddCommGroup A]
    [Module (ULift.{s, 0} (ZMod m)) A] (r : ULift.{s, 0} (ZMod m)) (a : A) :
    r • a = (ZMod.cast r.down : ℤ) • a := by
  conv_lhs =>
    rw [show r = ((ZMod.cast r.down : ℤ) : ULift.{s, 0} (ZMod m)) by
      rw [← ULift.up_intCast]
      exact congrArg ULift.up (ZMod.intCast_zmod_cast _).symm]
  exact Int.cast_smul_eq_zsmul _ _ _

/-- Every additive map between abelian groups carrying an action of the constant ring `ℤ/mℤ`
is linear. -/
public lemma map_smul_of_isAddHom {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module (ULift.{s, 0} (ZMod m)) A] [Module (ULift.{s, 0} (ZMod m)) B]
    (φ : A →+ B) (r : ULift.{s, 0} (ZMod m)) (a : A) : φ (r • a) = r • φ a := by
  rw [smul_eq_zsmul_cast, smul_eq_zsmul_cast, map_zsmul]

/-- The module structure over the constant ring `ℤ/mℤ` on an abelian group annihilated
by `m`. -/
@[instance_reducible]
public def uliftZModModule {A : Type*} [AddCommGroup A] (h : ∀ a : A, m • a = 0) :
    Module (ULift.{s, 0} (ZMod m)) A :=
  letI := AddCommGroup.zmodModule h
  ULift.module

variable {C : Type u} [Category.{v} C]

/-- An abelian presheaf annihilated by `m`, read as a presheaf of modules over the constant
presheaf of rings `ℤ/mℤ`. -/
public def torsionPresheafToModules (M : Cᵒᵖ ⥤ AddCommGrpCat.{t})
    (hM : ∀ (X : Cᵒᵖ) (x : ToType (M.obj X)), m • x = 0) :
    PresheafOfModules.{t} (zmodPresheaf.{s} C m) :=
  letI inst : ∀ X : Cᵒᵖ, Module (ULift.{s, 0} (ZMod m)) (ToType (M.obj X)) :=
    fun X ↦ uliftZModModule (hM X)
  @PresheafOfModules.ofPresheaf _ _ (zmodPresheaf.{s} C m) M inst
    (fun {_X _Y} f r x ↦ map_smul_of_isAddHom (M.map f).hom r x)

/-- Reading an abelian presheaf annihilated by `m` as a presheaf of modules over the constant
presheaf of rings `ℤ/mℤ` does not change the underlying abelian presheaf. -/
public lemma torsionPresheafToModules_presheaf (M : Cᵒᵖ ⥤ AddCommGrpCat.{t})
    (hM : ∀ (X : Cᵒᵖ) (x : ToType (M.obj X)), m • x = 0) :
    (torsionPresheafToModules.{t, s} M hM).presheaf = M :=
  rfl

end Scalars

/-! ### The constant sheaf of rings `ℤ/mℤ` -/

section RingSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (m : ℕ)
  [HasSheafify J CommRingCat.{s}]

/-- The constant sheaf of rings `ℤ/mℤ` on a site, as a sheaf of commutative rings. -/
@[sga "4½ Arcata 2.2.1" "C = Z/n"]
public def zmodCommRingSheaf : Sheaf J CommRingCat.{s} :=
  (constantSheaf J CommRingCat.{s}).obj (CommRingCat.of (ULift.{s, 0} (ZMod m)))

/-- The constant sheaf of rings `ℤ/mℤ` on a site, as a sheaf of rings. -/
@[sga "4½ Arcata 2.2.1" "C = Z/n"]
public def zmodRingSheaf : Sheaf J RingCat.{s} :=
  letI := Stacks.hasSheafCompose_forget₂_commRingCat.{s} J
  (sheafCompose J (forget₂ CommRingCat.{s} RingCat.{s})).obj (zmodCommRingSheaf.{s} J m)

/-- The sheafification map from the constant presheaf of rings `ℤ/mℤ` to the constant sheaf of
rings `ℤ/mℤ`. -/
public def zmodRingMap : zmodPresheaf.{s} C m ⟶ (zmodRingSheaf.{s} J m).obj :=
  Functor.whiskerRight
    (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of (ULift.{s, 0} (ZMod m)))))
    (forget₂ CommRingCat.{s} RingCat.{s})

/-- `m` vanishes in the constant sheaf of rings `ℤ/mℤ`: it is the image of `m` under the ring
map from the constant presheaf, and `m = 0` in `ℤ/mℤ`. -/
public lemma natCast_zmodRingSheaf_eq_zero (X : Cᵒᵖ) :
    ((m : ℕ) : ToType ((zmodRingSheaf.{s} J m).obj.obj X)) = 0 := by
  have h : ((m : ℕ) : ToType ((zmodPresheaf.{s} C m).obj X)) = 0 :=
    congrArg ULift.up (ZMod.natCast_self m)
  rw [← map_natCast ((zmodRingMap.{s} J m).app X).hom m, h, map_zero]

/-- **The sections of the underlying abelian sheaf of a sheaf of modules over the constant
sheaf of rings `ℤ/mℤ` are annihilated by `m`.** -/
public lemma nsmul_toSheaf_eq_zero (M : SheafOfModules.{t} (zmodRingSheaf.{s} J m)) (X : Cᵒᵖ)
    (x : ToType (M.val.obj X)) : m • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ToType ((zmodRingSheaf.{s} J m).obj.obj X)) m x,
    natCast_zmodRingSheaf_eq_zero, zero_smul]

variable [J.WEqualsLocallyBijective CommRingCat.{s}]

/-- The sheafification map into the constant sheaf of rings `ℤ/mℤ` is locally injective. -/
public instance zmodRingMap_isLocallyInjective :
    Presheaf.IsLocallyInjective J (zmodRingMap.{s} J m) := by
  have hα : Presheaf.IsLocallyInjective J
      (toSheafify J ((Functor.const Cᵒᵖ).obj
        (CommRingCat.of (ULift.{s, 0} (ZMod m))))) := inferInstance
  exact ⟨fun x y hxy ↦ hα.equalizerSieve_mem x y hxy⟩

/-- The sheafification map into the constant sheaf of rings `ℤ/mℤ` is locally surjective. -/
public instance zmodRingMap_isLocallySurjective :
    Presheaf.IsLocallySurjective J (zmodRingMap.{s} J m) := by
  have hα : Presheaf.IsLocallySurjective J
      (toSheafify J ((Functor.const Cᵒᵖ).obj
        (CommRingCat.of (ULift.{s, 0} (ZMod m))))) := inferInstance
  exact ⟨fun x ↦ hα.imageSieve_mem x⟩

variable [HasWeakSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}]

/-- **An abelian sheaf annihilated by `m`, read as a sheaf of modules over the constant sheaf
of rings `ℤ/mℤ`**: the sectionwise `ℤ/mℤ`-action, sheafified. -/
public def torsionSheafToModules (F : Sheaf J AddCommGrpCat.{t})
    (hF : ∀ (X : Cᵒᵖ) (x : ToType (F.obj.obj X)), m • x = 0) :
    SheafOfModules.{t} (zmodRingSheaf.{s} J m) :=
  (PresheafOfModules.sheafification (zmodRingMap.{s} J m)).obj
    (torsionPresheafToModules.{t, s} F.obj hF)

/-- **The underlying abelian sheaf of `torsionSheafToModules F hF` is `F` itself.** -/
public def torsionSheafToModulesIso (F : Sheaf J AddCommGrpCat.{t})
    (hF : ∀ (X : Cᵒᵖ) (x : ToType (F.obj.obj X)), m • x = 0) :
    (SheafOfModules.toSheaf.{t} (zmodRingSheaf.{s} J m)).obj
        (torsionSheafToModules.{t, s} J m F hF) ≅ F :=
  (sheafificationIso (J := J) (D := AddCommGrpCat.{t}) F).symm

end RingSheaf

/-! ### Annihilation by an integer, as a property of the identity morphism -/

section Torsion

/-- An element of an abelian group is annihilated by an integer exactly when it is annihilated
by that integer's natural absolute value. -/
public lemma natAbs_nsmul_eq_zero_iff {A : Type*} [AddCommGroup A] (n : ℤ) (x : A) :
    n.natAbs • x = 0 ↔ n • x = 0 := by
  rw [← natCast_zsmul, Int.natCast_natAbs]
  rcases abs_choice n with h | h
  · rw [h]
  · rw [h, neg_zsmul, neg_eq_zero]

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- `n` times a morphism of abelian sheaves acts on sections as `n` times. -/
public lemma zsmul_app_apply {F G : Sheaf J AddCommGrpCat.{t}} (φ : F ⟶ G) (n : ℤ) (X : Cᵒᵖ)
    (x : ToType (F.obj.obj X)) : (n • φ).hom.app X x = n • (φ.hom.app X x) := by
  change (n • φ.hom).app X x = _
  rw [NatTrans.app_zsmul]
  rfl

/-- **An abelian sheaf is annihilated by `n` exactly when `n` times its identity morphism is
zero.** -/
public lemma zsmul_id_eq_zero_iff (F : Sheaf J AddCommGrpCat.{t}) (n : ℤ) :
    n • 𝟙 F = 0 ↔ ∀ (X : Cᵒᵖ) (x : ToType (F.obj.obj X)), n • x = 0 := by
  refine ⟨fun h X x => ?_, fun h => ?_⟩
  · have hx := zsmul_app_apply (𝟙 F) n X x
    rw [h] at hx
    exact hx.symm
  · ext X x
    rw [zsmul_app_apply]
    exact h X x

/-- **A quotient of an abelian sheaf annihilated by `n` is annihilated by `n`.** -/
public lemma zsmul_eq_zero_of_epi {F G : Sheaf J AddCommGrpCat.{t}} (π : F ⟶ G) [Epi π] (n : ℤ)
    (hF : ∀ (X : Cᵒᵖ) (x : ToType (F.obj.obj X)), n • x = 0) (X : Cᵒᵖ)
    (y : ToType (G.obj.obj X)) : n • y = 0 := by
  refine (zsmul_id_eq_zero_iff G n).1 ?_ X y
  rw [← cancel_epi π]
  calc π ≫ (n • 𝟙 G) = n • π := by rw [Preadditive.comp_zsmul, Category.comp_id]
    _ = (n • 𝟙 F) ≫ π := by rw [Preadditive.zsmul_comp, Category.id_comp]
    _ = 0 := by rw [(zsmul_id_eq_zero_iff F n).2 hF, zero_comp]
    _ = π ≫ 0 := by rw [comp_zero]

end Torsion

end Stacks.Cohomology.ZModSheaf

end
