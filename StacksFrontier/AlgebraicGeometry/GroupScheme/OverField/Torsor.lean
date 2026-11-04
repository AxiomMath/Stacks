module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.Coverings

/-!
# Pseudo-torsors and principal homogeneous spaces

An action of a group object on an object is a *pseudo-torsor* when the shear map sending
`(g, x)` to `(g • x, x)` is an isomorphism, and such a pseudo-torsor is *trivial* when it is
equivariantly isomorphic to the group object with its left regular action.  A pseudo-torsor is
a *torsor* for a topology on the base when it becomes trivial after a covering of the base for
that topology; the default topology is fpqc, which gives the principal homogeneous spaces.

## Main definitions

* `AlgebraicGeometry.IsPseudoTorsor` says that the shear map of an action is an isomorphism.
* `AlgebraicGeometry.IsTrivialPseudoTorsor` says that the action is equivariantly isomorphic
  to the left regular action.
* `AlgebraicGeometry.IsTorsorFor` is local triviality for a precoverage of schemes, and
  `AlgebraicGeometry.IsFpqcTorsor`, `AlgebraicGeometry.IsZariskiTorsor`,
  `AlgebraicGeometry.IsEtaleTorsor`, `AlgebraicGeometry.IsSmoothTorsor`,
  `AlgebraicGeometry.IsSyntomicTorsor` and `AlgebraicGeometry.IsFppfTorsor` are its instances
  at the named topologies.

## Main results

* `AlgebraicGeometry.isPseudoTorsor_iff_forall_existsUnique_smul` characterizes a pseudo-torsor
  by the unique group element carrying any one generalized point to any other.
* `AlgebraicGeometry.isTrivial_iff_exists_globalSection` characterizes trivial pseudo-torsors
  by the existence of a global section.

## References

* [Stacks Project, Tag 0498](https://stacks.math.columbia.edu/tag/0498)
* [Stacks Project, Tag 0499](https://stacks.math.columbia.edu/tag/0499)
* [Stacks Project, Tag 049A](https://stacks.math.columbia.edu/tag/049A)
* [SGA3, Exposé IV, 6.5]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj

namespace AlgebraicGeometry

universe u v

/-- An action is a pseudo-torsor if its shear map `(g, x) ↦ (g • x, x)` is an
isomorphism. -/
@[stacks 0498 "part (1)",
  sga "3 VIB 10.15" "formally principal hom.",
  sga "3 IV 6.7" "(iii)",
  sga "3 IV 5.1.0", sga "3 III 0.1" "(ii)", sga "1 V 5.11" "formally princ. homog."]
abbrev IsPseudoTorsor {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    (G X : C) [GrpObj G] [ModObj G X] : Prop :=
  IsIso (ModObj.leftSMul G X)

/-- An action is trivial if it is equivariantly isomorphic to the group object with its left
regular action. -/
@[stacks 0498 "part (2)", sga "3 IV 5.1.1"]
abbrev IsTrivialPseudoTorsor {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    (G X : C) [GrpObj G] [ModObj G X] : Prop :=
  Nonempty (Mod.regular G ≅ (CategoryTheory.Mod.mk X : CategoryTheory.Mod C G))

add_to_stacks 0499 "pointwise_characterization" CategoryTheory.ModObj.isIso_leftSMul_iff

/-- An action is a pseudo-torsor exactly when it is pointwise simply transitive: for every test
object `T`, any two `T`-points of `X` differ by a unique `T`-point of `G`. -/
@[stacks 0499 "part (1), the pointwise characterization",
  sga "3 IV 5.1.0" "more general",
  sga "3 IV 6.7" "(i) ⇔ (iii)"]
lemma isPseudoTorsor_iff_forall_existsUnique_smul
    {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    (G X : C) [GrpObj G] [ModObj G X] :
    IsPseudoTorsor G X ↔ ∀ (T : C) (x y : T ⟶ X), ∃! g : T ⟶ G, g • x = y :=
  CategoryTheory.ModObj.isIso_leftSMul_iff

/-- A pseudo-torsor is trivial if and only if it admits a global section. -/
@[stacks 0499 "trivial_iff_section", sga "3 IV 5.1.4", sga "3 IV 5.1.5" "(ii) trivial ⟺ section"]
lemma isTrivial_iff_exists_globalSection
    {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    (G X : C) [GrpObj G] [ModObj G X] (hX : IsPseudoTorsor G X) :
    IsTrivialPseudoTorsor G X ↔ Nonempty (𝟙_ C ⟶ X) := by
  refine ⟨fun ⟨e⟩ => ⟨(MonObj.one : 𝟙_ C ⟶ G) ≫ e.hom.hom⟩, fun ⟨s⟩ => ?_⟩
  let _ : ModObj G G := .regular G
  let f : G ⟶ X := (𝟙 G) • (CartesianMonoidalCategory.toUnit G ≫ s)
  have hf : IsIso f := by
    rw [isIso_iff_yoneda_map_bijective]; intro Z
    rw [Function.bijective_iff_existsUnique]; intro y
    simpa [f, Function.comp_apply, ModObj.comp_smul] using
      (ModObj.isIso_leftSMul_iff.mp hX Z (CartesianMonoidalCategory.toUnit Z ≫ s) y)
  have hmod : μ[G] ≫ f = G ◁ f ≫ γ[G, X] := by
    have h : CartesianMonoidalCategory.lift (CartesianMonoidalCategory.fst G G)
        (CartesianMonoidalCategory.lift (CartesianMonoidalCategory.snd G G)
          (CartesianMonoidalCategory.toUnit (G ⊗ G) ≫ s) ≫ γ[G, X]) =
        G ◁ (CartesianMonoidalCategory.lift (𝟙 G)
          (CartesianMonoidalCategory.toUnit G ≫ s) ≫ γ[G, X]) := by
      ext
      · simp
      · rw [CartesianMonoidalCategory.whiskerLeft_snd]; simp [← Category.assoc]
    simpa [f, Hom.mul_def, Hom.smul_def, ← CartesianMonoidalCategory.lift_whiskerRight,
      ← Category.assoc, h] using mul_smul (CartesianMonoidalCategory.fst G G)
        (CartesianMonoidalCategory.snd G G) (CartesianMonoidalCategory.toUnit (G ⊗ G) ≫ s)
  let e : G ≅ X := @asIso C _ G X f hf
  let _ : IsModHom G e.hom := ⟨hmod⟩
  exact ⟨{
    hom := Mod.Hom.mk'' e.hom hmod
    inv := Mod.Hom.mk'' e.inv (inferInstance : IsModHom G e.inv).smul_hom
    hom_inv_id := Mod.hom_ext _ _ e.hom_inv_id
    inv_hom_id := Mod.hom_ext _ _ e.inv_hom_id }⟩

/-- A pseudo-torsor trivialized by a family in a precoverage of schemes. -/
abbrev IsTorsorFor (S : Scheme.{u}) (G X : Over S) [GrpObj G] [ModObj G X]
    (J : Precoverage Scheme.{u}) : Prop :=
  IsPseudoTorsor G X ∧ ∃ (I : Type (u + 1)) (T : I → Scheme.{u}) (f : ∀ i, T i ⟶ S),
    Presieve.ofArrows T f ∈ J S ∧
      ∀ i, Nonempty (𝟙_ (Over (T i)) ⟶ (Over.pullback (f i)).obj X)

/-- A pseudo-torsor trivialized by an fpqc covering. -/
@[stacks 049A "part (1)",
  sga "3 IV 5.1.5" "schemes, fpqc",
  sga "3 IV 6.5" "fpqc row",
  sga "3 VIB 10.15" "G-torsor, fpqc T", sga "1 XI 4.1"]
abbrev IsFpqcTorsor (S : Scheme.{u}) (G X : Over S) [GrpObj G] [ModObj G X] : Prop :=
  IsTorsorFor S G X Scheme.fpqcPrecoverage

/-- A pseudo-torsor trivialized by a Zariski covering; equivalently, a locally trivial
torsor. -/
@[stacks 049A "parts (2), (4): Zariski and locally trivial",
  sga "1 XI 4.7",
  sga "3 IV 6.5" "(Zar) row, special case",
  sga "4 IV 5.9" "special case"]
abbrev IsZariskiTorsor (S : Scheme.{u}) (G X : Over S) [GrpObj G] [ModObj G X] : Prop :=
  IsTorsorFor S G X Scheme.zariskiPrecoverage

/-- A pseudo-torsor trivialized by an étale covering; equivalently, a quasi-isotrivial
torsor. -/
@[stacks 049A "parts (2), (3): étale and quasi-isotrivial",
  sga "3 IV 5.1.5" "schemes, étale",
  sga "3 IV 6.5" "étale row", sga "3 VIB 10.15" "G-torsor, étale T"]
abbrev IsEtaleTorsor (S : Scheme.{u}) (G X : Over S) [GrpObj G] [ModObj G X] : Prop :=
  IsTorsorFor S G X Scheme.etalePrecoverage

/-- A pseudo-torsor trivialized by a smooth covering. -/
@[stacks 049A "part (2): smooth"]
abbrev IsSmoothTorsor (S : Scheme.{u}) (G X : Over S) [GrpObj G] [ModObj G X] : Prop :=
  IsTorsorFor S G X (Scheme.precoverage @Smooth)

/-- A pseudo-torsor trivialized by a syntomic covering. -/
@[stacks 049A "part (2): syntomic"]
abbrev IsSyntomicTorsor (S : Scheme.{u}) (G X : Over S) [GrpObj G] [ModObj G X] : Prop :=
  IsPseudoTorsor G X ∧ ∃ (I : Type (u + 1)) (T : I → Scheme.{u}) (f : ∀ i, T i ⟶ S),
    IsSyntomicCovering T f ∧
      ∀ i, Nonempty (𝟙_ (Over (T i)) ⟶ (Over.pullback (f i)).obj X)

/-- A pseudo-torsor trivialized by an fppf covering. -/
@[stacks 049A "part (2): fppf",
  sga "3 IV 5.1.5" "schemes, fppf",
  sga "3 VIB 10.15" "G-torsor, fppf T"]
abbrev IsFppfTorsor (S : Scheme.{u}) (G X : Over S) [GrpObj G] [ModObj G X] : Prop :=
  IsTorsorFor S G X Scheme.fppfPrecoverage

end AlgebraicGeometry

end
