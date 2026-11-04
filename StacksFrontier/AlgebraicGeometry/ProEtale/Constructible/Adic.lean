module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Functor.Const
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Whiskering
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.Defs
public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.AdicSheaves
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Defs

/-!
# Constructible, lisse and adic constructible `Λ`-sheaves on the small pro-étale site

Let `Λ` be a Noetherian ring and `I ⊆ Λ` an ideal. A sheaf of `Λ`-modules on the small
pro-étale site of a scheme is a *constructible `Λ`-sheaf* when it is the inverse limit of its
quotients by the powers of `I` and every such quotient is a constructible sheaf of
`Λ ⧸ Iⁿ`-modules; a constructible `Λ`-sheaf is *lisse* when each of those quotients is
moreover locally constant. Separately, it is *adic constructible* when every affine open of the
base decomposes into constructible locally closed subschemes on each of which the sheaf is adic
lisse.

## Main definitions

* `AlgebraicGeometry.ProEtale.IsAnnihilatedBy`: an ideal kills every local section.
* `AlgebraicGeometry.ProEtale.IsQuotientBy`: the universal property identifying a morphism of
  sheaves of modules as the quotient by an ideal.
* `AlgebraicGeometry.ProEtale.restrictQuotientScalars`: restriction of coefficients from a
  quotient ring, as a functor on pro-étale sheaves of modules.
* `AlgebraicGeometry.ProEtale.IsConstructibleAdicSheaf`: a constructible `Λ`-sheaf.
* `AlgebraicGeometry.ProEtale.IsLisse`: a lisse constructible `Λ`-sheaf.
* `AlgebraicGeometry.ProEtale.IsAdicConstructible`: an adic constructible `Λ`-sheaf.

## References

* [Stacks Project, Tag 09BT](https://stacks.math.columbia.edu/tag/09BT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace AlgebraicGeometry.ProEtale

/-- An ideal annihilates every local section of a sheaf of modules. -/
abbrev IsAnnihilatedBy (X : Scheme.{u}) (Λ : Type v) [CommRing Λ] (J : Ideal Λ)
    (G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)) : Prop :=
  ∀ (U : X.ProEt) (a : Λ), a ∈ J → ∀ x : G.obj.obj (op U), a • x = 0

/-- A morphism of sheaves of modules is *the* quotient by an ideal `J` when its target is
annihilated by `J` and it is initial among morphisms out of its source to sheaves annihilated
by `J`. -/
abbrev IsQuotientBy (X : Scheme.{u}) (Λ : Type v) [CommRing Λ] (J : Ideal Λ)
    (F G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)) (q : F ⟶ G) : Prop :=
  IsAnnihilatedBy X Λ J G ∧
    ∀ H : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ),
      IsAnnihilatedBy X Λ J H → ∀ f : F ⟶ H, ∃! g : G ⟶ H, q ≫ g = f

/-- Restriction of coefficients along `Λ → Λ ⧸ J`, as a functor between the categories of
sheaves of modules on the small pro-étale site. -/
@[implicit_reducible]
def restrictQuotientScalars (X : Scheme.{u}) (Λ : Type v) [CommRing Λ] [UnivLE.{u + 1, w}]
    (J : Ideal Λ) :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{w} (Λ ⧸ J)) ⥤
      Sheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ) := by
  haveI : (Scheme.ProEt.topology X).HasSheafCompose
      (ModuleCat.restrictScalars.{w} (Ideal.Quotient.mk J)) := by
    refine ⟨fun P hP ↦ ?_⟩
    apply Presheaf.isSheaf_of_isSheaf_comp _
      (P ⋙ ModuleCat.restrictScalars (Ideal.Quotient.mk J))
      (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})
    change Presheaf.IsSheaf (Scheme.ProEt.topology X)
      (P ⋙ forget₂ (ModuleCat.{w} (Λ ⧸ J)) AddCommGrpCat.{w})
    exact GrothendieckTopology.HasSheafCompose.isSheaf P hP
  exact sheafCompose (Scheme.ProEt.topology X)
    (ModuleCat.restrictScalars (Ideal.Quotient.mk J))

/-- A sheaf of `Λ`-modules on the small pro-étale site is a *constructible `Λ`-sheaf* if it is
the limit of its quotients by the powers of `I` and each of those quotients is, as a sheaf of
`Λ ⧸ Iⁿ`-modules, constructible. -/
@[stacks 09BT "part (1): constructible Λ-sheaves"]
abbrev IsConstructibleAdicSheaf (X : Scheme.{u}) (Λ : Type v) [CommRing Λ] [IsNoetherianRing Λ]
    [UnivLE.{u + 1, w}] (I : Ideal Λ)
    [∀ (n : ℕ) (Y : Scheme.{u}),
      HasWeakSheafify (Scheme.ProEt.topology Y) (ModuleCat.{w} (Λ ⧸ I ^ n))]
    [∀ (n : ℕ) (Y : Scheme.{u}) (V : Y.ProEt),
      HasWeakSheafify ((Scheme.ProEt.topology Y).over V) (ModuleCat.{w} (Λ ⧸ I ^ n))]
    [∀ (n : ℕ) {Z Y : Scheme.{u}} (f : Z ⟶ Y),
      ((Scheme.proetaleBaseChange f).sheafPushforwardContinuous
        (ModuleCat.{w} (Λ ⧸ I ^ n)) (Scheme.ProEt.topology Y)
        (Scheme.ProEt.topology Z)).IsRightAdjoint]
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)) : Prop :=
  ∃ (Q : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ))
      (q : (Functor.const ℕᵒᵖ).obj F ⟶ Q),
    Nonempty (IsLimit (Cone.mk F q)) ∧
      ∀ n : ℕ, IsQuotientBy X Λ (I ^ n) F (Q.obj (op n)) (q.app (op n)) ∧
        ∃ G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{w} (Λ ⧸ I ^ n)),
          Nonempty (Q.obj (op n) ≅ (restrictQuotientScalars X Λ (I ^ n)).obj G) ∧
            IsConstructibleModuleSheaf X (Λ ⧸ I ^ n) G

/-- A constructible `Λ`-sheaf is *lisse* if each of its quotients by a power of `I` is a locally
constant sheaf of `Λ ⧸ Iⁿ`-modules. -/
@[stacks 09BT "part (2): lisse"]
abbrev IsLisse (X : Scheme.{u}) (Λ : Type v) [CommRing Λ] [IsNoetherianRing Λ]
    [UnivLE.{u + 1, w}] (I : Ideal Λ)
    [∀ (n : ℕ) (Y : Scheme.{u}),
      HasWeakSheafify (Scheme.ProEt.topology Y) (ModuleCat.{w} (Λ ⧸ I ^ n))]
    [∀ (n : ℕ) (Y : Scheme.{u}) (V : Y.ProEt),
      HasWeakSheafify ((Scheme.ProEt.topology Y).over V) (ModuleCat.{w} (Λ ⧸ I ^ n))]
    [∀ (n : ℕ) {Z Y : Scheme.{u}} (f : Z ⟶ Y),
      ((Scheme.proetaleBaseChange f).sheafPushforwardContinuous
        (ModuleCat.{w} (Λ ⧸ I ^ n)) (Scheme.ProEt.topology Y)
        (Scheme.ProEt.topology Z)).IsRightAdjoint]
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)) : Prop :=
  IsConstructibleAdicSheaf X Λ I F ∧
    ∀ n : ℕ,
      ∃ G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{w} (Λ ⧸ I ^ n)),
        ∃ q : F ⟶ (restrictQuotientScalars X Λ (I ^ n)).obj G,
          IsQuotientBy X Λ (I ^ n) F _ q ∧
            Stacks.ConstantSheaf.IsLocallyConstant (Scheme.ProEt.topology X) G

/-- A sheaf of `Λ`-modules on the small pro-étale site of `X` is *adic constructible* if every
affine open of `X` decomposes into constructible locally closed subschemes on each of which the
inverse image of the sheaf is adic lisse. -/
@[stacks 09BT "part (4): adic constructible"]
abbrev IsAdicConstructible (X : Scheme.{u}) (Λ : Type v) [CommRing Λ] (I : Ideal Λ)
    [∀ Y : Scheme.{u}, HasWeakSheafify (Scheme.ProEt.topology Y) (ModuleCat.{w} Λ)]
    [∀ (Y : Scheme.{u}) (V : Y.ProEt),
      HasWeakSheafify ((Scheme.ProEt.topology Y).over V) (ModuleCat.{w} Λ)]
    [∀ {Z Y : Scheme.{u}} (f : Z ⟶ Y),
      ((Scheme.proetaleBaseChange f).sheafPushforwardContinuous
        (ModuleCat.{w} Λ) (Scheme.ProEt.topology Y)
        (Scheme.ProEt.topology Z)).IsRightAdjoint]
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)) : Prop :=
  ∀ U : X.affineOpens,
    ∃ s : Scheme.ConstructibleStratification X U.1,
      ∀ i, IsAdicLisse (s.piece i) Λ I
        (((Scheme.proetaleBaseChange (s.inclusion i)).sheafPullback
          (ModuleCat.{w} Λ) (Scheme.ProEt.topology X)
          (Scheme.ProEt.topology (s.piece i))).obj F)

end AlgebraicGeometry.ProEtale

end
