module

public import Mathlib.CategoryTheory.Functor.Const
public import Mathlib.CategoryTheory.Limits.IsLimit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuotientByIdeal
public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstructibleSheaves
public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.AdicSheaves
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Defs

/-!
# Constructible, lisse and adic constructible sheaves of modules on the pro-étale site

Let `Λ` be a Noetherian ring and `I ⊆ Λ` an ideal. A sheaf of `Λ`-modules `F` on the small
pro-étale site of a scheme is a *constructible `Λ`-sheaf* if it is the limit of its quotients
`F / IⁿF` and each of those quotients is a constructible sheaf of `Λ ⧸ Iⁿ`-modules; it is *lisse*
if moreover each quotient is locally constant; and it is *adic constructible* if every affine open
decomposes into constructible locally closed pieces on each of which the sheaf is adic lisse. This
is Stacks Tag 09BT, parts (1), (2) and (4); part (3) is `AlgebraicGeometry.ProEtale.IsAdicLisse`.

The definitions here are the forms of `AlgebraicGeometry.ProEtale.IsConstructibleAdicSheaf`,
`AlgebraicGeometry.ProEtale.IsLisse` and `AlgebraicGeometry.ProEtale.IsAdicConstructible` whose
sections live in the universe `max (u + 1) v w` of the site and the coefficients. There the
sheafification of presheaves of modules exists outright and the inverse image along a morphism of
schemes is `AlgebraicGeometry.ProEtale.proetaleModuleInverseImage`, so the definitions take no
sheafification or adjoint-functor instance arguments; constructibility of the quotients is
`AlgebraicGeometry.ProEtale.IsConstructibleModuleSheaf'` (Tag 09AJ) in the same universe.

## Main definitions

* `AlgebraicGeometry.ProEtale.IsConstructibleAdicModuleSheaf`: Tag 09BT (1), a constructible
  `Λ`-sheaf.
* `AlgebraicGeometry.ProEtale.IsLisseAdicModuleSheaf`: Tag 09BT (2), a lisse constructible
  `Λ`-sheaf.
* `AlgebraicGeometry.ProEtale.IsAdicConstructibleModuleSheaf`: Tag 09BT (4), an adic
  constructible `Λ`-sheaf.

## Main results

* `AlgebraicGeometry.ProEtale.IsLisseAdicModuleSheaf.isConstructibleAdicModuleSheaf`: a lisse
  constructible `Λ`-sheaf is a constructible `Λ`-sheaf.

## Implementation notes

The quotient `F / IⁿF` is not constructed; it is *characterized*, by
`Stacks.ModuleSheaf.IsQuotientBy`, as a morphism out of `F` which is initial among morphisms to
sheaves annihilated by `Iⁿ`. The tower of quotients and the comparison of `F` with its limit are
therefore canonical, and the condition `F = lim F / IⁿF` of the source becomes the requirement
that the cone of quotient maps be a limit cone.

Each quotient is a sheaf of `Λ`-modules annihilated by `Iⁿ`, which the source reads as a sheaf
of `Λ ⧸ Iⁿ`-modules. Here the two are related explicitly: the quotient is required to be
isomorphic to the restriction of scalars of a sheaf `G` of `Λ ⧸ Iⁿ`-modules, and it is `G` of
which constructibility and, for lisse sheaves, local constancy (Tag 093Q (2)) are asked.
Restriction of scalars along the surjection `Λ → Λ ⧸ Iⁿ` is fully faithful, so `G` is determined
by the quotient up to isomorphism, and asking constructibility and local constancy of one and the
same `G` is the source's condition.

Adic constructibility quantifies over affine opens and asks for adic lisseness (Tag 09BT (3)) on
the strata of a `AlgebraicGeometry.Scheme.ConstructibleStratification`. Its strata are indexed by
a `Fin n`, where the source writes an unindexed coproduct `U = ∐ Uᵢ`; this is the same condition,
because the underlying space of an affine open is spectral and the strata are clopen for its
constructible topology, so a disjoint cover by them has only finitely many nonempty members.

## References

* [Stacks Project, Tag 09BT](https://stacks.math.columbia.edu/tag/09BT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.ModuleSheaf

universe w v u

namespace AlgebraicGeometry.ProEtale

variable (X : Scheme.{u}) (Λ : Type v) [CommRing Λ] (I : Ideal Λ)

local instance hasWeakSheafify_proEt_over_moduleCat (Y : Scheme.{u}) (R : Type v) [Ring R]
    (U : Y.ProEt) :
    HasWeakSheafify ((Scheme.ProEt.topology Y).over U) (ModuleCat.{max (u + 1) v w} R) :=
  have := hasSheafify_moduleCat.{u + 1, u, max v w, v} ((Scheme.ProEt.topology Y).over U) R
  inferInstance

local instance hasWeakSheafify_proEt_moduleCat (Y : Scheme.{u}) (R : Type v) [Ring R] :
    HasWeakSheafify (Scheme.ProEt.topology Y) (ModuleCat.{max (u + 1) v w} R) :=
  have := hasSheafify_moduleCat.{u + 1, u, max v w, v} (Scheme.ProEt.topology Y) R
  inferInstance

/-- **Stacks 09BT (1).** A sheaf of `Λ`-modules on the small pro-étale site is a *constructible
`Λ`-sheaf* if it is the limit of its quotients by the powers of `I` and each of those quotients
is, as a sheaf of `Λ ⧸ Iⁿ`-modules, constructible. -/
@[stacks 09BT "part (1): constructible Λ-sheaves"]
def IsConstructibleAdicModuleSheaf [IsNoetherianRing Λ]
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ)) : Prop :=
  ∃ (Q : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ))
      (q : (Functor.const ℕᵒᵖ).obj F ⟶ Q),
    Nonempty (IsLimit (Cone.mk F q)) ∧
      ∀ n : ℕ, IsQuotientBy.{u + 1, u, max (u + 1) v w} (Scheme.ProEt.topology X) Λ (I ^ n) F
          (Q.obj (op n)) (q.app (op n)) ∧
        ∃ G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} (Λ ⧸ I ^ n)),
          Nonempty (Q.obj (op n) ≅
            (restrictQuotientScalars.{u + 1, u, max (u + 1) v w} (Scheme.ProEt.topology X) Λ
              (I ^ n)).obj G) ∧
            IsConstructibleModuleSheaf'.{u, v, w} X (Λ ⧸ I ^ n) G

/-- **Stacks 09BT (2).** A constructible `Λ`-sheaf is *lisse* if each of its quotients by a
power of `I` is a locally constant sheaf of `Λ ⧸ Iⁿ`-modules. -/
@[stacks 09BT "part (2): lisse"]
def IsLisseAdicModuleSheaf [IsNoetherianRing Λ]
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ)) : Prop :=
  ∃ (Q : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ))
      (q : (Functor.const ℕᵒᵖ).obj F ⟶ Q),
    Nonempty (IsLimit (Cone.mk F q)) ∧
      ∀ n : ℕ, IsQuotientBy.{u + 1, u, max (u + 1) v w} (Scheme.ProEt.topology X) Λ (I ^ n) F
          (Q.obj (op n)) (q.app (op n)) ∧
        ∃ G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} (Λ ⧸ I ^ n)),
          Nonempty (Q.obj (op n) ≅
            (restrictQuotientScalars.{u + 1, u, max (u + 1) v w} (Scheme.ProEt.topology X) Λ
              (I ^ n)).obj G) ∧
            IsConstructibleModuleSheaf'.{u, v, w} X (Λ ⧸ I ^ n) G ∧
              Stacks.ConstantSheaf.IsLocallyConstant (Scheme.ProEt.topology X) G

variable {X Λ I} in
/-- A lisse constructible `Λ`-sheaf is a constructible `Λ`-sheaf. -/
theorem IsLisseAdicModuleSheaf.isConstructibleAdicModuleSheaf [IsNoetherianRing Λ]
    {F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ)}
    (hF : IsLisseAdicModuleSheaf.{w} X Λ I F) : IsConstructibleAdicModuleSheaf.{w} X Λ I F := by
  obtain ⟨Q, q, hlim, hQ⟩ := hF
  exact ⟨Q, q, hlim, fun n => ⟨(hQ n).1, (hQ n).2.elim fun G hG => ⟨G, hG.1, hG.2.1⟩⟩⟩

/-- **Stacks 09BT (4).** A sheaf of `Λ`-modules on the small pro-étale site of `X` is *adic
constructible* if every affine open of `X` decomposes into constructible locally closed
subschemes on each of which the inverse image of the sheaf is adic lisse. -/
@[stacks 09BT "part (4): adic constructible"]
def IsAdicConstructibleModuleSheaf
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ)) : Prop :=
  ∀ U : X.affineOpens,
    ∃ s : Scheme.ConstructibleStratification X U.1,
      ∀ i, IsAdicLisse (s.piece i) Λ I
        ((proetaleModuleInverseImage.{u, v, w} (s.inclusion i) Λ).obj F)

end AlgebraicGeometry.ProEtale
