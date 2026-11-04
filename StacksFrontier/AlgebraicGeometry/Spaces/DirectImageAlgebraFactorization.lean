module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleCompIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback

/-!
# The direct-image algebra of a morphism of algebraic spaces and its relative spectrum

Let `f : Y ⟶ X` be a quasi-compact, quasi-separated morphism of algebraic spaces over a
scheme `S`.  Then `f_* 𝒪_Y` is a quasi-coherent `𝒪_X`-algebra, and `f` factors canonically as

`Y ⟶ \underline{Spec}_X(f_* 𝒪_Y) ⟶ X`.

Quasi-coherence of `f_* 𝒪_Y` comes from quasi-coherence of the direct image of a quasi-coherent
module along a quasi-compact quasi-separated morphism, Stacks 03M9, which is a hypothesis of
`AlgebraicGeometry.Space.isQuasicoherent_pushforwardAlgebra`: the content proved here is that
the module underlying the algebra `f_* 𝒪_Y` is the direct image of `𝒪_Y`.  The factorization is
read off the anti-equivalence of Stacks 081V and its base-change compatibility, which are the
parameters `E` and `C`.

## Main definitions

* `AlgebraicGeometry.Space.pushforwardAlgebraIdIso` identifies `(𝟙_Y)_* 𝒪_Y` with `𝒪_Y` as
  `𝒪_Y`-algebras.
* `AlgebraicGeometry.Space.directImageFactorizationMap` is the canonical morphism
  `Y ⟶ \underline{Spec}_X(f_* 𝒪_Y)` over `X`, and
  `AlgebraicGeometry.Space.qcqsDirectImageFactorizationMap` is the same morphism for a
  quasi-compact, quasi-separated `f`, whose direct-image algebra is quasi-coherent.

## Main results

* `AlgebraicGeometry.Space.isTerminalIdAffineOver`: an algebraic space is terminal among the
  algebraic spaces affine over it, and
  `AlgebraicGeometry.Space.isInitialUnitQuasicoherentAlgebra`: its structure sheaf is the
  initial quasi-coherent algebra on it.
* `AlgebraicGeometry.Space.underlyingModule_pushforwardAlgebra`: the `𝒪_X`-module underlying
  the algebra `f_* 𝒪_Y` is the direct image of `𝒪_Y`.
* `AlgebraicGeometry.Space.isQuasicoherent_pushforwardAlgebra`: for a quasi-compact,
  quasi-separated `f` the algebra `f_* 𝒪_Y` is quasi-coherent.
* `AlgebraicGeometry.Space.directImageFactorizationMap_factorization` and
  `AlgebraicGeometry.Space.qcqsDirectImageFactorizationMap_factorization`: the canonical morphism
  composed with the structure morphism of `\underline{Spec}_X(f_* 𝒪_Y)` is `f`.

## Implementation notes

The identification `(𝟙_Y)_* 𝒪_Y ≅ 𝒪_Y` is obtained from the anti-equivalence rather than from
the identity clause of Stacks 03G8: `Y` over itself is the terminal algebraic space affine over
`Y` and `𝒪_Y` is the initial quasi-coherent `𝒪_Y`-algebra, so the anti-equivalence matches them,
and it matches the first with `(𝟙_Y)_* 𝒪_Y`.

## References

* [Stacks Project, Tag 081X](https://stacks.math.columbia.edu/tag/081X)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### `Y` over itself is terminal, and `𝒪_Y` is the initial algebra -/

/-- An algebraic space is the terminal object among the algebraic spaces affine over it. -/
def isTerminalIdAffineOver (Y : AlgebraicSpaces B S hS) :
    IsTerminal (idAffineOver B S hS Y) :=
  IsTerminal.ofUniqueHom
    (fun Z => ObjectProperty.homMk (Over.homMk Z.obj.hom (by simp [idAffineOver])))
    (fun Z m => by
      apply ObjectProperty.hom_ext
      have h : m.hom.left = Z.obj.hom := by simpa [idAffineOver] using Over.w m.hom
      exact Over.OverMorphism.ext h)

/-- A morphism of algebra sheaves out of `𝒪_Y`, viewed as an algebra over itself, is the
structure map of its target. -/
theorem unitAlgebra_hom_right {Y : AlgebraicSpaces B S hS}
    {A : AlgebraSheaf.{u, u} B S hS Y.1 Y.2} (m : unitAlgebra B S hS Y ⟶ A) :
    m.right = A.hom := by
  ext U r
  exact m.comm U r

/-- The structure sheaf is the initial quasi-coherent algebra on an algebraic space. -/
def isInitialUnitQuasicoherentAlgebra (Y : AlgebraicSpaces B S hS) :
    IsInitial (unitQuasicoherentAlgebra B S hS Y) :=
  IsInitial.ofUniqueHom
    (fun A => ObjectProperty.homMk ⟨A.obj.hom, fun _ _ => rfl⟩)
    (fun A m => by
      apply ObjectProperty.hom_ext
      exact AlgebraSheaf.Hom.ext (unitAlgebra_hom_right B S hS m.hom))

/-! ### The direct image of `𝒪_Y` along the identity -/

variable (E : AffineAlgebraAntiEquivalence B S hS)

/-- The anti-equivalence sends `Y` over itself to the initial quasi-coherent algebra on `Y`. -/
def isInitialFunctorObjIdAffineOver (Y : AlgebraicSpaces B S hS) :
    IsInitial ((E.equivalence Y).functor.obj (op (idAffineOver B S hS Y))) :=
  ((isTerminalIdAffineOver B S hS Y).op).isInitialObj (E.equivalence Y).functor _

/-- The anti-equivalence matches `Y` over itself with `𝒪_Y`: both are universal, the first as
the terminal algebraic space affine over `Y` and the second as the initial quasi-coherent
`𝒪_Y`-algebra. -/
def unitQuasicoherentAlgebraIso (Y : AlgebraicSpaces B S hS) :
    unitQuasicoherentAlgebra B S hS Y ≅
      (E.equivalence Y).functor.obj (op (idAffineOver B S hS Y)) :=
  (isInitialUnitQuasicoherentAlgebra B S hS Y).uniqueUpToIso
    (isInitialFunctorObjIdAffineOver B S hS E Y)

/-- The direct image of `𝒪_Y` along the identity of `Y` is `𝒪_Y`, as an `𝒪_Y`-algebra. -/
def pushforwardAlgebraIdIso (Y : AlgebraicSpaces B S hS) :
    pushforwardAlgebra B S hS (idAffineOver B S hS Y).obj ≅ unitAlgebra B S hS Y :=
  (E.pushforward_obj Y (idAffineOver B S hS Y)).symm ≪≫
    (quasicoherentAlgebraInclusion B S hS Y).mapIso
      (((E.pushforwardIso Y).app (op (idAffineOver B S hS Y))).symm ≪≫
        (unitQuasicoherentAlgebraIso B S hS E Y).symm)

/-! ### Quasi-coherence of the direct-image algebra -/

variable {X Y : AlgebraicSpaces B S hS}

/-- The `𝒪_X`-module underlying the algebra `f_* 𝒪_Y` is the direct image of `𝒪_Y`. -/
theorem underlyingModule_pushforwardAlgebra (f : Y ⟶ X) :
    (pushforwardAlgebra B S hS (Over.mk f)).underlyingModule =
      (modulePushforward B S hS f).obj (SheafOfModules.unit (structureRingSheaf B S hS Y)) :=
  congrArg
    (fun G : Modules.{u, u} B S hS Y.1 Y.2 ⥤ Modules.{u, u} B S hS X.1 X.2 =>
      G.obj (SheafOfModules.unit (structureRingSheaf B S hS Y)))
    (pushforwardModules_eq_modulePushforward B S hS f)

/-- **The direct image of the structure sheaf along a quasi-compact, quasi-separated morphism of
algebraic spaces is a quasi-coherent algebra.**  The hypothesis `h03M9` is Stacks 03M9, that such
a direct image preserves quasi-coherence of modules. -/
@[stacks 081X "quasi-coherence of the pushforward algebra"]
theorem isQuasicoherent_pushforwardAlgebra (f : Y ⟶ X)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (h03M9 : IsQuasiCompact B S hS f.hom → IsQuasiSeparated B S hS f.hom →
      ∀ F : Modules.{u, u} B S hS Y.1 Y.2, F.IsQuasicoherentOnSite →
        ((modulePushforward B S hS f).obj F).IsQuasicoherentOnSite) :
    (pushforwardAlgebra B S hS (Over.mk f)).IsQuasicoherent := by
  have h := h03M9 hfqc hfqs _
    (SheafOfModules.isQuasicoherentOnSite_unit (structureRingSheaf B S hS Y))
  rwa [← underlyingModule_pushforwardAlgebra] at h

/-! ### The canonical factorization -/

variable (C : BaseChangeCompatibility B S hS E)

/-- **The canonical morphism `Y ⟶ \underline{Spec}_X(f_* 𝒪_Y)` over `X`** attached to a morphism
`f : Y ⟶ X` whose direct-image algebra `f_* 𝒪_Y` is quasi-coherent. -/
def directImageFactorizationMap (f : Y ⟶ X)
    (hqc : (pushforwardAlgebra B S hS (Over.mk f)).IsQuasicoherent) :
    Over.mk f ⟶ (relativeSpecDirectImage B S hS E f hqc).obj :=
  relativeSpecDirectImageMap B S hS E C f hqc (pushforwardAlgebraIdIso B S hS E Y)

/-- **The canonical factorization `Y ⟶ \underline{Spec}_X(f_* 𝒪_Y) ⟶ X`.**  The canonical
morphism composed with the structure morphism of the relative spectrum of `f_* 𝒪_Y` is `f`. -/
@[stacks 081X "the canonical factorization"]
theorem directImageFactorizationMap_factorization (f : Y ⟶ X)
    (hqc : (pushforwardAlgebra B S hS (Over.mk f)).IsQuasicoherent) :
    (directImageFactorizationMap B S hS E C f hqc).left ≫
        (relativeSpecDirectImage B S hS E f hqc).obj.hom = f :=
  Over.w _

/-- The structure morphism `\underline{Spec}_X(f_* 𝒪_Y) ⟶ X` of the middle term of the
factorization is affine. -/
theorem isAffineHom_relativeSpecDirectImage (f : Y ⟶ X)
    (hqc : (pushforwardAlgebra B S hS (Over.mk f)).IsQuasicoherent) :
    IsAffineHom B S hS (relativeSpecDirectImage B S hS E f hqc).obj.hom.hom :=
  (relativeSpecDirectImage B S hS E f hqc).property

/-! ### The factorization for a quasi-compact, quasi-separated morphism -/

variable (f : Y ⟶ X) (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom)
    (h03M9 : IsQuasiCompact B S hS f.hom → IsQuasiSeparated B S hS f.hom →
      ∀ F : Modules.{u, u} B S hS Y.1 Y.2, F.IsQuasicoherentOnSite →
        ((modulePushforward B S hS f).obj F).IsQuasicoherentOnSite)

/-- The relative spectrum `\underline{Spec}_X(f_* 𝒪_Y)` of the direct-image algebra of a
quasi-compact, quasi-separated morphism, as an algebraic space affine over `X`. -/
def qcqsRelativeSpecDirectImage : AffineOver B S hS X :=
  relativeSpecDirectImage B S hS E f
    (isQuasicoherent_pushforwardAlgebra B S hS f hfqc hfqs h03M9)

/-- **The canonical morphism `Y ⟶ \underline{Spec}_X(f_* 𝒪_Y)` over `X`** attached to a
quasi-compact, quasi-separated morphism `f : Y ⟶ X` of algebraic spaces. -/
def qcqsDirectImageFactorizationMap :
    Over.mk f ⟶ (qcqsRelativeSpecDirectImage B S hS E f hfqc hfqs h03M9).obj :=
  directImageFactorizationMap B S hS E C f
    (isQuasicoherent_pushforwardAlgebra B S hS f hfqc hfqs h03M9)

/-- **Stacks 081X.** A quasi-compact, quasi-separated morphism `f : Y ⟶ X` of algebraic spaces
factors canonically as `Y ⟶ \underline{Spec}_X(f_* 𝒪_Y) ⟶ X`. -/
@[stacks 081X "the canonical factorization of a quasi-compact quasi-separated morphism"]
theorem qcqsDirectImageFactorizationMap_factorization :
    (qcqsDirectImageFactorizationMap B S hS E C f hfqc hfqs h03M9).left ≫
        (qcqsRelativeSpecDirectImage B S hS E f hfqc hfqs h03M9).obj.hom = f :=
  Over.w _

end AlgebraicGeometry.Space

end
