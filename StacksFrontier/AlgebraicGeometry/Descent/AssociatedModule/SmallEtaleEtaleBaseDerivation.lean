module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAssociatedDerivation
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Differentials

/-!
# `d^a` annihilates the functions pulled back from an étale scheme over `Y`

Let `f : X ⟶ Y` be a morphism of schemes with `X` in a big étale site `B`, and let
`d^a : 𝒪_{X_étale} ⟶ (Ω_{X/Y})^a` be the derivation of Stacks 04CS,
`AlgebraicGeometry.SmallEtale.associatedDerivation`.  That it annihilates every function pulled
back from an *open* of `Y` is
`AlgebraicGeometry.SmallEtale.associatedDerivation_pullbackSection_eq_zero`.  This module proves
the stronger vanishing that the invertibility clause of Stacks 04CS needs: `d^a` annihilates
every function pulled back from a scheme `W` *étale over* `Y`.

Concretely, let `V` be an object of the small étale site of `X`, with scheme `T` and structure
morphism `h : T ⟶ X`, let `w : W ⟶ Y` be étale, and let `g : T ⟶ W` be a morphism over `Y`, so
`g ≫ w = h ≫ f`.  Then `d^a` over `V` kills `g^♯t` for every global function `t` on `W`.

The reason is that `Ω_{W/Y} = 0` for `w` étale, so the canonical morphism of Stacks 01UV for the
square `g : T ⟶ W` over `𝟙 Y` carries `d_{W/Y}t = 0` to `d_{T/Y}(g^♯t)`.  The vanishing of
`Ω_{W/Y}` is Stacks 02H9
(`AlgebraicGeometry.Scheme.Hom.formallyUnramified_iff_isZero_relativeDifferentials`, through the
instance that an étale morphism is formally unramified), and the transfer is the
characterizing property of the canonical morphism, in the shape already used by
`AlgebraicGeometry.etaleAssociatedDerivation_naturality`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.universalRelativeDerivation_d_eq_zero_of_etale`: the universal
  relative derivation of an étale morphism is zero, since its sheaf of relative differentials
  is a zero object.
* `AlgebraicGeometry.Scheme.Hom.universalRelativeDerivation_d_appTop_eq_zero_of_etaleBase`: if
  `p : T ⟶ Y` factors as `g ≫ w` with `w` étale, then `d_{T/Y}` annihilates the global
  functions pulled back along `g`.
* `AlgebraicGeometry.etaleAssociatedDerivation_etaleBase_eq_zero`: the same vanishing for the
  objectwise values `AlgebraicGeometry.etaleAssociatedDerivation` of `d^a`.
* `AlgebraicGeometry.SmallEtale.associatedSectionsDerivation_etaleBase_eq_zero` and
  `AlgebraicGeometry.SmallEtale.associatedDerivation_etaleBase_eq_zero`: the vanishing for `d^a`
  itself, over an object of the small étale site of `X`.

## Implementation notes

**What this is for.**  Stacks 04CS compares `(Ω_{X/Y})^a` with `Ω_{X_étale/Y_étale}`, the module
of differentials of the structure map `f_{small}^{-1}𝒪_{Y_étale} ⟶ 𝒪_{X_étale}` of the morphism
of small étale ringed topoi of `f`
(`AlgebraicGeometry.smallEtaleRingedToposHom`, whose structure map in direct-image form is
`AlgebraicGeometry.structureSharp`: at an étale `W / Y` it pulls a global function on `W` back
along the projection `X ×_Y W ⟶ W`, by
`AlgebraicGeometry.structureSharp_hom_app`).  What
`AlgebraicGeometry.SmallEtale.existsUnique_postcomp_associatedDerivation` corepresents is instead
the derivations annihilating `AlgebraicGeometry.SmallEtale.pullbackSection`, the functions pulled
back from the *opens* of `Y`.  Identifying the two classes of derivations is what the comparison
of 04CS needs, and the vanishing proved here is the direction that is not formal: the
sections of `𝒪_{X_étale}` in the image of `f_{small}^♯` are exactly those of the shape treated
here, with `T = X ×_Y W` and `g` the projection.

That identification is now carried out in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleDifferentialsIso.lean`, where
this vanishing becomes `AlgebraicGeometry.SmallEtale.etaleAssociatedDerivation` and the
comparison of the two classes gives the canonical isomorphism of Stacks 04CS,
`AlgebraicGeometry.SmallEtale.differentialsIso`.

**The vanishing is stated for a general factorization, not for the base change.**  Nothing in
the proof uses that `T ⟶ W` is a projection from a fibre product; only `g ≫ w = h ≫ f` and the
étaleness of `w` are used.  So the statement applies to whatever object of the small étale site
of `X` a consumer holds, without first matching it with a fibre product.

## References

* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 02H9](https://stacks.math.columbia.edu/tag/02H9), the vanishing of the
  sheaf of relative differentials of a formally unramified morphism.
* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV), the canonical morphism
  of relative differentials of a commutative square and its characterizing property.
* [Stacks Project, Tag 04BX](https://stacks.math.columbia.edu/tag/04BX), the étale localization
  of relative differentials, through which `d^a` is defined.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- **The universal relative derivation of an étale morphism is zero.**  An étale morphism is
formally unramified, so its sheaf of relative differentials is a zero object (Stacks 02H9) and
its sections over any open form a subsingleton. -/
public theorem universalRelativeDerivation_d_eq_zero_of_etale {W Y : Scheme.{u}} (w : W ⟶ Y)
    [Etale w] (U : W.Opens) (t : Γ(W, U)) :
    (universalRelativeDerivation w).d t = 0 := by
  have hz : IsZero (relativeDifferentials w) :=
    isZero_relativeDifferentials_of_formallyUnramified w
  have hsec : IsZero ((relativeDifferentials w).val.obj (op U)) :=
    Functor.map_isZero (PresheafOfModules.evaluation W.ringCatSheaf.obj (op U))
      (Functor.map_isZero (Scheme.Modules.toPresheafOfModules W) hz)
  have : Subsingleton ((relativeDifferentials w).val.obj (op U)) :=
    ModuleCat.isZero_iff_subsingleton.mp hsec
  exact Subsingleton.elim _ _

/-- **`d_{T/Y}` annihilates the global functions pulled back from a scheme étale over `Y`.**  If
`p : T ⟶ Y` factors as `g ≫ w` with `w : W ⟶ Y` étale, then the universal `Y`-derivation of `T`
kills `g^♯t` for every global function `t` on `W`.

The canonical morphism of Stacks 01UV for the square with horizontal edges `g` and `𝟙 Y` carries
`d_{W/Y}t` to `d_{T/Y}(g^♯t)`, and `d_{W/Y}t = 0` by
`AlgebraicGeometry.Scheme.Hom.universalRelativeDerivation_d_eq_zero_of_etale`. -/
public theorem universalRelativeDerivation_d_appTop_eq_zero_of_etaleBase {T W Y : Scheme.{u}}
    (p : T ⟶ Y) (w : W ⟶ Y) [Etale w] (g : T ⟶ W) (hg : g ≫ w = p)
    (t : Γ(W, (⊤ : W.Opens))) :
    (universalRelativeDerivation p).d (g.appTop.hom t) = 0 := by
  subst hg
  have hcomm : g ≫ w = (g ≫ w) ≫ 𝟙 Y := by simp
  have hd := (isRelativeDifferentialsMap_iff_eq g w (g ≫ w) (𝟙 Y) hcomm _).mpr rfl ⊤ t
  rw [universalRelativeDerivation_d_eq_zero_of_etale w ⊤ t, map_zero] at hd
  exact hd.symm

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry

/-- **The objectwise values of `d^a` annihilate the functions pulled back from a scheme étale
over `Y`.**  For an étale `h : T ⟶ X`, an étale `w : W ⟶ Y` and a morphism `g : T ⟶ W` over `Y`,
the value of `d^a` over `T` kills `g^♯t` for every global function `t` on `W`.

`AlgebraicGeometry.etaleAssociatedDerivation` is the universal derivation `d_{T/Y}` followed by
an additive map, so this is the vanishing of `d_{T/Y}` on those sections. -/
public theorem etaleAssociatedDerivation_etaleBase_eq_zero {X Y T W : Scheme.{u}} (f : X ⟶ Y)
    (h : T ⟶ X) [Etale h] (w : W ⟶ Y) [Etale w] (g : T ⟶ W) (hg : g ≫ w = h ≫ f)
    (t : Γ(W, (⊤ : W.Opens))) :
    etaleAssociatedDerivation f h (g.appTop.hom t) = 0 :=
  Eq.trans (congrArg (Scheme.Modules.Hom.app
      (Scheme.Hom.etaleRelativeDifferentialsIso h f (h ≫ f) rfl).inv (⊤ : T.Opens))
    (Scheme.Hom.universalRelativeDerivation_d_appTop_eq_zero_of_etaleBase (h ≫ f) w g hg t))
    (map_zero _)

namespace SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : Scheme.{u}} (hX : B.Contains X) (f : X ⟶ Y)

/-- **`d^a`, in its sections form, annihilates the functions pulled back from a scheme étale over
`Y`.**  Over an object `V` of the small étale site of `X` with scheme `T` and structure morphism
`h`, and for an étale `w : W ⟶ Y` and a morphism `g : T ⟶ W` over `Y`, the derivation kills
`g^♯t` for every global function `t` on `W`. -/
public theorem associatedSectionsDerivation_etaleBase_eq_zero {W : Scheme.{u}} (w : W ⟶ Y)
    [Etale w] (V : (SmallEtale B X hX)ᵒᵖ) (g : objScheme B X hX V.unop ⟶ W)
    (hg : g ≫ w = objHom B X hX V.unop ≫ f) (t : Γ(W, (⊤ : W.Opens))) :
    (associatedSectionsDerivation B hX f).d (g.appTop.hom t) = 0 :=
  etaleAssociatedDerivation_etaleBase_eq_zero f (objHom B X hX V.unop) w g hg t

/-- **`d^a` annihilates the functions pulled back from a scheme étale over `Y`.**  This is
`AlgebraicGeometry.SmallEtale.associatedSectionsDerivation_etaleBase_eq_zero` carried along the
isomorphism of Stacks 070S (2) which turns the sections form of `(Ω_{X/Y})^a` into
`(Ω_{X/Y})^a` itself.

It strengthens `AlgebraicGeometry.SmallEtale.associatedDerivation_pullbackSection_eq_zero`, whose
sections come from the opens of `Y` rather than from an arbitrary scheme étale over `Y`. -/
public theorem associatedDerivation_etaleBase_eq_zero {W : Scheme.{u}} (w : W ⟶ Y) [Etale w]
    (V : (SmallEtale B X hX)ᵒᵖ) (g : objScheme B X hX V.unop ⟶ W)
    (hg : g ≫ w = objHom B X hX V.unop ≫ f) (t : Γ(W, (⊤ : W.Opens))) :
    (associatedDerivation B hX f).d (g.appTop.hom t) = 0 :=
  Eq.trans (PresheafOfModules.Derivation.postcomp_d_apply (associatedSectionsDerivation B hX f)
      (associatedModuleIsoSectionsSheaf B X hX (Scheme.Hom.relativeDifferentials f)).inv.val _)
    (Eq.trans (congrArg _
      (associatedSectionsDerivation_etaleBase_eq_zero B hX f w V g hg t)) (map_zero _))

end SmallEtale

end AlgebraicGeometry

end
