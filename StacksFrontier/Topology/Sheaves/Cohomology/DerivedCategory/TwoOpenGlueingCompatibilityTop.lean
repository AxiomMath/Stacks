module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.TwoOpenGlueingCompatibility

/-!
# The compatibility clause of the two-open glueing problem over the ambient open

Let `(X, 𝒪_X)` be a ringed space and `S` a system of locally given derived objects on it, as in
Situation 0D67.  The object part of the two-open glueing statement is proved with nothing
assumed (`Stacks.DerivedGlueing.twoOpenGlueingObjectsOver_top`); what the transport of
[Stacks, Tag 08DG] into that situation still owes is the *compatibility clause*,
`Stacks.DerivedGlueing.TwoOpenGlueingOver S U V ⊤ le_top le_top`.

This file isolates what that clause needs.  The glueing datum produced by
`Stacks.Cohomology.GlueingComplexes.exists_glueing` carries its own compatibility, stated
against `Stacks.Cohomology.GlueingComplexes.overlapIso`; the clause of `TwoOpenGlueingOver` is
stated against `Stacks.DerivedGlueing.LocallyGiven.restrictionComp`.  Everything between the two
is a diagram chase, and what is left over after the chase is **one** equation: the coherence of
the dictionary between the displayed restriction of a system and derived restriction along an
open immersion, for a chain `W ≤ U ≤ ⊤` of opens.

## Main definitions

* `Stacks.DerivedGlueing.LocallyGiven.restrictionIsoDerivedRestrictIncl`: **the dictionary at a
  pair of opens.**  For `W ≤ U` the displayed restriction from `U` to `W` is derived restriction
  along the inclusion `Stacks.DerivedGlueing.restrictIncl` of the open subspace `W` into the open
  subspace `U`.  It is the dictionary of
  `Stacks.DerivedGlueing.LocallyGiven.restrictionIsoDerivedRestrict`, followed by the
  factorisation `Stacks.DerivedGlueing.restrictInclDerivedIso` of [Stacks, Tag 0D5S] and by the
  cancellation `Stacks.DerivedGlueing.derivedRestrictJShriekIso` of extension by zero against its
  own restriction.

## Main results

* `Stacks.DerivedGlueing.overlapIso_hom_app_eq`:
  `Stacks.DerivedGlueing.overlapIso_eq_restrictInclDerivedIso` read at an object.
* `Stacks.DerivedGlueing.glueCompat_eq`: the chase, in a single arbitrary category with every
  object and every morphism a variable.
* `Stacks.DerivedGlueing.glueing_compatible_eq`:
  `Stacks.Cohomology.GlueingComplexes.Glueing.compatible` read as the equation it unfolds to, at
  a variable square and a variable datum.
* `Stacks.DerivedGlueing.nonempty_glueing_restrictIncl` and
  `Stacks.DerivedGlueing.exists_glueing_restrictIncl`: [Stacks, Tag 08DG] at the Cartesian square
  of two opens, with its compatibility clause read through
  `Stacks.DerivedGlueing.restrictInclDerivedIso`.
* `Stacks.DerivedGlueing.twoOpenGlueingOver_top_compat`: the compatibility clause for one
  glueing datum, with the glued object and both identifications variables.
* `Stacks.DerivedGlueing.twoOpenGlueingOver_top_of_coherence`: **the compatibility clause over
  the ambient open, from the coherence of the dictionary alone.**

## Implementation notes

The chase is isolated as `Stacks.DerivedGlueing.glueCompat_eq` and applied by `exact`, with every
object and morphism implicit so that each is read off the goal rather than re-elaborated: the
morphisms involved live in four different derived categories, and writing one of them out in
argument position — `Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical`, say —
costs the whole heartbeat budget by itself.  For the same reason the glued object's two
identifications are handed to the chase through
`Stacks.DerivedGlueing.twoOpenGlueingOver_top_compat`, where they are *variables* constrained by
their factorisations, rather than written out at the point of use.

The glueing datum given to [Stacks, Tag 08DG] here is the prescribed identification conjugated by
the dictionary, written out directly rather than through
`Stacks.DerivedGlueing.overlapIsoOfRestriction`.  The two agree, but proving that they agree
means normalising a chain of five isomorphisms on each side across the two spellings of the
structure sheaf of an open subspace, which `simp` does not do: the goal is not type-correct at
the transparency at which it matches, so it silently makes no progress.

## References

* [Stacks Project, Tag 08DG](https://stacks.math.columbia.edu/tag/08DG)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D6A](https://stacks.math.columbia.edu/tag/0D6A)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ExtensionByZeroModules RingedSpaceModuleAdjunction
open Stacks.Cohomology.GlueingComplexes

namespace Stacks.DerivedGlueing

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-! ### The dictionary at a pair of opens -/

/-- **The displayed restriction from `U` to a smaller open `W` is derived restriction along the
inclusion of open subspaces.**

Three identifications in succession: the displayed restriction is extension by zero along `U`
followed by derived restriction to `W`
(`Stacks.DerivedGlueing.LocallyGiven.restrictionIsoDerivedRestrict`); that derived restriction
factors through the open subspace `U` (`Stacks.DerivedGlueing.restrictInclDerivedIso`, the
composition isomorphism of [Stacks, Tag 0D5S]); and restricting to `U` the extension by zero
from `U` is the identity (`Stacks.DerivedGlueing.derivedRestrictJShriekIso`).

Derived restriction along `Stacks.DerivedGlueing.restrictIncl` is the functor
`Stacks.Cohomology.GlueingComplexes.exists_glueing` restricts with at the Cartesian square of
`Stacks.DerivedGlueing.isPullback_restrictIncl`, so this is the form in which the glueing datum
of Situation 0D67 has to be presented to [Stacks, Tag 08DG]. -/
def LocallyGiven.restrictionIsoDerivedRestrictIncl (S : LocallyGiven X)
    {W U : Opens X.carrier} (hWU : W ≤ U) :
    S.restriction W U hWU ≅ derivedRestrict (restrictIncl (X := X) hWU) :=
  S.restrictionIsoDerivedRestrict U W hWU ≪≫
    Functor.isoWhiskerLeft ((jShriek U (underlyingRingSheaf X)).mapDerivedCategory)
      (restrictInclDerivedIso (X := X) hWU) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (derivedRestrictJShriekIso U)
      (derivedRestrict (restrictIncl (X := X) hWU)) ≪≫
    Functor.leftUnitor _

/-- `Stacks.DerivedGlueing.overlapIso_eq_restrictInclDerivedIso` read at an object.  The
splitting of the components holds by definition and is taken here as a definitional unification
against a stated type rather than by `simp only [NatTrans.comp_app]`, which does not fire on a
goal mixing the two spellings of the structure sheaf of an open subspace. -/
theorem overlapIso_hom_app_eq (U V : Opens X.carrier)
    (N : DerivedCategory (SheafOfModules.{u} (underlyingRingSheaf X))) :
    (overlapIso (X.ofRestrict U.isOpenEmbedding) (X.ofRestrict V.isOpenEmbedding)
        (restrictIncl (X := X) (inf_le_left : U ⊓ V ≤ U))
        (restrictIncl (X := X) (inf_le_right : U ⊓ V ≤ V))
        (isPullback_restrictIncl U V).w).hom.app N =
      (restrictInclDerivedIso (X := X) (inf_le_left : U ⊓ V ≤ U)).inv.app N ≫
        (restrictInclDerivedIso (X := X) (inf_le_right : U ⊓ V ≤ V)).hom.app N :=
  congrArg (fun e => e.hom.app N) (overlapIso_eq_restrictInclDerivedIso U V)

/-! ### The chase -/

/-- **The diagram chase behind
`Stacks.DerivedGlueing.twoOpenGlueingOver_top_compat`**, in a single arbitrary category with
every object and every morphism a variable.

Read `rcU`, `RUf`, `cc` as the three factors of the left-hand side of the compatibility clause;
`kUAh`/`kUAi` and `kUF` as the dictionary; `pU`, `qU`, `Df` as the three factors of the
restricted identification; `rU`, `rU'` as the composition isomorphism of [Stacks, Tag 0D5S];
`m` as the derived restriction of the counit at `⊤`; `phiW` as the dictionary over the
intersection.  After the three cancellation equations the hypotheses are, in order: naturality
of the dictionary, functoriality, the coherence of the dictionary, naturality of the composition
isomorphism — each four in turn on the `U` and on the `V` side — the cancellation of the
composition isomorphism, and the compatibility clause of the glueing datum produced by
[Stacks, Tag 08DG].

The two components of each of the two dictionary isomorphisms are taken as *morphisms* with
their cancellations as hypotheses, rather than as `CategoryTheory.Iso`s: at the point of use
they arrive as `α.hom.app A` and `α.inv.app A` for a natural isomorphism `α`, and recovering the
isomorphism `α.app A` from those is a higher-order unification the elaborator does not solve. -/
theorem glueCompat_eq {C : Type*} [Category C]
    {P aU bU dU eU G H rA xA aV bV dV eV rB xB : C}
    {rcU : P ⟶ aU} {RUf : aU ⟶ rA} {cc : rA ⟶ rB} {kUAh : rA ⟶ xA} {kUAi : xA ⟶ rA}
    {kUF : aU ⟶ bU} {dUf : bU ⟶ xA} {pU : bU ⟶ dU} {qU : dU ⟶ eU} {Df : eU ⟶ xA}
    {rU : dU ⟶ G} {rU' : eU ⟶ H} {m : G ⟶ H} {phiW : P ⟶ G}
    {rcV : P ⟶ aV} {RVg : aV ⟶ rB} {kVBh : rB ⟶ xB} {kVBi : xB ⟶ rB} {kVF : aV ⟶ bV}
    {dVg : bV ⟶ xB} {pV : bV ⟶ dV} {qV : dV ⟶ eV} {Dg : eV ⟶ xB} {rV : dV ⟶ G}
    {rV' : eV ⟶ H} {sV' : H ⟶ eV}
    (hkUA : kUAh ≫ kUAi = 𝟙 rA) (hkVBhi : kVBh ≫ kVBi = 𝟙 rB)
    (hkVBih : kVBi ≫ kVBh = 𝟙 xB)
    (hnatU : RUf ≫ kUAh = kUF ≫ dUf) (hfU : dUf = pU ≫ qU ≫ Df)
    (hkeyU : phiW = rcU ≫ kUF ≫ pU ≫ rU) (hnatrU : qU ≫ rU' = rU ≫ m)
    (hnatV : RVg ≫ kVBh = kVF ≫ dVg) (hfV : dVg = pV ≫ qV ≫ Dg)
    (hkeyV : phiW = rcV ≫ kVF ≫ pV ≫ rV) (hnatrV : qV ≫ rV' = rV ≫ m)
    (hrs : rV' ≫ sV' = 𝟙 eV)
    (hcompat : Df ≫ kUAi ≫ cc ≫ kVBh = (rU' ≫ sV') ≫ Dg) :
    rcU ≫ RUf ≫ cc = rcV ≫ RVg := by
  have h1 : RUf = (kUF ≫ dUf) ≫ kUAi := by
    rw [← hnatU, Category.assoc, hkUA, Category.comp_id]
  have h2 : RVg = (kVF ≫ dVg) ≫ kVBi := by
    rw [← hnatV, Category.assoc, hkVBhi, Category.comp_id]
  have hL : (rcU ≫ RUf ≫ cc) ≫ kVBh = phiW ≫ m ≫ sV' ≫ Dg := by
    rw [h1, hfU, hkeyU]
    simp only [Category.assoc]
    rw [hcompat]
    simp only [Category.assoc]
    rw [← Category.assoc qU rU', hnatrU]
    simp only [Category.assoc]
  have hR : (rcV ≫ RVg) ≫ kVBh = phiW ≫ m ≫ sV' ≫ Dg := by
    rw [h2, hfV, hkeyV]
    simp only [Category.assoc]
    rw [hkVBih, Category.comp_id, ← Category.assoc rV m, ← hnatrV]
    simp only [Category.assoc]
    rw [← Category.assoc rV' sV', hrs, Category.id_comp]
  have : IsSplitMono kVBh := ⟨⟨kVBi, hkVBhi⟩⟩
  exact (cancel_mono kVBh).1 (by simpa only [Category.assoc] using hL.trans hR.symm)

/-! ### The compatibility clause from the coherence of the dictionary -/

/-- Functoriality across a triple composite, as one step.  Private: the name is used, with
different statements, in several other files of the tree. -/
private theorem map_comp₃ {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {a b c d : C}
    (x : a ⟶ b) (y : b ⟶ c) (z : c ⟶ d) :
    F.map (x ≫ y ≫ z) = F.map x ≫ F.map y ≫ F.map z := by
  rw [F.map_comp, F.map_comp]

/-- **The compatibility clause of Situation 0D67 for a glueing of [Stacks, Tag 08DG], from the
coherence of the dictionary.**

`N` is the glued object of `D(𝒪_X)`, `e` identifies the extension by zero of its restriction to
`⊤` with it, `Df` and `Dg` are the identifications of its two derived restrictions, and `f` and
`g` are the identifications in the displayed restriction functors, constrained by `hfU` and
`hfV` — after restriction to the intersection — to be the transports of `Df` and `Dg` along the
dictionary.  `hD` is the compatibility of `Df` and `Dg`, as [Stacks, Tag 08DG] delivers it; `hU`
and `hV` are the coherence of the dictionary, read at the restriction of `N` to `⊤`.

Every object and morphism is a variable, so each naturality square and each functoriality
equation handed to `Stacks.DerivedGlueing.glueCompat_eq` determines its arguments without any of
them being re-elaborated. -/
theorem twoOpenGlueingOver_top_compat (S : LocallyGiven X) (U V : Opens X.carrier)
    {A : OpenDerivedCategory X U} {B : OpenDerivedCategory X V}
    (c : (S.restriction (U ⊓ V) U inf_le_left).obj A ≅
      (S.restriction (U ⊓ V) V inf_le_right).obj B)
    (N : DerivedCategory (SheafOfModules.{u} (underlyingRingSheaf X)))
    (e : (jShriek (⊤ : Opens X.carrier) (underlyingRingSheaf X)).mapDerivedCategory.obj
      ((jStar (⊤ : Opens X.carrier) (underlyingRingSheaf X)).mapDerivedCategory.obj N) ⟶ N)
    (Df : (derivedRestrict (X.ofRestrict U.isOpenEmbedding)).obj N ⟶ A)
    (Dg : (derivedRestrict (X.ofRestrict V.isOpenEmbedding)).obj N ⟶ B)
    (f : (S.restriction U ⊤ le_top).obj
      ((jStar (⊤ : Opens X.carrier) (underlyingRingSheaf X)).mapDerivedCategory.obj N) ⟶ A)
    (g : (S.restriction V ⊤ le_top).obj
      ((jStar (⊤ : Opens X.carrier) (underlyingRingSheaf X)).mapDerivedCategory.obj N) ⟶ B)
    (hfU : (derivedRestrict (restrictIncl (X := X) (inf_le_left : U ⊓ V ≤ U))).map f =
      (derivedRestrict (restrictIncl (X := X) (inf_le_left : U ⊓ V ≤ U))).map
          ((S.restrictionIsoDerivedRestrict ⊤ U le_top).hom.app _) ≫
        (derivedRestrict (restrictIncl (X := X) (inf_le_left : U ⊓ V ≤ U))).map
          ((derivedRestrict (X.ofRestrict U.isOpenEmbedding)).map e) ≫
        (derivedRestrict (restrictIncl (X := X) (inf_le_left : U ⊓ V ≤ U))).map Df)
    (hfV : (derivedRestrict (restrictIncl (X := X) (inf_le_right : U ⊓ V ≤ V))).map g =
      (derivedRestrict (restrictIncl (X := X) (inf_le_right : U ⊓ V ≤ V))).map
          ((S.restrictionIsoDerivedRestrict ⊤ V le_top).hom.app _) ≫
        (derivedRestrict (restrictIncl (X := X) (inf_le_right : U ⊓ V ≤ V))).map
          ((derivedRestrict (X.ofRestrict V.isOpenEmbedding)).map e) ≫
        (derivedRestrict (restrictIncl (X := X) (inf_le_right : U ⊓ V ≤ V))).map Dg)
    (hD : (derivedRestrict (restrictIncl (X := X) (inf_le_left : U ⊓ V ≤ U))).map Df ≫
        (S.restrictionIsoDerivedRestrictIncl (inf_le_left : U ⊓ V ≤ U)).inv.app A ≫ c.hom ≫
          (S.restrictionIsoDerivedRestrictIncl (inf_le_right : U ⊓ V ≤ V)).hom.app B =
      ((restrictInclDerivedIso (X := X) (inf_le_left : U ⊓ V ≤ U)).inv.app N ≫
          (restrictInclDerivedIso (X := X) (inf_le_right : U ⊓ V ≤ V)).hom.app N) ≫
        (derivedRestrict (restrictIncl (X := X) (inf_le_right : U ⊓ V ≤ V))).map Dg)
    (hU : (S.restrictionIsoDerivedRestrict ⊤ (U ⊓ V) le_top).hom.app
        ((jStar (⊤ : Opens X.carrier) (underlyingRingSheaf X)).mapDerivedCategory.obj N) =
      (S.restrictionComp (U ⊓ V) U ⊤ inf_le_left le_top).hom.app _ ≫
        (S.restrictionIsoDerivedRestrictIncl (inf_le_left : U ⊓ V ≤ U)).hom.app
          ((S.restriction U ⊤ le_top).obj _) ≫
        (derivedRestrict (restrictIncl (X := X) (inf_le_left : U ⊓ V ≤ U))).map
          ((S.restrictionIsoDerivedRestrict ⊤ U le_top).hom.app _) ≫
        (restrictInclDerivedIso (X := X) (inf_le_left : U ⊓ V ≤ U)).inv.app
          ((jShriek (⊤ : Opens X.carrier) (underlyingRingSheaf X)).mapDerivedCategory.obj
            ((jStar (⊤ : Opens X.carrier) (underlyingRingSheaf X)).mapDerivedCategory.obj N)))
    (hV : (S.restrictionIsoDerivedRestrict ⊤ (U ⊓ V) le_top).hom.app
        ((jStar (⊤ : Opens X.carrier) (underlyingRingSheaf X)).mapDerivedCategory.obj N) =
      (S.restrictionComp (U ⊓ V) V ⊤ inf_le_right le_top).hom.app _ ≫
        (S.restrictionIsoDerivedRestrictIncl (inf_le_right : U ⊓ V ≤ V)).hom.app
          ((S.restriction V ⊤ le_top).obj _) ≫
        (derivedRestrict (restrictIncl (X := X) (inf_le_right : U ⊓ V ≤ V))).map
          ((S.restrictionIsoDerivedRestrict ⊤ V le_top).hom.app _) ≫
        (restrictInclDerivedIso (X := X) (inf_le_right : U ⊓ V ≤ V)).inv.app
          ((jShriek (⊤ : Opens X.carrier) (underlyingRingSheaf X)).mapDerivedCategory.obj
            ((jStar (⊤ : Opens X.carrier) (underlyingRingSheaf X)).mapDerivedCategory.obj N))) :
    (S.restrictionComp (U ⊓ V) U ⊤ inf_le_left le_top).hom.app
          ((jStar (⊤ : Opens X.carrier) (underlyingRingSheaf X)).mapDerivedCategory.obj N) ≫
        (S.restriction (U ⊓ V) U inf_le_left).map f ≫ c.hom =
      (S.restrictionComp (U ⊓ V) V ⊤ inf_le_right le_top).hom.app
          ((jStar (⊤ : Opens X.carrier) (underlyingRingSheaf X)).mapDerivedCategory.obj N) ≫
        (S.restriction (U ⊓ V) V inf_le_right).map g :=
  glueCompat_eq
    ((S.restrictionIsoDerivedRestrictIncl (inf_le_left : U ⊓ V ≤ U)).hom_inv_id_app A)
    ((S.restrictionIsoDerivedRestrictIncl (inf_le_right : U ⊓ V ≤ V)).hom_inv_id_app B)
    ((S.restrictionIsoDerivedRestrictIncl (inf_le_right : U ⊓ V ≤ V)).inv_hom_id_app B)
    ((S.restrictionIsoDerivedRestrictIncl (inf_le_left : U ⊓ V ≤ U)).hom.naturality f)
    hfU hU ((restrictInclDerivedIso (X := X) (inf_le_left : U ⊓ V ≤ U)).inv.naturality e)
    ((S.restrictionIsoDerivedRestrictIncl (inf_le_right : U ⊓ V ≤ V)).hom.naturality g)
    hfV hV ((restrictInclDerivedIso (X := X) (inf_le_right : U ⊓ V ≤ V)).inv.naturality e)
    ((restrictInclDerivedIso (X := X) (inf_le_right : U ⊓ V ≤ V)).inv_hom_id_app N) hD

/-- **The compatibility clause carried by a glueing datum, with the Cartesian square and the
datum variables.**

`Stacks.Cohomology.GlueingComplexes.Glueing.compatible` is a term of the `Prop`-valued
definition `Stacks.Cohomology.GlueingComplexes.CompatibleOnOverlap`; reading it as the equation
it unfolds to is one delta step, but at the concrete square of
`Stacks.DerivedGlueing.isPullback_restrictIncl` the kernel does not finish rechecking it.  Taken
once here, against a type built from variables, it is free, and the instance that is needed
follows by substitution. -/
theorem glueing_compatible_eq {Y P Q Z : RingedSpace.{u, u}} (jU : P ⟶ Y) (jV : Q ⟶ Y)
    (iU : Z ⟶ P) (iV : Z ⟶ Q) (h : iU ≫ jU = iV ≫ jV) {A : DerivedModules P}
    {B : DerivedModules Q} (c : (derivedRestrict iU).obj A ≅ (derivedRestrict iV).obj B)
    (D : Glueing jU jV iU iV h A B c) :
    (derivedRestrict iU).map D.f.hom ≫ c.hom =
      (overlapIso jU jV iU iV h).hom.app D.F ≫ (derivedRestrict iV).map D.g.hom :=
  D.compatible

/-- **[Stacks, Tag 08DG] at the Cartesian square of two opens of a ringed space.**  This is
`Stacks.Cohomology.GlueingComplexes.exists_glueing` at
`Stacks.DerivedGlueing.isPullback_restrictIncl`, and nothing else; it is taken in its own
declaration so that the repackaging of the glueing datum below does not have to re-check the
application. -/
theorem nonempty_glueing_restrictIncl (U V : Opens X.carrier)
    (A : OpenDerivedCategory X U) (B : OpenDerivedCategory X V)
    (cc : (derivedRestrict (restrictIncl (X := X) (inf_le_left : U ⊓ V ≤ U))).obj A ≅
      (derivedRestrict (restrictIncl (X := X) (inf_le_right : U ⊓ V ≤ V))).obj B) :
    Nonempty (Glueing (X.ofRestrict U.isOpenEmbedding) (X.ofRestrict V.isOpenEmbedding)
      (restrictIncl (X := X) (inf_le_left : U ⊓ V ≤ U))
      (restrictIncl (X := X) (inf_le_right : U ⊓ V ≤ V))
      (isPullback_restrictIncl U V).w A B cc) :=
  exists_glueing (X.ofRestrict U.isOpenEmbedding) (X.ofRestrict V.isOpenEmbedding)
    (restrictIncl (X := X) (inf_le_left : U ⊓ V ≤ U))
    (restrictIncl (X := X) (inf_le_right : U ⊓ V ≤ V)) (isPullback_restrictIncl U V) A B cc

/-- **[Stacks, Tag 08DG] at two opens, with the compatibility clause read through
`Stacks.DerivedGlueing.restrictInclDerivedIso`.**  The glueing datum is given as an isomorphism
`cc` conjugated by two isomorphisms `kU` and `kV`, all three variables, so that the conjugation
is never unfolded. -/
theorem exists_glueing_restrictIncl (U V : Opens X.carrier)
    {A : OpenDerivedCategory X U} {B : OpenDerivedCategory X V}
    {rA rB : OpenDerivedCategory X (U ⊓ V)}
    (kU : rA ≅ (derivedRestrict (restrictIncl (X := X) (inf_le_left : U ⊓ V ≤ U))).obj A)
    (kV : rB ≅ (derivedRestrict (restrictIncl (X := X) (inf_le_right : U ⊓ V ≤ V))).obj B)
    (cc : rA ≅ rB) :
    ∃ (N : DerivedCategory (SheafOfModules.{u} (underlyingRingSheaf X)))
      (Df : (derivedRestrict (X.ofRestrict U.isOpenEmbedding)).obj N ≅ A)
      (Dg : (derivedRestrict (X.ofRestrict V.isOpenEmbedding)).obj N ≅ B),
      (derivedRestrict (restrictIncl (X := X) (inf_le_left : U ⊓ V ≤ U))).map Df.hom ≫
          kU.inv ≫ cc.hom ≫ kV.hom =
        ((restrictInclDerivedIso (X := X) (inf_le_left : U ⊓ V ≤ U)).inv.app N ≫
            (restrictInclDerivedIso (X := X) (inf_le_right : U ⊓ V ≤ V)).hom.app N) ≫
          (derivedRestrict (restrictIncl (X := X) (inf_le_right : U ⊓ V ≤ V))).map Dg.hom := by
  obtain ⟨D⟩ := nonempty_glueing_restrictIncl U V A B (kU.symm ≪≫ cc ≪≫ kV)
  exact ⟨D.F, D.f, D.g,
    (glueing_compatible_eq (X.ofRestrict U.isOpenEmbedding) (X.ofRestrict V.isOpenEmbedding)
        (restrictIncl (X := X) (inf_le_left : U ⊓ V ≤ U))
        (restrictIncl (X := X) (inf_le_right : U ⊓ V ≤ V)) (isPullback_restrictIncl U V).w
        (kU.symm ≪≫ cc ≪≫ kV) D).trans
      (congrArg
        (fun z => z ≫
          (derivedRestrict (restrictIncl (X := X) (inf_le_right : U ⊓ V ≤ V))).map D.g.hom)
        (overlapIso_hom_app_eq U V D.F))⟩

/-- **The compatibility clause of the two-open glueing problem of Situation 0D67 over the ambient
open, from the coherence of the dictionary.**

The coherence asked for, `hU` and `hV`, is this: for `W ≤ U ≤ ⊤` the dictionary over `W` is the
comparison of restriction in two steps, followed by the dictionary over `U`, followed by the
factorisation of [Stacks, Tag 0D5S] of derived restriction to `W` through `U`.  That is the only
input: the glued object, its two identifications and the whole of the rest of the compatibility
come from `Stacks.Cohomology.GlueingComplexes.exists_glueing` with nothing assumed. -/
theorem twoOpenGlueingOver_top_of_coherence (S : LocallyGiven X) (U V : Opens X.carrier)
    (hU : ∀ K : OpenDerivedCategory X ⊤,
      (S.restrictionIsoDerivedRestrict ⊤ (U ⊓ V) le_top).hom.app K =
        (S.restrictionComp (U ⊓ V) U ⊤ inf_le_left le_top).hom.app K ≫
          (S.restrictionIsoDerivedRestrictIncl (inf_le_left : U ⊓ V ≤ U)).hom.app
            ((S.restriction U ⊤ le_top).obj K) ≫
          (derivedRestrict (restrictIncl (X := X) (inf_le_left : U ⊓ V ≤ U))).map
            ((S.restrictionIsoDerivedRestrict ⊤ U le_top).hom.app K) ≫
          (restrictInclDerivedIso (X := X) (inf_le_left : U ⊓ V ≤ U)).inv.app
            ((jShriek (⊤ : Opens X.carrier) (underlyingRingSheaf X)).mapDerivedCategory.obj K))
    (hV : ∀ K : OpenDerivedCategory X ⊤,
      (S.restrictionIsoDerivedRestrict ⊤ (U ⊓ V) le_top).hom.app K =
        (S.restrictionComp (U ⊓ V) V ⊤ inf_le_right le_top).hom.app K ≫
          (S.restrictionIsoDerivedRestrictIncl (inf_le_right : U ⊓ V ≤ V)).hom.app
            ((S.restriction V ⊤ le_top).obj K) ≫
          (derivedRestrict (restrictIncl (X := X) (inf_le_right : U ⊓ V ≤ V))).map
            ((S.restrictionIsoDerivedRestrict ⊤ V le_top).hom.app K) ≫
          (restrictInclDerivedIso (X := X) (inf_le_right : U ⊓ V ≤ V)).inv.app
            ((jShriek (⊤ : Opens X.carrier) (underlyingRingSheaf X)).mapDerivedCategory.obj K)) :
    TwoOpenGlueingOver S U V ⊤ le_top le_top := by
  intro A B c
  obtain ⟨N, Df, Dg, hD⟩ := exists_glueing_restrictIncl U V
    ((S.restrictionIsoDerivedRestrictIncl (inf_le_left : U ⊓ V ≤ U)).app A)
    ((S.restrictionIsoDerivedRestrictIncl (inf_le_right : U ⊓ V ≤ V)).app B) c
  exact ⟨(jStar (⊤ : Opens X.carrier) (underlyingRingSheaf X)).mapDerivedCategory.obj N,
    (S.restrictionIsoDerivedRestrict ⊤ U le_top).app _ ≪≫
      (derivedRestrict (X.ofRestrict U.isOpenEmbedding)).mapIso
        (topJShriekCounitDerivedIso.app N) ≪≫ Df,
    (S.restrictionIsoDerivedRestrict ⊤ V le_top).app _ ≪≫
      (derivedRestrict (X.ofRestrict V.isOpenEmbedding)).mapIso
        (topJShriekCounitDerivedIso.app N) ≪≫ Dg,
    twoOpenGlueingOver_top_compat S U V c N (topJShriekCounitDerivedIso.hom.app N)
      Df.hom Dg.hom _ _ (map_comp₃ _ _ _ _) (map_comp₃ _ _ _ _) hD (hU _) (hV _)⟩

end Stacks.DerivedGlueing

end
