module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurj
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningEtaleLocalization

/-!
# Universal first-order thickenings and étale localization: the whole of Stacks 060D

Let `Z ⊂ Z'` be the universal first-order thickening of a formally unramified `Z ⟶ X`, and let
`V ⟶ U` lie over `Z ⟶ X` with étale vertical arrows `V ⟶ Z` and `U ⟶ X`.  Stacks 060D says
three things: `V ⟶ U` is formally unramified; the universal first-order thickening of `V` over
`U` is étale over `Z'`; and the conormal sheaf of `Z` over `X` restricts to that of `V` over `U`.
The source draws these in continuous prose and numbers none of them.

`StacksFrontier/AlgebraicGeometry/Spaces/UniversalThickeningEtaleLocalization.lean` proves the
thickening and conormal assertions for an étale extension `V'` of `V` across `Z ⊂ Z'` which is
given.  This file produces that extension from the étale `V ⟶ Z` alone, and assembles the three
assertions into one statement under the source's hypotheses.

## Main results

* `AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.exists_etaleLocalization`:
  **Stacks 060D, the thickening assertion, with the étale extension produced** from the étale
  `V ⟶ Z` and the commutative square alone.
* `AlgebraicGeometry.Space.etaleLocalization_commutes_universalFirstOrderThickening`:
  **Stacks 060D**, the whole lemma — all three of its assertions under the source's
  hypotheses, with nothing the lemma asserts assumed.

## Implementation notes

**The étale extension is produced.**  The source states the thickening assertion for *the*
universal first-order thickening `V'` of `V` over `U`, whose existence is Stacks 0606, and
identifies it with the étale extension of `V` across `Z ⊂ Z'` furnished by the topological
invariance of the spaces-étale site, Stacks 05ZH.  Stacks 0606 is
`AlgebraicGeometry.Space.nonempty_universalFirstOrderThickening` in
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/UniversalExistence.lean`.  Stacks 05ZH is
available in the case needed here, the inclusion of a first-order thickening:
`AlgebraicGeometry.Space.essSurj_spacesBaseChange_of_isFirstOrderThickening` in
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/SpacesEtaleEssSurj.lean` is its essential
surjectivity, and
`AlgebraicGeometry.Space.isEquivalence_spacesBaseChange_of_isFirstOrderThickening` the
equivalence.

So there are two statements of the thickening assertion.
`AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.exists_etaleLocalization` produces the
extension: from the étale `V ⟶ Z` and the square over `Z ⟶ X` it builds an étale
`g : V' ⟶ Z'`, a morphism `r : V' ⟶ U` over `X`, and a closed subspace of `V'` cartesian over
`Z ⊂ Z'` and identified with `V` over `Z`, which is a universal first-order thickening of `V`
over `U`.  `AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.etaleLocalization` keeps
`g` and the cartesian square as hypotheses, so that it applies to *any* such extension.  Read
together with the uniqueness clause of Stacks 0602 — a universal first-order thickening is
unique up to a unique isomorphism, which is
`AlgebraicGeometry.Space.eq_universalThickeningMap` — the two say the sentence of the source.

**The first assertion.**  That `V ⟶ U` is formally unramified, which is Stacks 04G8, is
independent of the other two, which carry the universal property of Stacks 0602 as a hypothesis
rather than deriving it.  It is
`AlgebraicGeometry.Space.formallyUnramified_of_etaleLocalization` of
`StacksFrontier/AlgebraicGeometry/Spaces/UniversalFirstOrderThickeningDescent.lean`, which the
whole-tag statement invokes for it.

**The bare registration sits on the whole-tag statement.**  Each assertion keeps a registration
with a part string on the declaration that states it; the one declaration whose statement is the
entire lemma is `AlgebraicGeometry.Space.etaleLocalization_commutes_universalFirstOrderThickening`,
and it carries the bare `@[stacks 060D]`.

## References

* [Stacks Project, Tag 060D](https://stacks.math.columbia.edu/tag/060D)
* [Stacks Project, Tag 0602](https://stacks.math.columbia.edu/tag/0602)
* [Stacks Project, Tag 0606](https://stacks.math.columbia.edu/tag/0606)
* [Stacks Project, Tag 0611](https://stacks.math.columbia.edu/tag/0611)
* [Stacks Project, Tag 04G8](https://stacks.math.columbia.edu/tag/04G8)
* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)


/-! ### The thickening assertion with the étale extension produced from `V ⟶ Z` -/

/-- **Stacks 060D, the thickening assertion, with the étale extension produced.**  Let
`Z ⊂ Z'` be a universal
first-order thickening of `Z` over an algebraic space `X`, with structure morphism `p : Z' ⟶ X`,
let `φ : U ⟶ X` be étale, and let

```
  V ---→ U
  |      |
  ↓      ↓
  Z ---→ X
```

commute with `v : V ⟶ Z` étale.  Then there are an algebraic space `V'`, an étale
`g : V' ⟶ Z'`, a morphism `r : V' ⟶ U` with `r ≫ φ = g ≫ p`, a subspace `V ⊂ V'` sitting in a
cartesian square over the inclusion of `Z`, and an isomorphism of that subspace with the given
`V` compatible with the maps to `Z` and to `U`, such that `V ⊂ V'` is a universal first-order
thickening of `V` over `U`.

Nothing about `V'` is assumed.  It is the essential-surjectivity half of the topological
invariance of the spaces-étale site at the first-order thickening `Z ⊂ Z'`, Stacks 05ZH in the
form `AlgebraicGeometry.Space.essSurj_spacesBaseChange_of_isFirstOrderThickening`, applied to
the object `v` of the spaces-étale site of `Z`: it returns an object of the spaces-étale site of
`Z'` whose base change along the inclusion of `Z` is `v`.  Its subspace is the inverse image
`g⁻¹(Z)`, which is cartesian over `Z ⊂ Z'` by Stacks 083Q,
`CategoryTheory.Subfunctor.isPullback_preimage`, and is a first-order thickening because `g` is
étale, by Stacks 09ZX in the étale case
(`AlgebraicGeometry.Space.isNthOrderThickening_preimage_of_isEtale`).  The identification of
`g⁻¹(Z)` with the given `V` is the comparison of two cartesian squares on one cospan, composed
with the isomorphism of objects of the site.  The remaining datum, `r`, is the extension of
`V ⟶ U` across `g⁻¹(Z) ⊂ V'`: that is the unique lift of Stacks 0611 for the formally étale
`φ`, which is where étaleness of `φ` — rather than of `U ⟶ X` only in the source's diagram — is
used.  That `V ⊂ V'` is then a universal first-order thickening of `V` over `U` is
`AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.etaleLocalization`.

The conormal assertion applies verbatim to the data produced here: the cartesian square returned
below is the hypothesis of `AlgebraicGeometry.Space.conormalModuleEtaleLocalizationIso`.

The attribute carries a part string rather than being bare for the reason recorded in the
implementation notes: the first assertion of the source, formal unramifiedness of `V ⟶ U`, is
independent of this statement — it is
`AlgebraicGeometry.Space.formallyUnramified_of_etaleLocalization`, which takes formal
unramifiedness of `Z ⟶ X` as a hypothesis, whereas here the universal property of Stacks 0602
is carried instead.  The bare registration sits on
`AlgebraicGeometry.Space.etaleLocalization_commutes_universalFirstOrderThickening` at the end of
this file, which states all three assertions together. -/
@[stacks 060D "the thickening assertion, étale extension produced from `V ⟶ Z`, not assumed"]
theorem IsUniversalFirstOrderThickening.exists_etaleLocalization
    {X U Z' : AlgebraicSpaces B S hS} (Z : Subfunctor Z'.obj) (p : Z' ⟶ X)
    (hZ : IsUniversalFirstOrderThickening B S hS Z p)
    (φ : U ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (V₀ : AlgebraicSpaces B S hS) (v : V₀.obj ⟶ Z.toFunctor) (hv : IsEtale B S hS v)
    (u : V₀ ⟶ U) (hcomm : u.hom ≫ φ.hom = v ≫ Z.ι ≫ p.hom) :
    ∃ (V' : AlgebraicSpaces B S hS) (g : V' ⟶ Z') (r : V' ⟶ U) (V : Subfunctor V'.obj)
      (c : V.toFunctor ⟶ Z.toFunctor) (e : V.toFunctor ≅ V₀.obj),
      IsEtale B S hS g.hom ∧ IsPullback c V.ι Z.ι g.hom ∧ r ≫ φ = g ≫ p ∧
        e.hom ≫ v = c ∧ V.ι ≫ r.hom = e.hom ≫ u.hom ∧
        IsUniversalFirstOrderThickening B S hS V r := by
  classical
  -- `Z` is an algebraic space, and its inclusion is the inclusion of a first-order thickening.
  let Zsp : AlgebraicSpaces B S hS := ⟨Z.toFunctor, hZ.firstOrder.1.1.1⟩
  let jZ : Zsp ⟶ Z' := ObjectProperty.homMk Z.ι
  have : Mono jZ.hom := (inferInstance : Mono Z.ι)
  have hthick : IsFirstOrderThickening B S hS Z' (Subfunctor.range jZ.hom) := by
    rw [show Subfunctor.range jZ.hom = Z from Subfunctor.range_ι Z]
    exact hZ.firstOrder
  -- The given étale `V ⟶ Z`, as an object of the spaces-étale site of `Z`.
  let C : SpacesEtale B S hS Zsp := ⟨Over.mk (ObjectProperty.homMk v : V₀ ⟶ Zsp), hv⟩
  -- Stacks 05ZH at the first-order thickening `Z ⊂ Z'` extends it across the thickening.
  have := essSurj_spacesBaseChange_of_isFirstOrderThickening B S hS jZ hthick
  obtain ⟨D, ⟨iso⟩⟩ := Functor.EssSurj.mem_essImage (spacesBaseChange B S hS jZ).functor C
  have hg : IsEtale B S hS D.1.hom.hom := D.2
  let FD := (spacesBaseChange B S hS jZ).functor.obj D
  -- The base-change square of the extension along the inclusion of `Z`, read in presheaves.
  have hDpb : IsPullback ((spacesBaseChange B S hS jZ).projection.app D).hom FD.1.hom.hom
      D.1.hom.hom Z.ι :=
    AlgebraicSpaces.isPullback_hom B S hS ((spacesBaseChange B S hS jZ).isPullback D)
  -- The inverse image of `Z` along the extension is cartesian over the inclusion of `Z` too.
  have hpre := Subfunctor.isPullback_preimage D.1.hom.hom Z
  let hk := hDpb.isoIsPullback _ _ hpre.flip
  have hksnd : hk.hom ≫ Z.fromPreimage D.1.hom.hom = FD.1.hom.hom :=
    hDpb.isoIsPullback_hom_snd _ _ hpre.flip
  -- The isomorphism of objects of the site, read in presheaves.
  let I := (SpacesEtale.toSpaces B S hS Zsp).mapIso iso
  let eP : FD.1.left.obj ≅ V₀.obj :=
    { hom := I.hom.hom, inv := I.inv.hom
      hom_inv_id := congrArg (fun k ↦ k.hom) I.hom_inv_id
      inv_hom_id := congrArg (fun k ↦ k.hom) I.inv_hom_id }
  have hov : eP.hom ≫ v = FD.1.hom.hom :=
    congrArg (fun k : FD.1.left ⟶ Zsp ↦ k.hom) (Over.w iso.hom.hom)
  -- Composing the two gives the identification of `g⁻¹(Z)` with the given `V` over `Z`.
  let e : (Z.preimage D.1.hom.hom).toFunctor ≅ V₀.obj := hk.symm ≪≫ eP
  have hev : e.hom ≫ v = Z.fromPreimage D.1.hom.hom := by
    show (hk.inv ≫ eP.hom) ≫ v = Z.fromPreimage D.1.hom.hom
    rw [Category.assoc, hov, ← hksnd, ← Category.assoc, hk.inv_hom_id, Category.id_comp]
  -- `g⁻¹(Z) ⊂ V'` is a first-order thickening, the extension being étale.
  have hVfo : IsFirstOrderThickening B S hS D.1.left (Z.preimage D.1.hom.hom) :=
    isNthOrderThickening_preimage_of_isEtale B S hS Z D.1.hom hg hZ.firstOrder
  have hφFE : FormallyEtale φ.hom :=
    ((isEtale_iff_isLocallyOfFinitePresentation_and_formallyEtale B S hS
      U.property X.property φ.hom).mp hφ).2
  have hsolid : (e.hom ≫ u.hom) ≫ φ.hom =
      (Z.preimage D.1.hom.hom).ι ≫ D.1.hom.hom ≫ p.hom := by
    rw [Category.assoc, hcomm, reassoc_of% hev, reassoc_of% Subfunctor.fromPreimage_ι]
  -- Stacks 0611 for the formally étale `φ` extends `V ⟶ U` to `V' ⟶ U`.
  obtain ⟨rho, hrho, -⟩ := FormallyEtale.existsUnique_lift_of_firstOrderThickening B S hS φ hφFE
    (Z.preimage D.1.hom.hom) hVfo (e.hom ≫ u.hom) (D.1.hom.hom ≫ p.hom) hsolid
  have hr : ObjectProperty.homMk rho ≫ φ = D.1.hom ≫ p := ObjectProperty.hom_ext _ hrho.2
  exact ⟨D.1.left, D.1.hom, ObjectProperty.homMk rho, Z.preimage D.1.hom.hom,
    Z.fromPreimage D.1.hom.hom, e, hg, hpre, hr, hev, hrho.1,
    IsUniversalFirstOrderThickening.etaleLocalization B S hS Z p hZ φ hφ D.1.hom hg
      (ObjectProperty.homMk rho) hr (Z.preimage D.1.hom.hom) (Z.fromPreimage D.1.hom.hom) hpre⟩

/-! ### The whole of Stacks 060D -/

/-- **Stacks 060D.**  Taking the universal first-order thickenings commutes with étale
localization.  Let `h : Z ⟶ X` be a formally unramified morphism of algebraic spaces over `S`,
presented as a closed subspace `Z` of an algebraic space `Z'` with structure morphism
`p : Z' ⟶ X`, so that `h = Z.ι ≫ p.hom`, and let `Z ⊂ Z'` be the universal first-order
thickening of `Z` over `X`.  Let

```
  V ---→ U
  |      |
  ↓      ↓
  Z ---→ X
```

commute with the vertical arrows `v : V ⟶ Z` and `φ : U ⟶ X` étale.  Then

* `f : V ⟶ U` is formally unramified;
* the universal first-order thickening of `V` over `U` is étale over `Z'`: there is one, and
  *every* one admits an étale morphism to `Z'` restricting on `V` to `V ⟶ Z ⊂ Z'` and lying
  over `X`;
* `𝒞_{Z/X}|_V = 𝒞_{V/U}`: the *canonical* comparison map from the restriction along `V ⟶ Z` of
  the conormal module of `Z` in `Z'` to the conormal module of `V` in that thickening — the
  morphism underlying `AlgebraicGeometry.Space.conormalModuleEtaleLocalizationIso`, which is
  the étale base change of Stacks 04CO transported along the cartesian square — is an
  isomorphism.

The source draws these three assertions in continuous prose and numbers none of them.

The first is `AlgebraicGeometry.Space.formallyUnramified_of_etaleLocalization`.  The second is
`AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.exists_etaleLocalization`, which
produces the thickening `V ⊂ V'` as the étale extension of `V` across `Z ⊂ Z'`, together with
`AlgebraicGeometry.Space.exists_isEtale_of_isUniversalFirstOrderThickening`, which carries the
étaleness over `Z'` to any other universal first-order thickening of `V` over `U` — the source
speaks of *the* thickening, which is determined up to unique isomorphism by Stacks 0602.  The
third is `AlgebraicGeometry.Space.conormalModuleEtaleLocalizationIso`.

The étaleness of `g` and the cartesian square are existential *binders* rather than conjuncts
because the canonical comparison map is built from them: the third assertion then names that
map, instead of asserting that the two conormal modules are isomorphic by some unnamed
isomorphism.  The source writes an equality, `𝒞_{Z/X}|_V = 𝒞_{V/U}`, which is the canonical
identification and not a bare existence claim.

The smaller space of a thickening is presented as a subfunctor of its ambient space, so the
copy of `V` inside the thickening is never literally the given `V₀`; the isomorphism `e`, and
the identification `eW` in the second assertion, record the comparison, and the equations that
accompany them say that it is one of spaces over `Z` and over `U`. -/
@[stacks 060D]
theorem etaleLocalization_commutes_universalFirstOrderThickening
    {X U Z' : AlgebraicSpaces B S hS} (Z : Subfunctor Z'.obj) (p : Z' ⟶ X)
    (hZ : IsUniversalFirstOrderThickening B S hS Z p)
    (hh : FormallyUnramified (Z.ι ≫ p.hom))
    (φ : U ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (V₀ : AlgebraicSpaces B S hS) (f : V₀ ⟶ U) (v : V₀.obj ⟶ Z.toFunctor)
    (hv : IsEtale B S hS v) (hcomm : f.hom ≫ φ.hom = v ≫ Z.ι ≫ p.hom) :
    FormallyUnramified f.hom ∧
      (∀ (W' : AlgebraicSpaces B S hS) (W : Subfunctor W'.obj) (q : W' ⟶ U)
          (eW : W.toFunctor ≅ V₀.obj), IsUniversalFirstOrderThickening B S hS W q →
          eW.hom ≫ f.hom = W.ι ≫ q.hom →
          ∃ m : W' ⟶ Z', IsEtale B S hS m.hom ∧
            W.ι ≫ m.hom = eW.hom ≫ v ≫ Z.ι ∧ m ≫ p = q ≫ φ) ∧
      ∃ (V' : AlgebraicSpaces B S hS) (g : V' ⟶ Z') (r : V' ⟶ U) (V : Subfunctor V'.obj)
        (c : V.toFunctor ⟶ Z.toFunctor) (e : V.toFunctor ≅ V₀.obj)
        (hV : IsUniversalFirstOrderThickening B S hS V r) (hg : IsEtale B S hS g.hom)
        (hsq : IsPullback c V.ι Z.ι g.hom),
        r ≫ φ = g ≫ p ∧ e.hom ≫ v = c ∧ V.ι ≫ r.hom = e.hom ≫ f.hom ∧
          IsIso (conormalModuleEtaleLocalizationIso B S hS ⟨Z, hZ.firstOrder.1.1⟩ g hg V
            hV.firstOrder.1.1 c hsq).hom := by
  -- The first assertion: formal unramifiedness descends to the localization.
  have hfu : FormallyUnramified f.hom :=
    formallyUnramified_of_etaleLocalization B S hS f
      (ObjectProperty.homMk v : V₀ ⟶ ⟨Z.toFunctor, hZ.firstOrder.1.1.1⟩)
      (ObjectProperty.homMk (Z.ι ≫ p.hom)) φ (ObjectProperty.hom_ext _ hcomm) hh hv hφ
  -- The étale extension of `V` across `Z ⊂ Z'`, which is the universal first-order thickening
  -- of `V` over `U`.
  obtain ⟨V', g, r, V, c, e, hg, hsqV, hrφ, hev, hVr, hVuniv⟩ :=
    IsUniversalFirstOrderThickening.exists_etaleLocalization B S hS Z p hZ φ hφ V₀ v hv f hcomm
  refine ⟨hfu, ?_, V', g, r, V, c, e, hVuniv, hg, hsqV, hrφ, hev, hVr, inferInstance⟩
  -- The second assertion, for an arbitrary universal first-order thickening of `V` over `U`:
  -- compare it with the étale extension and transport `g` along the comparison.
  intro W' W q eW hW hWq
  have hc : e.inv ≫ c = v := by rw [← hev, Iso.inv_hom_id_assoc]
  have he : (eW ≪≫ e.symm).hom ≫ V.ι ≫ r.hom = W.ι ≫ q.hom := by
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, hVr, Iso.inv_hom_id_assoc, hWq]
  obtain ⟨m, hmE, hmres, hmover⟩ :=
    exists_isEtale_of_isUniversalFirstOrderThickening B S hS Z p hZ φ hφ g hg r hrφ V c hsqV
      W q hW (eW ≪≫ e.symm) he
  refine ⟨m, hmE, ?_, hmover⟩
  rw [hmres]
  show (eW.hom ≫ e.inv) ≫ V.ι ≫ g.hom = eW.hom ≫ v ≫ Z.ι
  simp only [Category.assoc]
  rw [← hsqV.w, ← hc]
  simp only [Category.assoc]

end AlgebraicGeometry.Space

end
