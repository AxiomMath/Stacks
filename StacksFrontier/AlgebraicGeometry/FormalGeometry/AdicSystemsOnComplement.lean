module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationSituation
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Algebra.Category.ModuleCat.Limits

/-!
# Coherent adic systems on the open complement

Fix an algebraization situation `S`: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, giving
`X = Spec(A)`, the closed subscheme `Y = V(I)` and the open complement `U = X \ V(𝔞)`. The
algebraization problem of Stacks chapter 52 starts from a coherent `I`-adic system `(F_n)` on
`U` and asks when it comes from `X`.

This file records the two constructions that pose that question. From a system on `U` one forms
the `A`-module `M = limₙ H⁰(U, F_n)` of compatible global sections, which is the candidate
algebraization; and one says the system *extends to `X`* when it is isomorphic, as an inverse
system, to the restriction of a coherent `I`-adic system on all of `X`. The theorems of the
chapter give conditions under which `M` is finite and the system extends.

## Main definitions

* `Stacks.Algebraization.idealOnOpen` — the ideal sheaf `I 𝒪_U` on `U`.
* `Stacks.Algebraization.scalarMap` — the ring map `A → Γ(U, 𝒪_U)`.
* `Stacks.Algebraization.globalSectionsSystem` — the inverse system `n ↦ H⁰(U, F_n)` of
  `A`-modules.
* `Stacks.Algebraization.limitGlobalSections` — the `A`-module `M = limₙ H⁰(U, F_n)`.
* `Stacks.Algebraization.ExtendsToX` — the predicate that a coherent adic system on `U` is the
  restriction of one on `X`.
* `Stacks.Algebraization.underlyingPrime` — the prime of `A` under a point of `U`.
* `Stacks.Algebraization.pointStalkRingEquiv` — the identification `𝒪_{U,y} ≃+* A_𝔮` of the local
  ring of `U` at `y` with the localization of `A` at the prime under `y`.
* `Stacks.Algebraization.baseToPointStalk` — the ring map `A → 𝒪_{U,y}`.

## Main results

* `Stacks.Algebraization.pointStalkRingEquiv_baseToPointStalk_apply` — the identification
  `𝒪_{U,y} ≃+* A_𝔮` carries `A → 𝒪_{U,y}` to the localization map `A → A_𝔮`.

## Implementation notes

The adic system is indexed by `ℕᵒᵖ`, with term `n` representing the Stacks source's `F_{n+1}`.
Global sections are taken on `U` and then restricted along `scalarMap` from
`Γ(U, 𝒪_U)`-modules to `A`-modules before the limit is formed, so that the limit is an
`A`-module as the source intends; `A → Γ(U, 𝒪_U)` is the map induced by the open immersion
`U ⟶ Spec(A)` through `Scheme.ΓSpecIso`.

The two definitions present the ideal on `U` differently, each in the form its own statement
uses: `idealOnOpen` pushes the ideal `I` of `A` to the top ideal sheaf of `X` and pulls it back
along `U.ι`, while `ExtendsToX` writes it as the pullback of the kernel ideal sheaf of
`Y ⟶ X`. Both name `I 𝒪_U`.

`ExtendsToX` asks for an isomorphism of the underlying `ℕᵒᵖ`-indexed functors, which is the
right notion because coherent adic systems form a *full* subcategory: such an isomorphism
automatically respects every transition map.

## References

* [Stacks Project, Tag 0EHD](https://stacks.math.columbia.edu/tag/0EHD)
* [Stacks Project, Tag 0EIM](https://stacks.math.columbia.edu/tag/0EIM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

/-- The ideal `I 𝒪_U` induced by the ideal `I` of the affine scheme `X`. -/
public abbrev idealOnOpen (S : AlgebraizationSituation.{u}) : S.U.toScheme.IdealSheafData :=
  (Scheme.IdealSheafData.ofIdealTop (S.I.map (Scheme.ΓSpecIso (.of S.A)).inv.hom)).comap S.U.ι

/-- The homomorphism `A → Γ(U, 𝒪_U)` coming from the open immersion into `Spec A`. -/
public abbrev scalarMap (S : AlgebraizationSituation.{u}) : S.A →+* Γ(S.U.toScheme, ⊤) :=
  ((Scheme.ΓSpecIso (.of S.A)).inv ≫ S.U.ι.appTop).hom

/-- The inverse system of sections, viewed as modules over `A`. -/
public abbrev globalSectionsSystem (S : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) : ℕᵒᵖ ⥤ ModuleCat.{u} S.A :=
  F.obj ⋙ SheafOfModules.evaluation S.U.toScheme.ringCatSheaf (op ⊤) ⋙
    ModuleCat.restrictScalars (scalarMap S)

/-- **Stacks Project, Tag 0EHD.** The `A`-module `M = limₙ H⁰(U, Fₙ)` associated to a coherent
adic system on `U`. -/
@[stacks 0EHD]
public abbrev limitGlobalSections (S : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) : ModuleCat.{u} S.A :=
  limit (globalSectionsSystem S F)

/-- **Stacks Project, Tag 0EIM.** A coherent `I`-adic system on `U` extends to `X` when it is
isomorphic, as an inverse system, to the restriction of a coherent `I`-adic system on `X`. -/
@[stacks 0EIM]
public abbrev ExtendsToX (S : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (S.Yι.ker.comap S.U.ι)) : Prop :=
  ∃ G : Stacks.Coherent.CoherentAdicSystems S.Yι.ker,
    Nonempty ((G.obj ⋙ Scheme.Modules.restrictFunctor S.U.ι) ≅ F.obj)

/-! ### The local ring of `U` at a point -/

/-- The prime of `A` under a point of the open complement `U`. -/
public def underlyingPrime (S : AlgebraizationSituation.{u}) (y : S.U.toScheme) :
    PrimeSpectrum S.A :=
  S.U.ι.base y

/-- The local ring of `U` at `y` is the localization of `A` at the prime under `y`: the stalk of
an open subscheme is the stalk of the ambient scheme, and on `Spec A` the stalk at a prime is the
localization there. -/
public def pointStalkRingEquiv (S : AlgebraizationSituation.{u}) (y : S.U.toScheme) :
    S.U.toScheme.presheaf.stalk y ≃+*
      Localization.AtPrime (underlyingPrime S y).asIdeal :=
  ((Scheme.Opens.stalkIso S.U y).trans
    (Spec.stalkIso (.of S.A) (underlyingPrime S y))).commRingCatIsoToRingEquiv

/-- The ring map `A → 𝒪_{U,y}` through the germ at the image of `y` in `X = Spec A`. -/
public def baseToPointStalk (S : AlgebraizationSituation.{u}) (y : S.U.toScheme) :
    S.A →+* S.U.toScheme.presheaf.stalk y :=
  ((S.U.ι.stalkMap y).hom.comp
    ((S.X.presheaf.germ ⊤ (S.U.ι.base y) (Set.mem_univ _)).hom)).comp
    (Scheme.ΓSpecIso (.of S.A)).inv.hom

/-- The identification `𝒪_{U,y} ≃+* A_𝔮` of the local ring of `U` at `y` with the localization of
`A` at the prime `𝔮` under `y` carries the map `A → 𝒪_{U,y}` to the localization map
`A → A_𝔮`, element by element. -/
public theorem pointStalkRingEquiv_baseToPointStalk_apply (S : AlgebraizationSituation.{u})
    (y : S.U.toScheme) (a : S.A) :
    pointStalkRingEquiv S y (baseToPointStalk S y a) =
      algebraMap S.A (Localization.AtPrime (underlyingPrime S y).asIdeal) a := by
  let q := underlyingPrime S y
  have hu := Scheme.Opens.stalkIso_inv S.U y
  have hs' :
      S.X.presheaf.germ ⊤ (S.U.ι.base y) (Set.mem_univ _) ≫
          (Spec.stalkIso (.of S.A) q).hom =
        (Scheme.ΓSpecIso (.of S.A)).hom ≫
          CommRingCat.ofHom (algebraMap S.A (Localization.AtPrime q.asIdeal)) :=
    Spec.germ_stalkMapIso_hom (R := .of S.A) (x := q)
  have hrestrict :
      S.U.ι.stalkMap y ≫
          ((Scheme.Opens.stalkIso S.U y).trans
            (Spec.stalkIso (.of S.A) q)).hom =
        (Spec.stalkIso (.of S.A) q).hom := by
    rw [← hu]
    change (Scheme.Opens.stalkIso S.U y).inv ≫
      (Scheme.Opens.stalkIso S.U y).hom ≫
      (Spec.stalkIso (.of S.A) q).hom = _
    calc
      _ = ((Scheme.Opens.stalkIso S.U y).inv ≫
          (Scheme.Opens.stalkIso S.U y).hom) ≫
          (Spec.stalkIso (.of S.A) q).hom := (Category.assoc _ _ _).symm
      _ = _ := by
        rw [Iso.inv_hom_id]
        change 𝟙 ((AlgebraicGeometry.Spec (CommRingCat.of S.A)).presheaf.stalk q) ≫
          (Spec.stalkIso (.of S.A) q).hom = _
        exact Category.id_comp _
  have hmorph :
      (Scheme.ΓSpecIso (.of S.A)).inv ≫
          S.X.presheaf.germ ⊤ (S.U.ι.base y) (Set.mem_univ _) ≫
          S.U.ι.stalkMap y ≫
          ((Scheme.Opens.stalkIso S.U y).trans
            (Spec.stalkIso (.of S.A) q)).hom =
        CommRingCat.ofHom (algebraMap S.A (Localization.AtPrime q.asIdeal)) := by
    simp only [hrestrict]
    rw [hs']
    simp
  exact congrArg (fun t : (.of S.A : CommRingCat) ⟶
      .of (Localization.AtPrime q.asIdeal) => t.hom a) hmorph

end Stacks.Algebraization

end
