module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CohomologicalGysinHodgeConormal
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinCohomologyDeRham
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinDeRhamConormalRank

/-!
# Stacks 0G8B at the glued Gysin map of Stacks 0G86

Let `π : X ⟶ S` be a morphism of schemes and let `i : Z ⟶ X` be as in [Stacks, Tag 0G86]: a
closed immersion of finite presentation whose conormal sheaf is locally free of rank `c`, an
arbitrary natural number — [Stacks, Tag 0G8A] says `c ≥ 0` explicitly.
[Stacks, Tag 0G8A] attaches to the glued Gysin map `γ^p` of [Stacks, Tag 0G86] the maps on
cohomology

`γ^{p, q} : H^q(X, i_*Ω^p_{Z/S}) ⟶ H^{q + c}(X, Ω^{p + c}_{X/S})`,

and [Stacks, Tag 0G8B] says that these are compatible with the de Rham differentials on
`Ω^•_{X/S}` and `Ω^•_{Z/S}`.

This file carries that square across from the sheaf level to cohomology.  The
sheaf-level input is [Stacks, Tag 0G87], `Stacks.Gysin.gysinHom_comm_deRham_of_conormalRank`,
which states the square on the sections over every open of `X`; the cohomological passage is
`Stacks.DeRham.GysinCohomologyDeRham.gysinCohomologyMap_comm`, which is stated for an arbitrary
closed subset and an arbitrary morphism of underlying abelian sheaves and so applies at
`Set.range i.base` with no change.

## Main results

* `gysinTargetDeRhamHom_comm_conormalGysinTargetIso`: **the identification
  `Stacks.DeRham.CohomologicalGysin.conormalGysinTargetIso` of the two spellings of
  `i_*ℋ ᶜ_Z(Ω^{p+c}_{X/S})` carries the action of `i_*ℋ ᶜ_Z` on the de Rham differential in one
  spelling to the action in the other.**  Both actions are conjugations of the same morphism of
  the abelian local cohomology functor, by two isomorphisms differing exactly by that
  identification, so the square is formal.
* `conormalGysinHom_comm_deRham`: **[Stacks, Tag 0G87] as an equality of morphisms of abelian
  sheaves** rather than on sections, which is the shape the cohomological passage consumes.
* `conormalGysinCohomologyMap_comm_deRham`: the square on cohomology at the glued `γ^p`, with the
  vanishing of [Stacks, Tag 0G8A] still a hypothesis.

## Implementation notes

**Why the target has two spellings.**  The glued Gysin map of [Stacks, Tag 0G86] lands in
`Stacks.Gysin.gysinTarget`, which takes the degree-`c` cohomology sheaf of `i_*R𝓗_Z(ℱ[0])` on the
ambient scheme, while the cohomological construction consumes the spelling in which the cohomology
sheaf is taken on the closed subset and pushed forward afterwards.  They agree by
`Stacks.Perfect.GysinLocalCohomology.supportCohomologySheafFunctorIso`, which is what
`Stacks.DeRham.CohomologicalGysin.conormalGysinTargetIso` is; the content of this file's first
lemma is that the de Rham differential's action is carried along it.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ConormalEquations
open Stacks.Cohomology.SupportedComplexes
open Stacks.Perfect.AbelianFraction (abelianSheaf)
open Stacks.Perfect.GysinAbelianSquare (abelianLocalCohomologyPushforward
  pushforwardLocalCohomologyAbelianMap pushforwardLocalCohomologyForgetIso
  supportCohomologySheafAbelianMap supportCohomologySheafForgetIso)
open Stacks.Perfect.GysinLocalCohomology (supportCohomologySheafFunctorIso)

universe u

namespace Stacks.DeRham.GysinCohomologyDeRhamConormal

open AlgebraicGeometry.Scheme.Hom
open Stacks.DeRham.CohomologicalGysin
open Stacks.DeRham.GysinCohomologyDeRham
open Stacks.Gysin
open scoped AlgebraicGeometry

variable {Z X S : Scheme.{u}}

/-! ### Two formal cancellations

Both are pure category theory, stated separately so that each chase below runs inside a single
reading of the category of `𝒪_X`-modules.  `AlgebraicGeometry.Scheme.Modules` and
`Stacks.DeRham.CohomologicalGysin.RModules` of the underlying ringed space are the same type by
unfolding but carry two syntactically different `CategoryTheory.Category` instances, so a `rw`
whose pattern mentions `≫` sees only one of them; passing every arrow explicitly to a lemma of
this shape leaves the single definitional check to `exact`. -/

/-- **Conjugating by a composite of two natural isomorphisms is conjugating by the second, after
the first.**  Both sides of the square of `supportCohomologySheafAbelianMap_comm_functorIso` are
conjugations of one morphism `m`, by `A ≪≫ B` and by `B`; the outer copies of `A` cancel.

Stated at this generality so that the square is ONE definitional check at the call site.  Spelling
it instead as a chain of rewrites through the components exhausted the heartbeat budget at `whnf`,
and the budget may not be raised. -/
private lemma conj_trans_square {C D : Type*} [Category* C] [Category* D]
    {P Q R : C ⥤ D} (A : P ≅ Q) (B : Q ≅ R) {F G : C} (m : R.obj F ⟶ R.obj G) :
    ((A ≪≫ B).hom.app F ≫ m ≫ (A ≪≫ B).inv.app G) ≫ A.hom.app G =
      A.hom.app F ≫ B.hom.app F ≫ m ≫ B.inv.app G := by
  simp only [Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id]

/-- **Two squares pasted along a shared vertical arrow, through a functor.**  The upper square is
the sheaf-level square of [Stacks, Tag 0G87] and the lower one the transport of its right-hand
vertical arrow across the identification of the two spellings of the target. -/
private lemma paste_square {C D : Type*} [Category* C] [Category* D] (Φ : C ⥤ D)
    {A A' Tg Tg' L L' : C} (g : A ⟶ Tg) (g' : A' ⟶ Tg') (θ : Tg ⟶ L) (θ' : Tg' ⟶ L')
    (dT : Φ.obj Tg ⟶ Φ.obj Tg') (ψA : Φ.obj A ⟶ Φ.obj A') (ψT : Φ.obj L ⟶ Φ.obj L')
    (h0 : Φ.map g ≫ dT = ψA ≫ Φ.map g')
    (h1 : dT ≫ Φ.map θ' = Φ.map θ ≫ ψT) :
    Φ.map (g ≫ θ) ≫ ψT = ψA ≫ Φ.map (g' ≫ θ') := by
  rw [Φ.map_comp, Φ.map_comp, Category.assoc, ← h1, ← Category.assoc, h0, Category.assoc]

/-! ### The two spellings of the target, against the de Rham differential -/

/-- The inverse of `Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafForgetIso`, on a
component, splits as the inverse of the comparison of the two places at which the degree-`c`
cohomology sheaf is taken, after the inverse of the identification of the two spellings of the
target.  This is the counterpart of
`Stacks.Perfect.SupportedEndoForgetDegreewise.supportCohomologySheafForgetIso_hom_app_split` and,
like it, holds by definition: the isomorphism is a `CategoryTheory.Iso.trans`. -/
theorem supportCohomologySheafForgetIso_inv_app_split {T : Set X} (hT : IsClosed T) (c : ℕ)
    (H : X.Modules) :
    (supportCohomologySheafForgetIso hT c).inv.app H =
      (pushforwardLocalCohomologyForgetIso hT c).inv.app H ≫
        (abelianSheaf X).map ((supportCohomologySheafFunctorIso hT (c : ℤ)).inv.app H) := rfl

/-- **The action of `i_*ℋ ᶜ_Z` on a morphism of underlying abelian sheaves is carried across the
identification of the two spellings of the target.**  For an arbitrary — in particular not
`𝒪_X`-linear — morphism `ψ`, the square formed by
`Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafAbelianMap`, by
`Stacks.Perfect.GysinAbelianSquare.pushforwardLocalCohomologyAbelianMap` and by the forgetful
image of `Stacks.Perfect.GysinLocalCohomology.supportCohomologySheafFunctorIso` commutes.

Both actions are conjugations of one and the same morphism
`(abelianLocalCohomologyPushforward …).map ψ` of the abelian local cohomology functor: the first
by `supportCohomologySheafForgetIso`, the second by `pushforwardLocalCohomologyForgetIso`, and the
first of those is by definition the second preceded by the forgetful image of
`supportCohomologySheafFunctorIso`.  So the two outer copies of that comparison cancel against the
square's horizontal arrows and nothing of substance is used. -/
theorem supportCohomologySheafAbelianMap_comm_functorIso {T : Set X} (hT : IsClosed T) (c : ℕ)
    {F G : X.Modules} (ψ : (abelianSheaf X).obj F ⟶ (abelianSheaf X).obj G) :
    supportCohomologySheafAbelianMap hT c ψ ≫
        (abelianSheaf X).map ((supportCohomologySheafFunctorIso hT (c : ℤ)).hom.app G) =
      (abelianSheaf X).map ((supportCohomologySheafFunctorIso hT (c : ℤ)).hom.app F) ≫
        pushforwardLocalCohomologyAbelianMap hT c ψ :=
  conj_trans_square
    (Functor.isoWhiskerRight (supportCohomologySheafFunctorIso hT (c : ℤ)) (abelianSheaf X))
    (pushforwardLocalCohomologyForgetIso hT c)
    ((abelianLocalCohomologyPushforward X.toRingedSpace T hT c).map ψ)

/-- **The identification of the two spellings of the Gysin map's target carries the right-hand
vertical arrow of the square of [Stacks, Tag 0G87] to the one the cohomological construction
uses.**  The left-hand side is `Stacks.Gysin.gysinTargetDeRhamHom`, the action of `i_*ℋ ᶜ_Z` on
the relative de Rham differential of `X/S` at the target `Stacks.Gysin.gysinTarget` of the glued
Gysin map; the right-hand side is the same action at the spelling
`Stacks.DeRham.GysinCohomologyDeRham.supportedLocalCohomology`.

This is `supportCohomologySheafAbelianMap_comm_functorIso` at the differential
`Stacks.Gysin.ambientDeRhamShiftAbHom`, the de Rham differential with the degree identification
`p + c + 1 = p + 1 + c` absorbed. -/
theorem gysinTargetDeRhamHom_comm_conormalGysinTargetIso (i : Z ⟶ X) [IsClosedImmersion i]
    (π : X ⟶ S) (c p : ℕ) :
    gysinTargetDeRhamHom i π c p ≫
        (abelianSheaf X).map (conormalGysinTargetIso i π c (p + 1)).hom =
      (abelianSheaf X).map (conormalGysinTargetIso i π c p).hom ≫
        pushforwardLocalCohomologyAbelianMap (isClosed_range_base i) c
          (ambientDeRhamShiftAbHom π c p) :=
  supportCohomologySheafAbelianMap_comm_functorIso (isClosed_range_base i) c
    (ambientDeRhamShiftAbHom π c p)

/-! ### Stacks 0G87 as an equality of morphisms -/

/-- **[Stacks, Tag 0G87] as an equality of morphisms of abelian sheaves.**  The tag is stated on
the sections over every open of `X` — the two vertical arrows being only additive, the de Rham
differential being `𝒪_X`-linear for no `X` — and this is the same square read as an equality of
morphisms, which is the shape `gysinCohomologyMap_comm` consumes.

The passage is `Stacks.Gysin.abSectionsHom_ext`: the category of abelian sheaves is a full
subcategory of the presheaves, so a morphism is determined by its action on sections.  The two
vertical arrows are recognised on sections by `Stacks.Gysin.abSectionsHom_comp` and
`Stacks.Gysin.abSectionsHom_abelianSheaf_map`, and the left-hand one is
`Stacks.Gysin.pushforwardDeRham` by definition. -/
theorem conormalGysinHom_comm_deRham (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i] (π : X ⟶ S) {c : ℕ} (p : ℕ)
    (hE : ConormalRank i c) :
    (abelianSheaf X).map (conormalGysinHom i π p hE) ≫ gysinTargetDeRhamHom i π c p =
      pushforwardDeRhamDifferentialAbHom i π p ≫
        (abelianSheaf X).map (conormalGysinHom i π (p + 1) hE) := by
  refine abSectionsHom_ext fun V x => ?_
  rw [abSectionsHom_comp, abSectionsHom_comp, abSectionsHom_abelianSheaf_map,
    abSectionsHom_abelianSheaf_map]
  exact gysinHom_comm_deRham_of_conormalRank i π p hE _ _
    (conormalGysinHom_app i π p hE) (conormalGysinHom_app i π (p + 1) hE) V x

/-! ### The square on cohomology -/

/-- **The square of [Stacks, Tag 0G8B] at the glued Gysin map of [Stacks, Tag 0G86], with the
vanishing of [Stacks, Tag 0G8A] still a hypothesis.**  The cohomological Gysin maps attached to
the glued `γ^p` and `γ^{p+1}` commute with the arrows the de Rham differentials induce on the
cohomology groups.

The sheaf-level input is [Stacks, Tag 0G87], read as an equality of morphisms by
`conormalGysinHom_comm_deRham` and transported to the spelling of the target that the
cohomological construction uses by `gysinTargetDeRhamHom_comm_conormalGysinTargetIso`; the
compatibility of the Gysin edge morphism with forgetting the module structure is
`Stacks.DeRham.GysinCohomologyDeRham.edgeCommutesWithAbelian` at the closed subset
`Set.range i.base`.

The right-hand vertical arrow is the action of the relative de Rham differential of `X/S` with the
canonical identification of the two equal degrees `p + c + 1` and `p + 1 + c` absorbed, which is
`Stacks.Gysin.ambientDeRhamShiftAbHom` — the same arrow [Stacks, Tag 0G87] uses, so that no degree
transport is left over. -/
theorem conormalGysinCohomologyMap_comm_deRham (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i] (π : X ⟶ S) {c : ℕ} (p q : ℕ)
    (hE : ConormalRank i c)
    (hvan : SupportVanishing X.toRingedSpace (Set.range i.base) (isClosed_range_base i) c
      (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))))
    (hvan' : SupportVanishing X.toRingedSpace (Set.range i.base) (isClosed_range_base i) c
      (relativeDifferentialForms π (((p + 1 : ℕ) : ℤ) + (c : ℤ)))) :
    gysinCohomologyMap (Set.range i.base) (isClosed_range_base i) c
          (pushforwardRelativeForms i π (p : ℤ))
          (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))) hvan
          (conormalGysinHom i π p hE ≫ (conormalGysinTargetIso i π c p).hom) q ≫
        abelianHgroupMap X.toRingedSpace (0 : ℤ) ((q : ℤ) + (c : ℤ)) (q + c)
          (by omega) (ambientDeRhamShiftAbHom π c p) =
      abelianHgroupMap X.toRingedSpace (c : ℤ) ((q : ℤ) + (c : ℤ)) q
          (by omega) (pushforwardDeRhamDifferentialAbHom i π p) ≫
        gysinCohomologyMap (Set.range i.base) (isClosed_range_base i) c
          (pushforwardRelativeForms i π ((p + 1 : ℕ) : ℤ))
          (relativeDifferentialForms π (((p + 1 : ℕ) : ℤ) + (c : ℤ))) hvan'
          (conormalGysinHom i π (p + 1) hE ≫
            (conormalGysinTargetIso i π c (p + 1)).hom) q :=
  gysinCohomologyMap_comm X.toRingedSpace (Set.range i.base) (isClosed_range_base i) c q
    hvan hvan' _ _ (pushforwardDeRhamDifferentialAbHom i π p)
    (ambientDeRhamShiftAbHom π c p)
    (pushforwardLocalCohomologyAbelianMap (isClosed_range_base i) c
      (ambientDeRhamShiftAbHom π c p))
    (paste_square (abelianSheaf X) (conormalGysinHom i π p hE)
      (conormalGysinHom i π (p + 1) hE) (conormalGysinTargetIso i π c p).hom
      (conormalGysinTargetIso i π c (p + 1)).hom (gysinTargetDeRhamHom i π c p) _ _
      (conormalGysinHom_comm_deRham i π p hE)
      (gysinTargetDeRhamHom_comm_conormalGysinTargetIso i π c p))
    (edgeCommutesWithAbelian (isClosed_range_base i) c _ _ hvan hvan'
      (ambientDeRhamShiftAbHom π c p))

/-- **The tagged [Stacks, Tag 0G8A] map at the glued `γ^p` is the map this file's square is
about, preceded by the affine-pushforward comparison of [Stacks, Tag 089W].**  The two sides are
definitionally equal: `Stacks.DeRham.CohomologicalGysin.gysinHodgeFormsMapOfConormalRank` is
`gysinHodgeFormsMap` at `conormalGysinHom ≫ conormalGysinTargetIso`, and `gysinHodgeFormsMap` is
`gysinCohomologyMap` with its source rewritten from `H^q(X, i_*Ω^p_{Z/S})` to `H^q(Z, Ω^p_{Z/S})`
by `Stacks.AffineCohomologyResolution.cohomologyPushforwardIso`.

So the square proved here is a square for the tagged `γ^{p,q}` of [Stacks, Tag 0G8A] and not for a
second construction; this is the counterpart of
`Stacks.DeRham.GysinCohomologyDeRham.equationGysinHodgeMap_eq` for the glued Gysin map. -/
theorem gysinHodgeFormsMapOfConormalRank_eq (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i] (π : X ⟶ S) {c : ℕ} (p : ℕ)
    (hE : ConormalRank i c)
    (hvan : SupportVanishing X.toRingedSpace (Set.range i.base) (isClosed_range_base i) c
      (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))))
    (q : ℕ) :
    gysinHodgeFormsMapOfConormalRank i π p hE hvan q =
      ((Stacks.AffineCohomologyResolution.cohomologyPushforwardIso i q).app
          ⟨relativeDifferentialForms (i ≫ π) (p : ℤ),
            isQuasicoherent_relativeDifferentialForms (i ≫ π) p⟩).hom ≫
        gysinCohomologyMap (Set.range i.base) (isClosed_range_base i) c
          (pushforwardRelativeForms i π (p : ℤ))
          (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))) hvan
          (conormalGysinHom i π p hE ≫ (conormalGysinTargetIso i π c p).hom) q := rfl

end Stacks.DeRham.GysinCohomologyDeRhamConormal

end
