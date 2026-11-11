module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.RestrictCrystallineDifferentials
public import StacksFrontier.AlgebraicGeometry.Crystalline.UniversalThickeningScheme

/-!
# The first-order universal thickening and an open subscheme of the base

Let `T` be a divided power scheme over a scheme `Y'`, along `f' : T ⟶ Y'`, and let `j : Y' ⟶ Y`
be an open immersion.  The sections of `𝒪_T` pulled back from `Y` along `f' ≫ j` are those pulled
back from `Y'` along `f'` (`Crystalline.baseSections_comp_of_isOpenImmersion`), so the universal
divided power derivation of `T` over `Y'` is one over `Y`, and the universal property of
`Ω_{T/Y,δ}` gives a map `Ω_{T/Y,δ} ⟶ Ω_{T/Y',δ}` carrying `d_{T/Y} b` to `d_{T/Y'} b`.  On the
first-order universal thickenings of [Stacks, Tag 07J2], `𝒪_{T'} = 𝒪_T ⊕ Ω_{T/·,δ}`, it gives a
morphism of divided power schemes `T'_{Y'} ⟶ T'_Y` which is the identity on underlying spaces and
on `𝒪_T`, and which commutes with the two projections `p₀, p₁` and with the diagonal `i`.

For a restricted situation `(p, S|_W, V)` of a global crystalline situation and an object `B` of
`CRIS(V/S|_W)`, this is a morphism of `CRIS(X/S)` from the extension of the first-order
thickening of `B` to the first-order thickening of the extension of `B`, compatible with `p₀` and
`p₁` (`...SmallSite.firstOrderThickeningCrysExtendHom` and its two relations).  This is what
identifies the canonical connections of [Stacks, Tag 07J6] of a crystal and of its restriction.

Only this morphism and its relations are proved here; it is in fact an isomorphism, which is not
needed and not proved.

## Main definitions

* `Crystalline.dpDifferentialsOpenBaseMap` — the map `Ω_{T/Y,δ} ⟶ Ω_{T/Y',δ}`.
* `Crystalline.firstOrderThickeningOpenBaseSchemeMap` — the morphism of schemes `T'_{Y'} ⟶ T'_Y`.
* `Crystalline.GlobalCrystallineSituation.firstOrderThickeningExtendHom` — the morphism of
  `CRIS(X/S)` from the extension of the first-order thickening of an object of `CRIS(V/S|_W)` to
  the first-order thickening of its extension.
* `Crystalline.GlobalCrystallineSituation.SmallSite.firstOrderThickeningCrysExtendHom` — the same
  in `Cris(X/S)`.

## Main results

* `Crystalline.dpDifferentialsOpenBaseMap_sheafApp` — the map carries `d_{T/Y} b` to `d_{T/Y'} b`.
* `Crystalline.GlobalCrystallineSituation.SmallSite.firstOrderThickeningCrysExtendHom_comp_P₀`
  and `..._comp_P₁` — the morphism commutes with the two projections.

## References

* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07IW](https://stacks.math.columbia.edu/tag/07IW)
* [Stacks Project, Tag 07KL](https://stacks.math.columbia.edu/tag/07KL)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace PresheafOfModules
open scoped AlgebraicGeometry

universe u

namespace Crystalline

section OpenBase

variable (T : DividedPowerScheme.{u}) {Y' Y : Scheme.{u}} (f' : T.scheme ⟶ Y') (j : Y' ⟶ Y)
  [IsOpenImmersion j]

/-! ### The map on divided power differentials -/

/-- The universal divided power derivation of `T` over `Y'` kills every section pulled back from
`Y` along `f' ≫ j`, those being pulled back from `Y'`. -/
theorem sheafApp_appLE_comp (Wo : T.scheme.Opens) (V : Y.Opens) (h : Wo ≤ (f' ≫ j) ⁻¹ᵁ V)
    (a : Γ(Y, V)) : sheafApp T Y' f' Wo ((f' ≫ j).appLE V Wo h a) = 0 :=
  sheafApp_base T Y' f' Wo
    (baseSections_comp_of_isOpenImmersion T f' j Wo ▸ appLE_mem_baseSections T Y (f' ≫ j) Wo V h a)

/-- The universal divided power derivation of `T` over `Y'`, over an open `Wo` of `T` lying above an
open `V` of `Y`, as a divided power `Γ(V, 𝒪_Y)`-derivation. -/
def dpDerivationAtOpenBase (Wo : T.scheme.Opens) (V : Y.Opens) (h : Wo ≤ (f' ≫ j) ⁻¹ᵁ V) :
    DividedPowerDerivation Γ(Y, V) (T.dividedPowers.toDividedPowerRing (op Wo))
      ((f' ≫ j).appLE V Wo h).hom Γ(dpDifferentialsSheaf T Y' f', Wo) where
  toDerivation :=
    Derivation.mk'
      (AddMonoidHom.toIntLinearMap
        (AddMonoidHom.mk' (sheafApp T Y' f' Wo) (sheafApp_add T Y' f' Wo)))
      (sheafApp_mul T Y' f' Wo)
  map_ringHom' a := sheafApp_appLE_comp T f' j Wo V h a
  map_dpow' n hn x hx := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact sheafApp_dpow T Y' f' Wo k x hx

/-- **The universal divided power derivation of `T` over `Y'`, read as a divided power derivation
over `Y` along `f' ≫ j`.** -/
def openBaseDerivation :
    DividedPowerSchemeDerivation T Y (f' ≫ j) (dpDifferentialsSheaf T Y' f') where
  app Wo := sheafApp T Y' f' Wo
  naturality i x := sheafApp_naturality T Y' f' i x
  dividedPowerDerivation Wo V h := dpDerivationAtOpenBase T f' j Wo V h
  dividedPowerDerivation_apply _ _ _ _ := rfl

/-- **The map `Ω_{T/Y,δ} ⟶ Ω_{T/Y',δ}`** induced, by the universal property of `Ω_{T/Y,δ}`, by
the universal divided power derivation of `T` over `Y'`. -/
def dpDifferentialsOpenBaseMap :
    dpDifferentialsSheaf T Y (f' ≫ j) ⟶ dpDifferentialsSheaf T Y' f' :=
  (universalDPSchemeDerivation_isUniversal T Y (f' ≫ j) _ (openBaseDerivation T f' j)).choose

/-- **The map `Ω_{T/Y,δ} ⟶ Ω_{T/Y',δ}` carries `d_{T/Y} b` to `d_{T/Y'} b`.** -/
theorem dpDifferentialsOpenBaseMap_sheafApp (Wo : T.scheme.Opens) (b : Γ(T.scheme, Wo)) :
    (dpDifferentialsOpenBaseMap T f' j).app Wo (sheafApp T Y (f' ≫ j) Wo b) =
      sheafApp T Y' f' Wo b :=
  (universalDPSchemeDerivation_isUniversal T Y (f' ≫ j) _
    (openBaseDerivation T f' j)).choose_spec.1 Wo b

/-- The map `Ω_{T/Y,δ} ⟶ Ω_{T/Y',δ}` commutes with restriction. -/
theorem dpDifferentialsOpenBaseMap_naturality {Wo Wo' : T.scheme.Opens} (i : Wo' ⟶ Wo)
    (ω : Γ(dpDifferentialsSheaf T Y (f' ≫ j), Wo)) :
    (dpDifferentialsSheaf T Y' f').presheaf.map i.op
        ((dpDifferentialsOpenBaseMap T f' j).app Wo ω) =
      (dpDifferentialsOpenBaseMap T f' j).app Wo'
        ((dpDifferentialsSheaf T Y (f' ≫ j)).presheaf.map i.op ω) :=
  (congrArg
    (fun φ : (dpDifferentialsSheaf T Y (f' ≫ j)).presheaf.obj (op Wo) ⟶
      (dpDifferentialsSheaf T Y' f').presheaf.obj (op Wo') => ConcreteCategory.hom φ ω)
    ((dpDifferentialsOpenBaseMap T f' j).mapPresheaf.naturality i.op)).symm

/-! ### The map on the structure sheaves of the first-order thickenings -/

/-- **The map on sections `𝒪_{T'_Y} ⟶ 𝒪_{T'_{Y'}}`**, `(b, ω) ↦ (b, φ ω)` with `φ` the map
`Ω_{T/Y,δ} ⟶ Ω_{T/Y',δ}`. -/
def firstOrderThickeningOpenBaseApp (W : (Opens ↑T.scheme)ᵒᵖ) :
    (firstOrderThickeningPresheaf T Y (f' ≫ j)).obj W ⟶
      (firstOrderThickeningPresheaf T Y' f').obj W :=
  sqZeroExtLift (dpDifferentialsModules T Y' f')
    ((sqZeroExtProj (dpDifferentialsModules T Y (f' ≫ j))).app W)
    (AddMonoidHom.mk' (fun x => (dpDifferentialsOpenBaseMap T f' j).app W.unop (sqZeroExtSnd x))
      (fun x y => map_add _ (sqZeroExtSnd x) (sqZeroExtSnd y)))
    (fun a b =>
      (map_add _ (sqZeroExtFst a • sqZeroExtSnd b) (sqZeroExtFst b • sqZeroExtSnd a)).trans
        (congrArg₂ (· + ·)
          (Scheme.Modules.Hom.app_smul (dpDifferentialsOpenBaseMap T f' j)
            (sqZeroExtFst a) (sqZeroExtSnd b))
          (Scheme.Modules.Hom.app_smul (dpDifferentialsOpenBaseMap T f' j)
            (sqZeroExtFst b) (sqZeroExtSnd a))))

/-- The first component of the map on sections is the identity. -/
@[simp]
theorem firstOrderThickeningOpenBaseApp_fst (W : (Opens ↑T.scheme)ᵒᵖ)
    (x : ↑((firstOrderThickeningPresheaf T Y (f' ≫ j)).obj W)) :
    sqZeroExtFst ((firstOrderThickeningOpenBaseApp T f' j W).hom x) = sqZeroExtFst x := rfl

/-- The second component of the map on sections is the map on divided power differentials. -/
@[simp]
theorem firstOrderThickeningOpenBaseApp_snd (W : (Opens ↑T.scheme)ᵒᵖ)
    (x : ↑((firstOrderThickeningPresheaf T Y (f' ≫ j)).obj W)) :
    sqZeroExtSnd ((firstOrderThickeningOpenBaseApp T f' j W).hom x) =
      (dpDifferentialsOpenBaseMap T f' j).app W.unop (sqZeroExtSnd x) := rfl

/-- **The map on the structure sheaves of the first-order thickenings**, as a morphism of
presheaves of commutative rings. -/
def firstOrderThickeningOpenBasePresheaf :
    firstOrderThickeningPresheaf T Y (f' ≫ j) ⟶ firstOrderThickeningPresheaf T Y' f' where
  app W := firstOrderThickeningOpenBaseApp T f' j W
  naturality _ _ i := CommRingCat.hom_ext (RingHom.ext fun x => sqZeroExt_ext rfl
    (dpDifferentialsOpenBaseMap_naturality T f' j i.unop (sqZeroExtSnd x)).symm)

/-! ### The morphism of schemes -/

/-- The map of the first-order thickenings as a morphism of sheafed spaces, the identity on
underlying spaces. -/
def firstOrderThickeningOpenBaseRawMap :
    firstOrderThickeningSheafedSpace T Y' f' ⟶ firstOrderThickeningSheafedSpace T Y (f' ≫ j) :=
  ⟨{ base := 𝟙 _, c := firstOrderThickeningOpenBasePresheaf T f' j }⟩

/-- The map of the first-order thickenings composed with the immersion `T ⟶ T'_{Y'}` is the
immersion `T ⟶ T'_Y`, as morphisms of sheafed spaces. -/
theorem firstOrderThickeningι_comp_openBaseRawMap :
    (firstOrderThickeningExtension T Y' f').inclusion ≫ firstOrderThickeningOpenBaseRawMap T f' j =
      (Scheme.Hom.toLRSHom (firstOrderThickeningι T Y (f' ≫ j))).toShHom := by
  rfl

/-- The map of the first-order thickenings induces a local homomorphism on every stalk: composed
with the immersion `T ⟶ T'_{Y'}` it is the immersion `T ⟶ T'_Y`, so the stalk map has a
retraction by a local homomorphism. -/
theorem firstOrderThickeningOpenBaseRawMap_isLocalHom (x : ↑T.scheme) :
    IsLocalHom (((firstOrderThickeningOpenBaseRawMap T f' j).hom.stalkMap x).hom) := by
  have hlocal : IsLocalHom ((((firstOrderThickeningExtension T Y' f').inclusion.hom ≫
      (firstOrderThickeningOpenBaseRawMap T f' j).hom).stalkMap x).hom) :=
    LocallyRingedSpace.isLocalHom_stalkMap_congr _ _
      (firstOrderThickeningι_comp_openBaseRawMap T f' j).symm x
      (LocallyRingedSpace.isLocalHomStalkMap
        (Scheme.Hom.toLRSHom (firstOrderThickeningι T Y (f' ≫ j))) x)
  have hstalk : ((((firstOrderThickeningExtension T Y' f').inclusion.hom ≫
        (firstOrderThickeningOpenBaseRawMap T f' j).hom).stalkMap x).hom) =
      (((firstOrderThickeningExtension T Y' f').inclusion.hom.stalkMap x).hom).comp
        (((firstOrderThickeningOpenBaseRawMap T f' j).hom.stalkMap x).hom) := by
    rw [PresheafedSpace.stalkMap.comp]
    rfl
  have hcomp : IsLocalHom
      ((((firstOrderThickeningExtension T Y' f').inclusion.hom.stalkMap x).hom).comp
        (((firstOrderThickeningOpenBaseRawMap T f' j).hom.stalkMap x).hom)) := by
    rw [← hstalk]
    exact hlocal
  exact isLocalHom_of_comp (((firstOrderThickeningOpenBaseRawMap T f' j).hom.stalkMap x).hom)
    (((firstOrderThickeningExtension T Y' f').inclusion.hom.stalkMap x).hom)

/-- **The morphism of schemes `T'_{Y'} ⟶ T'_Y` between the first-order universal thickenings of
`T` over `Y'` and over `Y`.** -/
def firstOrderThickeningOpenBaseSchemeMap :
    firstOrderThickeningScheme T Y' f' ⟶ firstOrderThickeningScheme T Y (f' ≫ j) :=
  ⟨LocallyRingedSpace.homMk (firstOrderThickeningOpenBaseRawMap T f' j)
    (firstOrderThickeningOpenBaseRawMap_isLocalHom T f' j)⟩

/-- The morphism of schemes acts on sections by `(b, ω) ↦ (b, φ ω)`. -/
@[simp]
theorem firstOrderThickeningOpenBaseSchemeMap_c_app (W : (Opens ↑T.scheme)ᵒᵖ) :
    (firstOrderThickeningOpenBaseSchemeMap T f' j).c.app W =
      firstOrderThickeningOpenBaseApp T f' j W := rfl

/-- Two morphisms of schemes with the same map of spaces are equal if their maps of structure
sheaves agree pointwise. -/
private theorem scheme_hom_ext_of_heq' {X Z : Scheme.{u}} {f g : X ⟶ Z}
    (hb : f.base = g.base)
    (h : ∀ W x, HEq ((f.c.app W).hom x) ((g.c.app W).hom x)) : f = g := by
  apply congrArg Scheme.Hom.mk
  apply LocallyRingedSpace.Hom.ext'
  refine PresheafedSpace.hext _ _ hb ?_
  have key : ∀ {b b' : (X : TopCat) ⟶ (Z : TopCat)} (c : Z.presheaf ⟶ b _* X.presheaf)
      (c' : Z.presheaf ⟶ b' _* X.presheaf), b = b' →
      (∀ W x, HEq ((c.app W).hom x) ((c'.app W).hom x)) → HEq c c' := by
    rintro b _ c c' rfl h
    exact heq_of_eq (by ext W x; exact eq_of_heq (h (op W) x))
  exact key f.c g.c hb h

/-- **The immersion `T ⟶ T'_{Y'}` followed by the morphism `T'_{Y'} ⟶ T'_Y` is the immersion
`T ⟶ T'_Y`.** -/
theorem firstOrderThickeningι_comp_openBaseSchemeMap :
    firstOrderThickeningι T Y' f' ≫ firstOrderThickeningOpenBaseSchemeMap T f' j =
      firstOrderThickeningι T Y (f' ≫ j) := by
  rfl

/-- **The morphism `T'_{Y'} ⟶ T'_Y` commutes with the first projections.** -/
theorem firstOrderThickeningOpenBaseSchemeMap_comp_projHom :
    firstOrderThickeningOpenBaseSchemeMap T f' j ≫ firstOrderThickeningProjHom T Y (f' ≫ j) =
      firstOrderThickeningProjHom T Y' f' := by
  refine scheme_hom_ext_of_heq' rfl fun W x => ?_
  exact heq_of_eq (sqZeroExt_ext rfl
    (map_zero (ConcreteCategory.hom ((dpDifferentialsOpenBaseMap T f' j).app W.unop))))

/-- **The morphism `T'_{Y'} ⟶ T'_Y` commutes with the second projections**: the map on
differentials carries `d_{T/Y} b` to `d_{T/Y'} b`. -/
theorem firstOrderThickeningOpenBaseSchemeMap_comp_P₁Hom :
    firstOrderThickeningOpenBaseSchemeMap T f' j ≫ firstOrderThickeningP₁Hom T Y (f' ≫ j) =
      firstOrderThickeningP₁Hom T Y' f' := by
  refine scheme_hom_ext_of_heq' rfl fun W x => ?_
  exact heq_of_eq (sqZeroExt_ext rfl (dpDifferentialsOpenBaseMap_sheafApp T f' j W.unop x))

/-- **The map on sections `𝒪_{T'_Y} ⟶ 𝒪_{T'_{Y'}}` is a homomorphism of divided power rings**:
it is the identity on the first summand and semilinear on the second. -/
theorem firstOrderThickeningOpenBaseApp_isDPMorphism (U : T.scheme.Opens) :
    DividedPowers.IsDPMorphism
      (firstOrderThickeningDividedPowers T Y (f' ≫ j) (op U))
      (firstOrderThickeningDividedPowers T Y' f' (op U))
      (firstOrderThickeningOpenBaseApp T f' j (op U)).hom := by
  have hmem : ∀ x ∈ firstOrderThickeningIdeal T Y (f' ≫ j) (op U),
      (firstOrderThickeningOpenBaseApp T f' j (op U)).hom x ∈
        firstOrderThickeningIdeal T Y' f' (op U) :=
    fun _ hx => hx
  refine ⟨Ideal.map_le_iff_le_comap.mpr fun x hx => hmem x hx, ?_⟩
  intro n x hx
  match n with
  | 0 =>
      exact (firstOrderThickeningDividedPowers_dpow_zero _ _ _ _ (hmem x hx)).trans
        ((map_one _).symm.trans
          (congrArg (fun z => (firstOrderThickeningOpenBaseApp T f' j (op U)).hom z)
            (firstOrderThickeningDividedPowers_dpow_zero _ _ _ _ hx).symm))
  | k + 1 =>
      refine (firstOrderThickeningDividedPowers_dpow_succ _ _ _ _ k (hmem x hx)).trans ?_
      refine Eq.trans ?_ (congrArg (fun z => (firstOrderThickeningOpenBaseApp T f' j (op U)).hom z)
        (firstOrderThickeningDividedPowers_dpow_succ _ _ _ _ k hx).symm)
      exact sqZeroExt_ext rfl
        (Scheme.Modules.Hom.app_smul (dpDifferentialsOpenBaseMap T f' j)
          ((T.dividedPowers.dividedPowers (op U)).dpow k (sqZeroExtFst x))
          (sqZeroExtSnd x)).symm

end OpenBase

/-! ### The comparison for a restricted situation -/

namespace GlobalCrystallineSituation

variable (S : GlobalCrystallineSituation.{u}) (W : S.S.scheme.Opens) (V : S.X.Opens)
  (hVW : V ≤ sourceToBase S ⁻¹ᵁ W)

/-- **The morphism of divided power schemes from the first-order thickening of an object `B` of
`CRIS(V/S|_W)` to the first-order thickening of its extension to `CRIS(X/S)`.** -/
def firstOrderThickeningExtendDPMap (B : Thickening (restrict S W V hVW)) :
    firstOrderThickeningDPScheme (restrict S W V hVW) B ⟶
      firstOrderThickeningDPScheme S ((extend S W V hVW).obj B) where
  hom := firstOrderThickeningOpenBaseSchemeMap B.thickening.target B.toBase.hom
    (restrictSι S W V hVW).hom
  compatible U := firstOrderThickeningOpenBaseApp_isDPMorphism B.thickening.target B.toBase.hom
    (restrictSι S W V hVW).hom U

/-- The structure morphism to `S` of the extension of an object of `CRIS(V/S|_W)`. -/
theorem extend_obj_toBase_hom (B : Thickening (restrict S W V hVW)) :
    ((extend S W V hVW).obj B).toBase.hom = B.toBase.hom ≫ (restrictSι S W V hVW).hom := rfl

/-- The comparison of first-order thickenings commutes with the immersions of `U`. -/
theorem firstOrderThickeningExtend_immersion_naturality (B : Thickening (restrict S W V hVW)) :
    ((extend S W V hVW).obj
        (firstOrderThickeningObject (restrict S W V hVW) B)).thickening.immersion ≫
        (firstOrderThickeningExtendDPMap S W V hVW B).hom =
      𝟙 _ ≫ (firstOrderThickeningObject S ((extend S W V hVW).obj B)).thickening.immersion := by
  have h := firstOrderThickeningι_comp_openBaseSchemeMap B.thickening.target B.toBase.hom
    (restrictSι S W V hVW).hom
  exact (Category.assoc _ _ _).trans ((congrArg (B.thickening.immersion ≫ ·) h).trans
    (Category.id_comp _).symm)

/-- The comparison of first-order thickenings lies over the divided power base `S`. -/
theorem firstOrderThickeningExtend_base_naturality (B : Thickening (restrict S W V hVW)) :
    firstOrderThickeningExtendDPMap S W V hVW B ≫
        (firstOrderThickeningObject S ((extend S W V hVW).obj B)).toBase =
      ((extend S W V hVW).obj (firstOrderThickeningObject (restrict S W V hVW) B)).toBase := by
  apply DividedPowerScheme.Hom.ext
  have h := firstOrderThickeningOpenBaseSchemeMap_comp_projHom B.thickening.target B.toBase.hom
    (restrictSι S W V hVW).hom
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h).trans (Category.assoc _ _ _).symm)

/-- The structure morphism to `X` of the first-order thickening of the extension of an object of
`CRIS(V/S|_W)`. -/
theorem firstOrderThickeningObject_extend_toX (B : Thickening (restrict S W V hVW)) :
    (firstOrderThickeningObject S ((extend S W V hVW).obj B)).toX = B.toX ≫ V.ι := rfl

/-- The structure morphism to `X` of the extension of the first-order thickening of an object of
`CRIS(V/S|_W)`. -/
theorem extend_firstOrderThickeningObject_toX (B : Thickening (restrict S W V hVW)) :
    ((extend S W V hVW).obj (firstOrderThickeningObject (restrict S W V hVW) B)).toX =
      B.toX ≫ V.ι := rfl

/-- The comparison of first-order thickenings lies over `X`. -/
theorem firstOrderThickeningExtend_toX_naturality (B : Thickening (restrict S W V hVW)) :
    𝟙 B.thickening.source ≫ (firstOrderThickeningObject S ((extend S W V hVW).obj B)).toX =
      ((extend S W V hVW).obj (firstOrderThickeningObject (restrict S W V hVW) B)).toX :=
  (congrArg (𝟙 B.thickening.source ≫ ·) (firstOrderThickeningObject_extend_toX S W V hVW B)).trans
    ((Category.id_comp (B.toX ≫ V.ι)).trans
      (extend_firstOrderThickeningObject_toX S W V hVW B).symm)

/-- **The morphism of `CRIS(X/S)` from the extension of the first-order thickening of an object
`B` of `CRIS(V/S|_W)` to the first-order thickening of the extension of `B`.**  It is the identity
on the thickened scheme `U` and the map `T'_{S|_W} ⟶ T'_S` of first-order thickenings on the
ambient schemes. -/
def firstOrderThickeningExtendHom (B : Thickening (restrict S W V hVW)) :
    (extend S W V hVW).obj (firstOrderThickeningObject (restrict S W V hVW) B) ⟶
      firstOrderThickeningObject S ((extend S W V hVW).obj B) where
  sourceHom := 𝟙 B.thickening.source
  targetHom := firstOrderThickeningExtendDPMap S W V hVW B
  immersion_naturality := firstOrderThickeningExtend_immersion_naturality S W V hVW B
  base_naturality := firstOrderThickeningExtend_base_naturality S W V hVW B
  toX_naturality := firstOrderThickeningExtend_toX_naturality S W V hVW B

/-- The map of thickened schemes of the comparison followed by `p₀` is the identity of `U`. -/
theorem firstOrderThickeningExtendHom_comp_P₀_sourceHom (B : Thickening (restrict S W V hVW)) :
    (firstOrderThickeningExtendHom S W V hVW B ≫
        firstOrderThickeningSiteP₀ S ((extend S W V hVW).obj B)).sourceHom =
      𝟙 B.thickening.source :=
  Category.id_comp (𝟙 B.thickening.source)

/-- The map of thickened schemes of the comparison followed by `p₁` is the identity of `U`. -/
theorem firstOrderThickeningExtendHom_comp_P₁_sourceHom (B : Thickening (restrict S W V hVW)) :
    (firstOrderThickeningExtendHom S W V hVW B ≫
        firstOrderThickeningSiteP₁ S ((extend S W V hVW).obj B)).sourceHom =
      𝟙 B.thickening.source :=
  Category.id_comp (𝟙 B.thickening.source)

/-- The map of thickened schemes of the extension of `p₀` is the identity of `U`. -/
theorem extend_map_firstOrderThickeningSiteP₀_sourceHom (B : Thickening (restrict S W V hVW)) :
    ((extend S W V hVW).map (firstOrderThickeningSiteP₀ (restrict S W V hVW) B)).sourceHom =
      𝟙 B.thickening.source := rfl

/-- The map of thickened schemes of the extension of `p₁` is the identity of `U`. -/
theorem extend_map_firstOrderThickeningSiteP₁_sourceHom (B : Thickening (restrict S W V hVW)) :
    ((extend S W V hVW).map (firstOrderThickeningSiteP₁ (restrict S W V hVW) B)).sourceHom =
      𝟙 B.thickening.source := rfl

/-- **The comparison morphism commutes with the first projections.** -/
theorem firstOrderThickeningExtendHom_comp_P₀ (B : Thickening (restrict S W V hVW)) :
    firstOrderThickeningExtendHom S W V hVW B ≫
        firstOrderThickeningSiteP₀ S ((extend S W V hVW).obj B) =
      (extend S W V hVW).map (firstOrderThickeningSiteP₀ (restrict S W V hVW) B) :=
  Thickening.Hom.ext ((firstOrderThickeningExtendHom_comp_P₀_sourceHom S W V hVW B).trans
      (extend_map_firstOrderThickeningSiteP₀_sourceHom S W V hVW B).symm)
    (DividedPowerScheme.Hom.ext (firstOrderThickeningOpenBaseSchemeMap_comp_projHom
      B.thickening.target B.toBase.hom (restrictSι S W V hVW).hom))

/-- **The comparison morphism commutes with the second projections.** -/
theorem firstOrderThickeningExtendHom_comp_P₁ (B : Thickening (restrict S W V hVW)) :
    firstOrderThickeningExtendHom S W V hVW B ≫
        firstOrderThickeningSiteP₁ S ((extend S W V hVW).obj B) =
      (extend S W V hVW).map (firstOrderThickeningSiteP₁ (restrict S W V hVW) B) :=
  Thickening.Hom.ext ((firstOrderThickeningExtendHom_comp_P₁_sourceHom S W V hVW B).trans
      (extend_map_firstOrderThickeningSiteP₁_sourceHom S W V hVW B).symm)
    (DividedPowerScheme.Hom.ext (firstOrderThickeningOpenBaseSchemeMap_comp_P₁Hom
      B.thickening.target B.toBase.hom (restrictSι S W V hVW).hom))

namespace SmallSite

/-- **The comparison morphism in `Cris(X/S)`**: from the extension of the first-order thickening
of an object `B` of `Cris(V/S|_W)` to the first-order thickening of the extension of `B`. -/
def firstOrderThickeningCrysExtendHom (B : CrystallineThickening (restrict S W V hVW)) :
    (smallExtend S W V hVW).obj (firstOrderThickeningCrysObject (restrict S W V hVW) B) ⟶
      firstOrderThickeningCrysObject S ((smallExtend S W V hVW).obj B) :=
  ObjectProperty.homMk (firstOrderThickeningExtendHom S W V hVW B.obj)

/-- **The comparison morphism in `Cris(X/S)` commutes with the first projections.** -/
theorem firstOrderThickeningCrysExtendHom_comp_P₀ (B : CrystallineThickening (restrict S W V hVW)) :
    firstOrderThickeningCrysExtendHom S W V hVW B ≫
        firstOrderThickeningCrysP₀ S ((smallExtend S W V hVW).obj B) =
      (smallExtend S W V hVW).map (firstOrderThickeningCrysP₀ (restrict S W V hVW) B) :=
  ObjectProperty.hom_ext _ (firstOrderThickeningExtendHom_comp_P₀ S W V hVW B.obj)

/-- **The comparison morphism in `Cris(X/S)` commutes with the second projections.** -/
theorem firstOrderThickeningCrysExtendHom_comp_P₁ (B : CrystallineThickening (restrict S W V hVW)) :
    firstOrderThickeningCrysExtendHom S W V hVW B ≫
        firstOrderThickeningCrysP₁ S ((smallExtend S W V hVW).obj B) =
      (smallExtend S W V hVW).map (firstOrderThickeningCrysP₁ (restrict S W V hVW) B) :=
  ObjectProperty.hom_ext _ (firstOrderThickeningExtendHom_comp_P₁ S W V hVW B.obj)

end SmallSite

end GlobalCrystallineSituation

end Crystalline

end
