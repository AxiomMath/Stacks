module

public import StacksFrontier.AlgebraicGeometry.Crystalline.UniversalThickeningScheme

/-!
# Functoriality of the first-order universal thickening

Let `g : (U, T, δ) ⟶ (U₁, T₁, δ₁)` be a morphism of the big crystalline category `CRIS(X/S)` of a
global crystalline situation, and write `gh : T ⟶ T₁` for the morphism of ambient schemes.
`StacksFrontier/AlgebraicGeometry/Crystalline/UniversalThickeningScheme.lean` builds the first-order
universal thickening `(U, T', δ')` of [Stacks, Tag 07J2] of an object, with its two projections
`p₀, p₁ : T' ⟶ T`.  This module builds the induced morphism `(U, T', δ') ⟶ (U₁, T₁', δ₁')` of
`CRIS(X/S)` and proves the two relations `G ∘ p₀ = p₀ ∘ g` and `G ∘ p₁ = p₁ ∘ g` that make the
family of first-order thickenings a functor over the identity of `CRIS(X/S)`.

The construction is forced by `𝒪_{T'} = 𝒪_T ⊕ Ω_{T/S,δ}`: on sections it has to be
`(b, ω) ↦ (gh^# b, dg ω)`, so everything rests on a map `dg : Ω_{T₁/S,δ₁} → gh_* Ω_{T/S,δ}` with
`dg ∘ d_{T₁} = d_T ∘ gh^#`.  That map is produced by the universal property of the sheaf of
divided power differentials: `b ↦ d_T(gh^# b)` is a divided power derivation of `𝒪_{T₁}` over `S`
with values in the pushforward `gh_* Ω_{T/S,δ}`, which is a sheaf of `𝒪_{T₁}`-modules, because
`gh` is a morphism over the divided power base and a homomorphism of divided power rings on
sections.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.dpDifferentialsMapSheaf` — the map
  `Ω_{T₁/S,δ₁} ⟶ gh_* Ω_{T/S,δ}` on sheaves of divided power differentials.
* `Crystalline.GlobalCrystallineSituation.firstOrderThickeningSchemeMap` — the morphism of
  schemes `T' ⟶ T₁'`.
* `Crystalline.GlobalCrystallineSituation.firstOrderThickeningDPMap` — the same as a morphism of
  divided power schemes `(T', J', δ') ⟶ (T₁', J₁', δ₁')`.
* `Crystalline.GlobalCrystallineSituation.firstOrderThickeningSiteMap` — **the functoriality
  datum**: the morphism `(U, T', δ') ⟶ (U₁, T₁', δ₁')` of `CRIS(X/S)`.

## Main results

* `Crystalline.GlobalCrystallineSituation.dpDifferentialsMapSheaf_sheafApp` — the key
  computation `dg ∘ d_{T₁} = d_T ∘ gh^#`.
* `Crystalline.GlobalCrystallineSituation.firstOrderThickeningSiteMap_comp_P₀` and
  `Crystalline.GlobalCrystallineSituation.firstOrderThickeningSiteMap_comp_P₁` — the two
  relations of the diagram of [Stacks, Tag 07J2].
* `Crystalline.GlobalCrystallineSituation.firstOrderThickeningSiteMap_id` and
  `Crystalline.GlobalCrystallineSituation.firstOrderThickeningSiteMap_comp` — the datum is
  functorial.

## Implementation notes

The morphism of schemes is built directly on the locally ringed space of
`Crystalline.firstOrderThickeningScheme`, whose topological space is that of `T`, so the map of
spaces is the one of `gh` and only the map of sheaves carries information.  Locality on stalks
is obtained, as for the two projections in the previous module, from a retraction: composing
with the immersion `T ⟶ T'` of the source gives the morphism of schemes
`gh` followed by the immersion `T₁ ⟶ T₁'`, whose stalk maps are local, and a ring map with a
retraction by a local homomorphism is local.

## References

* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07I6](https://stacks.math.columbia.edu/tag/07I6)
* [Stacks Project, Tag 07IW](https://stacks.math.columbia.edu/tag/07IW)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace PresheafOfModules
open scoped AlgebraicGeometry

universe u

namespace Crystalline

/-- **Sections pulled back from the base stay pulled back from the base.**  If `gh` is a morphism
over the base, the image of a section of `𝒪_{T_B}` pulled back from `Y` is a section of
`𝒪_{T_A}` pulled back from `Y`. -/
public theorem map_mem_baseSections_of_comp {TA TB : DividedPowerScheme.{u}} {Y : Scheme.{u}}
    (gh : TA.scheme ⟶ TB.scheme) (fB : TB.scheme ⟶ Y) (fA : TA.scheme ⟶ Y)
    (hfac : gh ≫ fB = fA) (W : TB.scheme.Opens) {b : Γ(TB.scheme, W)}
    (hb : b ∈ baseSections TB Y fB W) :
    gh.app W b ∈ baseSections TA Y fA (gh ⁻¹ᵁ W) := by
  obtain ⟨V, h, a, rfl⟩ := hb
  subst hfac
  refine ⟨V, ((Opens.map gh.base).map (homOfLE h)).le, a, ?_⟩
  rw [← Scheme.Hom.appLE_eq_app (f := gh) (U := W), ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_comp_appLE]

/-- Two morphisms of schemes with the same map of spaces are equal if their maps of structure
sheaves agree pointwise. -/
private theorem scheme_hom_ext_of_heq {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (hb : f.base = g.base)
    (h : ∀ W x, HEq ((f.c.app W).hom x) ((g.c.app W).hom x)) : f = g := by
  apply congrArg Scheme.Hom.mk
  apply LocallyRingedSpace.Hom.ext'
  refine PresheafedSpace.hext _ _ hb ?_
  have key : ∀ {b b' : (X : TopCat) ⟶ (Y : TopCat)} (c : Y.presheaf ⟶ b _* X.presheaf)
      (c' : Y.presheaf ⟶ b' _* X.presheaf), b = b' →
      (∀ W x, HEq ((c.app W).hom x) ((c'.app W).hom x)) → HEq c c' := by
    rintro b _ c c' rfl h
    exact heq_of_eq (by ext W x; exact eq_of_heq (h (op W) x))
  exact key f.c g.c hb h

namespace GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

/-- The sheaf `Ω_{T/S,δ}` of divided power differentials of the ambient divided power scheme of
an object of `CRIS(X/S)`. -/
public abbrev objDPDifferentials (A : Thickening S) : A.thickening.target.scheme.Modules :=
  dpDifferentialsSheaf A.thickening.target S.S.scheme A.toBase.hom

/-- The universal divided power derivation of the ambient divided power scheme of an object of
`CRIS(X/S)`, on sections over an open. -/
public abbrev objSheafApp (A : Thickening S) (W : A.thickening.target.scheme.Opens) :
    Γ(A.thickening.target.scheme, W) → Γ(objDPDifferentials A, W) :=
  sheafApp A.thickening.target S.S.scheme A.toBase.hom W

variable {A B : Thickening S}

/-- The morphism of ambient schemes underlying a morphism of `CRIS(X/S)`. -/
public abbrev ambientHom (g : A ⟶ B) :
    A.thickening.target.scheme ⟶ B.thickening.target.scheme := g.targetHom.hom

/-! ### The map on divided power differentials -/

/-- The ambient morphism of a morphism of `CRIS(X/S)` is a morphism over the divided power
base. -/
public theorem ambientHom_comp_toBase (g : A ⟶ B) :
    ambientHom g ≫ B.toBase.hom = A.toBase.hom :=
  congrArg DividedPowerScheme.Hom.hom g.base_naturality

/-- The maps on sections of the ambient morphism commute with restriction. -/
public theorem ambientHom_app_map (g : A ⟶ B) {W W' : B.thickening.target.scheme.Opens}
    (i : W' ⟶ W) (x : Γ(B.thickening.target.scheme, W)) :
    A.thickening.target.scheme.presheaf.map ((Opens.map (ambientHom g).base).map i).op
        ((ambientHom g).app W x) =
      (ambientHom g).app W' (B.thickening.target.scheme.presheaf.map i.op x) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  exact congrArg
    (fun φ : Γ(B.thickening.target.scheme, W) ⟶
      Γ(A.thickening.target.scheme, ambientHom g ⁻¹ᵁ W') => ConcreteCategory.hom φ x)
    (Scheme.Hom.naturality (f := ambientHom g) (U := W') (U' := W) i.op).symm

/-- The pushforward along the ambient morphism of the sheaf of divided power differentials of the
source: a sheaf of modules on the ambient scheme of the target. -/
public abbrev pushforwardDPDifferentials (g : A ⟶ B) : B.thickening.target.scheme.Modules :=
  (Scheme.Modules.pushforward (ambientHom g)).obj (objDPDifferentials A)

/-- **The universal divided power derivation of the source, composed with the ambient
morphism.**  On sections over an open `W` of the ambient scheme of the target it carries `b` to
`d_{T_A}(gh^# b)`. -/
public abbrev ambientDPApp (g : A ⟶ B) (W : B.thickening.target.scheme.Opens)
    (b : Γ(B.thickening.target.scheme, W)) : Γ(objDPDifferentials A, ambientHom g ⁻¹ᵁ W) :=
  objSheafApp A (ambientHom g ⁻¹ᵁ W) ((ambientHom g).app W b)

/-- The composite derivation is additive on sections. -/
public theorem ambientDPApp_add (g : A ⟶ B) (W : B.thickening.target.scheme.Opens)
    (x y : Γ(B.thickening.target.scheme, W)) :
    ambientDPApp g W (x + y) = ambientDPApp g W x + ambientDPApp g W y := by
  show objSheafApp A _ ((ambientHom g).app W (x + y)) = _
  rw [map_add]
  exact sheafApp_add _ _ _ _ _ _

/-- The Leibniz rule for the composite derivation. -/
public theorem ambientDPApp_mul (g : A ⟶ B) (W : B.thickening.target.scheme.Opens)
    (x y : Γ(B.thickening.target.scheme, W)) :
    ambientDPApp g W (x * y) =
      (ambientHom g).app W x • ambientDPApp g W y +
        (ambientHom g).app W y • ambientDPApp g W x := by
  show objSheafApp A _ ((ambientHom g).app W (x * y)) = _
  rw [map_mul]
  exact sheafApp_mul _ _ _ _ _ _

/-- The composite derivation kills every section pulled back from the divided power base. -/
public theorem ambientDPApp_base (g : A ⟶ B) (W : B.thickening.target.scheme.Opens)
    (V : S.S.scheme.Opens) (h : W ≤ B.toBase.hom ⁻¹ᵁ V) (a : Γ(S.S.scheme, V)) :
    ambientDPApp g W (B.toBase.hom.appLE V W h a) = 0 :=
  sheafApp_base A.thickening.target S.S.scheme A.toBase.hom (ambientHom g ⁻¹ᵁ W)
    (map_mem_baseSections_of_comp (ambientHom g) B.toBase.hom A.toBase.hom
      (ambientHom_comp_toBase g) W
      (appLE_mem_baseSections B.thickening.target S.S.scheme B.toBase.hom W V h a))

/-- The divided power chain rule for the composite derivation. -/
public theorem ambientDPApp_dpow (g : A ⟶ B) (W : B.thickening.target.scheme.Opens) (n : ℕ)
    (x : Γ(B.thickening.target.scheme, W))
    (hx : x ∈ B.thickening.target.ideal.obj (op W)) :
    ambientDPApp g W ((B.thickening.target.dividedPowers.dividedPowers (op W)).dpow (n + 1) x) =
      (ambientHom g).app W ((B.thickening.target.dividedPowers.dividedPowers (op W)).dpow n x) •
        ambientDPApp g W x := by
  have hx' : (ambientHom g).app W x ∈
      A.thickening.target.ideal.obj (op (ambientHom g ⁻¹ᵁ W)) :=
    mem_ideal_of_isDPMorphism (g.targetHom.compatible W) hx
  set dB := B.thickening.target.dividedPowers.dividedPowers (op W) with hdB
  show objSheafApp A _ ((ambientHom g).app W (dB.dpow (n + 1) x)) = _
  rw [← g.targetHom.dpow_comp W x hx, ← g.targetHom.dpow_comp W x hx]
  exact sheafApp_dpow A.thickening.target S.S.scheme A.toBase.hom
    (ambientHom g ⁻¹ᵁ W) n ((ambientHom g).app W x) hx'

/-- The composite derivation commutes with restriction. -/
public theorem ambientDPApp_naturality (g : A ⟶ B)
    {W W' : B.thickening.target.scheme.Opens} (i : W' ⟶ W)
    (x : Γ(B.thickening.target.scheme, W)) :
    (objDPDifferentials A).presheaf.map ((Opens.map (ambientHom g).base).map i).op
        (ambientDPApp g W x) =
      ambientDPApp g W' (B.thickening.target.scheme.presheaf.map i.op x) := by
  show (objDPDifferentials A).presheaf.map ((Opens.map (ambientHom g).base).map i).op
      (objSheafApp A _ ((ambientHom g).app W x)) = _
  rw [sheafApp_naturality A.thickening.target S.S.scheme A.toBase.hom
    ((Opens.map (ambientHom g).base).map i) ((ambientHom g).app W x), ambientHom_app_map]

/-- **The divided power derivation of the ambient scheme of the target induced by the ambient
morphism**: the universal divided power derivation of the source, precomposed with the maps on
sections of the ambient morphism, with values in the pushforward of the differentials of the
source. -/
public def ambientDPDerivation (g : A ⟶ B) :
    DividedPowerSchemeDerivation B.thickening.target S.S.scheme B.toBase.hom
      (pushforwardDPDifferentials g) where
  app W b := ambientDPApp g W b
  naturality i x := by exact ambientDPApp_naturality g i x
  dividedPowerDerivation W V h :=
    { toDerivation :=
        Derivation.mk'
          (AddMonoidHom.toIntLinearMap
            (AddMonoidHom.mk' (fun b => ambientDPApp g W b) (ambientDPApp_add g W)))
          (by exact ambientDPApp_mul g W)
      map_ringHom' a := by exact ambientDPApp_base g W V h a
      map_dpow' n hn x hx := by
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        exact ambientDPApp_dpow g W k x hx }
  dividedPowerDerivation_apply _ _ _ _ := rfl

/-- **The map on sheaves of divided power differentials induced by a morphism of `CRIS(X/S)`.**
It is the unique map of sheaves of modules carrying the universal divided power derivation of
the target to the universal divided power derivation of the source composed with the ambient
morphism. -/
public def dpDifferentialsMapSheaf (g : A ⟶ B) :
    objDPDifferentials B ⟶ pushforwardDPDifferentials g :=
  (universalDPSchemeDerivation_isUniversal B.thickening.target S.S.scheme B.toBase.hom
    (pushforwardDPDifferentials g) (ambientDPDerivation g)).choose

/-- **The map on divided power differentials carries `d_{T_B} b` to `d_{T_A}(gh^# b)`.** -/
public theorem dpDifferentialsMapSheaf_sheafApp (g : A ⟶ B)
    (W : B.thickening.target.scheme.Opens) (b : Γ(B.thickening.target.scheme, W)) :
    (dpDifferentialsMapSheaf g).app W (objSheafApp B W b) = ambientDPApp g W b :=
  (universalDPSchemeDerivation_isUniversal B.thickening.target S.S.scheme B.toBase.hom
    (pushforwardDPDifferentials g) (ambientDPDerivation g)).choose_spec.1 W b

/-- The map on divided power differentials on sections over an open, read in the sheaf of
divided power differentials of the source. -/
public abbrev dpDifferentialsMapApp (g : A ⟶ B) (W : B.thickening.target.scheme.Opens)
    (ω : Γ(objDPDifferentials B, W)) : Γ(objDPDifferentials A, ambientHom g ⁻¹ᵁ W) :=
  (dpDifferentialsMapSheaf g).app W ω

/-- The map on divided power differentials commutes with restriction. -/
public theorem dpDifferentialsMapSheaf_naturality (g : A ⟶ B)
    {W W' : B.thickening.target.scheme.Opens} (i : W' ⟶ W)
    (ω : Γ(objDPDifferentials B, W)) :
    (objDPDifferentials A).presheaf.map ((Opens.map (ambientHom g).base).map i).op
        ((dpDifferentialsMapSheaf g).app W ω) =
      (dpDifferentialsMapSheaf g).app W' ((objDPDifferentials B).presheaf.map i.op ω) :=
  (congrArg
    (fun φ : (objDPDifferentials B).presheaf.obj (op W) ⟶
      (pushforwardDPDifferentials g).presheaf.obj (op W') => ConcreteCategory.hom φ ω)
    ((dpDifferentialsMapSheaf g).mapPresheaf.naturality i.op)).symm

/-! ### The map on the structure sheaves of the first-order thickenings -/

/-- **The map on sections of the structure sheaves of the first-order universal thickenings.**
Over an open `W` of the ambient scheme of the target it is
`(b, ω) ↦ (gh^# b, dg ω)`, which is a ring homomorphism because the differential part is
semilinear over `gh^#` and the ideal of differentials has square zero. -/
public def firstOrderThickeningMapApp (g : A ⟶ B)
    (W : (Opens ↑B.thickening.target.scheme)ᵒᵖ) :
    (firstOrderThickeningPresheaf B.thickening.target S.S.scheme B.toBase.hom).obj W ⟶
      (firstOrderThickeningPresheaf A.thickening.target S.S.scheme A.toBase.hom).obj
        (op (ambientHom g ⁻¹ᵁ W.unop)) :=
  sqZeroExtLift (dpDifferentialsModules A.thickening.target S.S.scheme A.toBase.hom)
    ((sqZeroExtProj
        (dpDifferentialsModules B.thickening.target S.S.scheme B.toBase.hom)).app W ≫
      (ambientHom g).app W.unop)
    (AddMonoidHom.mk' (fun x => (dpDifferentialsMapSheaf g).app W.unop (sqZeroExtSnd x))
      (fun x y => map_add _ (sqZeroExtSnd x) (sqZeroExtSnd y)))
    (fun a b =>
      (map_add _ (sqZeroExtFst a • sqZeroExtSnd b) (sqZeroExtFst b • sqZeroExtSnd a)).trans
        (congrArg₂ (· + ·)
          (Scheme.Modules.Hom.app_smul (dpDifferentialsMapSheaf g)
            (sqZeroExtFst a) (sqZeroExtSnd b))
          (Scheme.Modules.Hom.app_smul (dpDifferentialsMapSheaf g)
            (sqZeroExtFst b) (sqZeroExtSnd a))))

/-- The first component of the map on sections is the map on sections of the ambient
morphism. -/
@[simp]
public theorem firstOrderThickeningMapApp_fst (g : A ⟶ B)
    (W : (Opens ↑B.thickening.target.scheme)ᵒᵖ)
    (x : ↑((firstOrderThickeningPresheaf B.thickening.target S.S.scheme B.toBase.hom).obj W)) :
    sqZeroExtFst ((firstOrderThickeningMapApp g W).hom x) =
      (ambientHom g).app W.unop (sqZeroExtFst x) := rfl

/-- The second component of the map on sections is the map on divided power differentials. -/
@[simp]
public theorem firstOrderThickeningMapApp_snd (g : A ⟶ B)
    (W : (Opens ↑B.thickening.target.scheme)ᵒᵖ)
    (x : ↑((firstOrderThickeningPresheaf B.thickening.target S.S.scheme B.toBase.hom).obj W)) :
    sqZeroExtSnd ((firstOrderThickeningMapApp g W).hom x) =
      (dpDifferentialsMapSheaf g).app W.unop (sqZeroExtSnd x) := rfl

/-- **The map on the structure sheaves of the first-order universal thickenings**, as a morphism
of presheaves of commutative rings over the map of underlying spaces. -/
public def firstOrderThickeningMapPresheaf (g : A ⟶ B) :
    firstOrderThickeningPresheaf B.thickening.target S.S.scheme B.toBase.hom ⟶
      (ambientHom g).base _*
        firstOrderThickeningPresheaf A.thickening.target S.S.scheme A.toBase.hom where
  app W := firstOrderThickeningMapApp g W
  naturality _ _ i := CommRingCat.hom_ext (RingHom.ext fun x => sqZeroExt_ext
    (ambientHom_app_map g i.unop (sqZeroExtFst x)).symm
    (dpDifferentialsMapSheaf_naturality g i.unop (sqZeroExtSnd x)).symm)

/-! ### The morphism of schemes -/

/-- The map of the first-order universal thickenings as a morphism of sheafed spaces: the map of
underlying spaces is that of the ambient morphism and the map on sections is the previous one. -/
public def firstOrderThickeningRawMap (g : A ⟶ B) :
    firstOrderThickeningSheafedSpace A.thickening.target S.S.scheme A.toBase.hom ⟶
      firstOrderThickeningSheafedSpace B.thickening.target S.S.scheme B.toBase.hom :=
  ⟨{ base := (ambientHom g).base, c := firstOrderThickeningMapPresheaf g }⟩

/-- **The map of first-order thickenings composed with the immersion of the source is the ambient
morphism composed with the immersion of the target.**  Both carry a section `(b, ω)` of
`𝒪_{T_B'}` to `gh^# b`. -/
public theorem firstOrderThickeningι_comp_rawMap (g : A ⟶ B) :
    (firstOrderThickeningExtension A.thickening.target S.S.scheme A.toBase.hom).inclusion ≫
        firstOrderThickeningRawMap g =
      (Scheme.Hom.toLRSHom (ambientHom g ≫
        firstOrderThickeningι B.thickening.target S.S.scheme B.toBase.hom)).toShHom := by
  rfl

/-- The map of first-order thickenings induces a local homomorphism on every stalk: composing it
with the immersion of the source recovers a morphism of schemes, so the induced stalk map has a
retraction, and a ring map with a retraction reflects units. -/
public theorem firstOrderThickeningRawMap_isLocalHom (g : A ⟶ B)
    (x : ↑A.thickening.target.scheme) :
    IsLocalHom (((firstOrderThickeningRawMap g).hom.stalkMap x).hom) := by
  have hlocal : IsLocalHom ((((firstOrderThickeningExtension A.thickening.target S.S.scheme
      A.toBase.hom).inclusion.hom ≫ (firstOrderThickeningRawMap g).hom).stalkMap x).hom) :=
    LocallyRingedSpace.isLocalHom_stalkMap_congr _ _ (firstOrderThickeningι_comp_rawMap g).symm x
      (LocallyRingedSpace.isLocalHomStalkMap
        (Scheme.Hom.toLRSHom (ambientHom g ≫
          firstOrderThickeningι B.thickening.target S.S.scheme B.toBase.hom)) x)
  have hstalk : ((((firstOrderThickeningExtension A.thickening.target S.S.scheme
        A.toBase.hom).inclusion.hom ≫ (firstOrderThickeningRawMap g).hom).stalkMap x).hom) =
      (((firstOrderThickeningExtension A.thickening.target S.S.scheme
          A.toBase.hom).inclusion.hom.stalkMap x).hom).comp
        (((firstOrderThickeningRawMap g).hom.stalkMap x).hom) := by
    rw [PresheafedSpace.stalkMap.comp]
    rfl
  have hcomp : IsLocalHom
      ((((firstOrderThickeningExtension A.thickening.target S.S.scheme
          A.toBase.hom).inclusion.hom.stalkMap x).hom).comp
        (((firstOrderThickeningRawMap g).hom.stalkMap x).hom)) := by
    rw [← hstalk]
    exact hlocal
  exact isLocalHom_of_comp (((firstOrderThickeningRawMap g).hom.stalkMap x).hom)
    (((firstOrderThickeningExtension A.thickening.target S.S.scheme
      A.toBase.hom).inclusion.hom.stalkMap x).hom)

/-- **The morphism of schemes `T_A' ⟶ T_B'` between the first-order universal thickenings.** -/
@[stacks 07J2 "the morphism T' ⟶ T₁' of schemes"]
public def firstOrderThickeningSchemeMap (g : A ⟶ B) :
    firstOrderThickeningScheme A.thickening.target S.S.scheme A.toBase.hom ⟶
      firstOrderThickeningScheme B.thickening.target S.S.scheme B.toBase.hom :=
  ⟨LocallyRingedSpace.homMk (firstOrderThickeningRawMap g)
    (firstOrderThickeningRawMap_isLocalHom g)⟩

/-- The morphism of schemes between the first-order thickenings acts on sections by the map of
the previous section. -/
@[simp]
public theorem firstOrderThickeningSchemeMap_c_app (g : A ⟶ B)
    (W : (Opens ↑B.thickening.target.scheme)ᵒᵖ) :
    (firstOrderThickeningSchemeMap g).c.app W = firstOrderThickeningMapApp g W := rfl

/-! ### The divided power scheme morphism -/

/-- **The map on sections of the first-order thickenings is a homomorphism of divided power
rings.**  It carries `J'_B = J_B ⊕ Ω_B` into `J'_A = J_A ⊕ Ω_A` because the ambient morphism does
so on the first summand, and it commutes with `δ'` because the ambient morphism commutes with
`δ` and the map on differentials is semilinear. -/
@[stacks 07J2 "the map T' ⟶ T₁' is compatible with the divided powers δ'"]
public theorem firstOrderThickeningMapApp_isDPMorphism (g : A ⟶ B)
    (U : B.thickening.target.scheme.Opens) :
    DividedPowers.IsDPMorphism
      (firstOrderThickeningDividedPowers B.thickening.target S.S.scheme B.toBase.hom (op U))
      (firstOrderThickeningDividedPowers A.thickening.target S.S.scheme A.toBase.hom
        (op (ambientHom g ⁻¹ᵁ U)))
      (firstOrderThickeningMapApp g (op U)).hom := by
  have hmem : ∀ x ∈ firstOrderThickeningIdeal B.thickening.target S.S.scheme B.toBase.hom (op U),
      (firstOrderThickeningMapApp g (op U)).hom x ∈
        firstOrderThickeningIdeal A.thickening.target S.S.scheme A.toBase.hom
          (op (ambientHom g ⁻¹ᵁ U)) :=
    fun _ hx => mem_ideal_of_isDPMorphism (g.targetHom.compatible U) hx
  refine ⟨Ideal.map_le_iff_le_comap.mpr fun x hx => hmem x hx, ?_⟩
  intro n x hx
  have hb : sqZeroExtFst x ∈ B.thickening.target.ideal.obj (op U) := hx
  match n with
  | 0 =>
      exact (firstOrderThickeningDividedPowers_dpow_zero _ _ _ _ (hmem x hx)).trans
        ((map_one _).symm.trans
          (congrArg (fun z => (firstOrderThickeningMapApp g (op U)).hom z)
            (firstOrderThickeningDividedPowers_dpow_zero _ _ _ _ hx).symm))
  | k + 1 =>
      refine (firstOrderThickeningDividedPowers_dpow_succ _ _ _ _ k (hmem x hx)).trans ?_
      refine Eq.trans ?_ (congrArg (fun z => (firstOrderThickeningMapApp g (op U)).hom z)
        (firstOrderThickeningDividedPowers_dpow_succ _ _ _ _ k hx).symm)
      refine sqZeroExt_ext (g.targetHom.dpow_comp U (sqZeroExtFst x) hb) ?_
      exact (congrArg
          (fun r : Γ(A.thickening.target.scheme, ambientHom g ⁻¹ᵁ U) =>
            r • dpDifferentialsMapApp g U (sqZeroExtSnd x))
          (g.targetHom.dpow_comp U (sqZeroExtFst x) hb)).trans
        (Scheme.Modules.Hom.app_smul (dpDifferentialsMapSheaf g)
          ((B.thickening.target.dividedPowers.dividedPowers (op U)).dpow k (sqZeroExtFst x))
          (sqZeroExtSnd x)).symm

/-- **The morphism of divided power schemes `(T_A', J_A', δ_A') ⟶ (T_B', J_B', δ_B')`** between
the first-order universal thickenings. -/
@[stacks 07J2 "the morphism T' ⟶ T₁' of divided power schemes"]
public def firstOrderThickeningDPMap (g : A ⟶ B) :
    firstOrderThickeningDPScheme S A ⟶ firstOrderThickeningDPScheme S B where
  hom := firstOrderThickeningSchemeMap g
  compatible U := firstOrderThickeningMapApp_isDPMorphism g U

/-! ### The relations of the diagram -/

/-- **The map of first-order thickenings composed with the immersion of the source is the ambient
morphism composed with the immersion of the target**, as morphisms of schemes. -/
public theorem firstOrderThickeningι_comp_schemeMap (g : A ⟶ B) :
    firstOrderThickeningι A.thickening.target S.S.scheme A.toBase.hom ≫
        firstOrderThickeningSchemeMap g =
      ambientHom g ≫ firstOrderThickeningι B.thickening.target S.S.scheme B.toBase.hom := by
  rfl

/-- **The map of first-order thickenings commutes with the first projection**, both sides
carrying `(b, ω)` to `gh^# b`. -/
@[stacks 07J2 "the map T' ⟶ T₁' commutes with p₀, for schemes"]
public theorem firstOrderThickeningSchemeMap_comp_projHom (g : A ⟶ B) :
    firstOrderThickeningSchemeMap g ≫
        firstOrderThickeningProjHom B.thickening.target S.S.scheme B.toBase.hom =
      firstOrderThickeningProjHom A.thickening.target S.S.scheme A.toBase.hom ≫ ambientHom g := by
  refine scheme_hom_ext_of_heq rfl fun W x => ?_
  exact heq_of_eq (sqZeroExt_ext rfl
    (map_zero (ConcreteCategory.hom ((dpDifferentialsMapSheaf g).app W.unop))))

/-- **The map of first-order thickenings commutes with the second projection.**  This is the
computation `dg ∘ d_B = d_A ∘ gh^#`: one side carries `b` to `(gh^# b, dg (d_B b))` and the
other to `(gh^# b, d_A (gh^# b))`. -/
@[stacks 07J2 "the map T' ⟶ T₁' commutes with p₁, for schemes"]
public theorem firstOrderThickeningSchemeMap_comp_P₁Hom (g : A ⟶ B) :
    firstOrderThickeningSchemeMap g ≫
        firstOrderThickeningP₁Hom B.thickening.target S.S.scheme B.toBase.hom =
      firstOrderThickeningP₁Hom A.thickening.target S.S.scheme A.toBase.hom ≫ ambientHom g := by
  refine scheme_hom_ext_of_heq rfl fun W x => ?_
  exact heq_of_eq (sqZeroExt_ext rfl (dpDifferentialsMapSheaf_sheafApp g W.unop x))

/-- **The morphism of `CRIS(X/S)` between the first-order universal thickenings** induced by a
morphism `g` of `CRIS(X/S)`: the functoriality datum of [Stacks, Tag 07J2]. -/
@[stacks 07J2 "the functoriality (U, T, δ) ↦ (U, T', δ') of the first-order thickening"]
public def firstOrderThickeningSiteMap (g : A ⟶ B) :
    firstOrderThickeningObject S A ⟶ firstOrderThickeningObject S B where
  sourceHom := g.sourceHom
  targetHom := firstOrderThickeningDPMap g
  immersion_naturality := by
    change (A.thickening.immersion ≫
        firstOrderThickeningι A.thickening.target S.S.scheme A.toBase.hom) ≫
      firstOrderThickeningSchemeMap g = _
    rw [Category.assoc, firstOrderThickeningι_comp_schemeMap, ← Category.assoc,
      g.immersion_naturality, Category.assoc]
    rfl
  base_naturality := by
    apply DividedPowerScheme.Hom.ext
    change firstOrderThickeningSchemeMap g ≫
        (firstOrderThickeningProjHom B.thickening.target S.S.scheme B.toBase.hom ≫
          B.toBase.hom) =
      firstOrderThickeningProjHom A.thickening.target S.S.scheme A.toBase.hom ≫ A.toBase.hom
    rw [← Category.assoc, firstOrderThickeningSchemeMap_comp_projHom, Category.assoc,
      ambientHom_comp_toBase]
  toX_naturality := g.toX_naturality

/-- **The functoriality datum commutes with the first projection**, the left relation of
[Stacks, Tag 07J2]. -/
@[stacks 07J2 "the functoriality datum commutes with p₀, in CRIS(X/S)"]
public theorem firstOrderThickeningSiteMap_comp_P₀ (g : A ⟶ B) :
    firstOrderThickeningSiteMap g ≫ firstOrderThickeningSiteP₀ S B =
      firstOrderThickeningSiteP₀ S A ≫ g :=
  Thickening.Hom.ext ((Category.comp_id _).trans (Category.id_comp _).symm)
    (DividedPowerScheme.Hom.ext (firstOrderThickeningSchemeMap_comp_projHom g))

/-- **The functoriality datum commutes with the second projection**, the right relation of
[Stacks, Tag 07J2]. -/
@[stacks 07J2 "the functoriality datum commutes with p₁, in CRIS(X/S)"]
public theorem firstOrderThickeningSiteMap_comp_P₁ (g : A ⟶ B) :
    firstOrderThickeningSiteMap g ≫ firstOrderThickeningSiteP₁ S B =
      firstOrderThickeningSiteP₁ S A ≫ g :=
  Thickening.Hom.ext ((Category.comp_id _).trans (Category.id_comp _).symm)
    (DividedPowerScheme.Hom.ext (firstOrderThickeningSchemeMap_comp_P₁Hom g))

/-! ### Functoriality -/

/-- The map on divided power differentials induced by the identity is the identity. -/
public theorem dpDifferentialsMapSheaf_id (A : Thickening S) :
    dpDifferentialsMapSheaf (𝟙 A) = 𝟙 (objDPDifferentials A) :=
  (universalDPSchemeDerivation_isUniversal A.thickening.target S.S.scheme A.toBase.hom
    (pushforwardDPDifferentials (𝟙 A)) (ambientDPDerivation (𝟙 A))).unique
      (fun W b => dpDifferentialsMapSheaf_sheafApp (𝟙 A) W b) (fun _ _ => rfl)

/-- **The functoriality datum of the identity is the identity.** -/
public theorem firstOrderThickeningSiteMap_id (A : Thickening S) :
    firstOrderThickeningSiteMap (𝟙 A) = 𝟙 (firstOrderThickeningObject S A) := by
  apply Thickening.Hom.ext
  · rfl
  · apply DividedPowerScheme.Hom.ext
    refine scheme_hom_ext_of_heq rfl fun W x => heq_of_eq (sqZeroExt_ext rfl ?_)
    change (dpDifferentialsMapSheaf (𝟙 A)).app W.unop (sqZeroExtSnd x) = _
    rw [dpDifferentialsMapSheaf_id]
    rfl

/-- The map on divided power differentials induced by a composite is the composite of the maps,
the second one pushed forward along the ambient morphism of the first. -/
public theorem dpDifferentialsMapSheaf_comp {C : Thickening S} (g : A ⟶ B) (h : B ⟶ C) :
    dpDifferentialsMapSheaf (g ≫ h) =
      dpDifferentialsMapSheaf h ≫
        (Scheme.Modules.pushforward (ambientHom h)).map (dpDifferentialsMapSheaf g) :=
  (universalDPSchemeDerivation_isUniversal C.thickening.target S.S.scheme C.toBase.hom
    (pushforwardDPDifferentials (g ≫ h)) (ambientDPDerivation (g ≫ h))).unique
      (fun W b => dpDifferentialsMapSheaf_sheafApp (g ≫ h) W b)
      (fun W b =>
        (congrArg (fun z => dpDifferentialsMapApp g (ambientHom h ⁻¹ᵁ W) z)
            (dpDifferentialsMapSheaf_sheafApp h W b)).trans
          (dpDifferentialsMapSheaf_sheafApp g (ambientHom h ⁻¹ᵁ W)
            ((ambientHom h).app W b)))

/-- **The functoriality datum of a composite is the composite of the functoriality data.** -/
public theorem firstOrderThickeningSiteMap_comp {C : Thickening S} (g : A ⟶ B) (h : B ⟶ C) :
    firstOrderThickeningSiteMap (g ≫ h) =
      firstOrderThickeningSiteMap g ≫ firstOrderThickeningSiteMap h := by
  apply Thickening.Hom.ext
  · rfl
  · apply DividedPowerScheme.Hom.ext
    refine scheme_hom_ext_of_heq rfl fun W x => heq_of_eq (sqZeroExt_ext rfl ?_)
    change (dpDifferentialsMapSheaf (g ≫ h)).app W.unop (sqZeroExtSnd x) = _
    rw [dpDifferentialsMapSheaf_comp]
    rfl

end GlobalCrystallineSituation

end Crystalline

end
