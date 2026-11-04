module

public import StacksFrontier.AlgebraicGeometry.Modules.DerivedPullbackOpensHomGlueing
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentDerivedHom
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.BBDGlueing
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.LocallyGivenOfGlobalObject
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.TwoOpenGlueingObjectTransport

/-!
# Glueing objects along derived pullbacks to opens (the BBD glueing lemma)

Let `X` be a scheme and `ℬ` a collection of opens covering `X` such that the intersection of two
members is the union of the members it contains. Suppose given objects `K_U` of `D(𝒪_U)` for
`U ∈ ℬ` with `Ext^n(K_U, K_U) = 0` for `n < 0`, and isomorphisms `ρ_{VU} : K_U|_V ≅ K_V` for
`V ≤ U` in `ℬ` satisfying the cocycle condition, where `K_U|_V` is the derived pullback along the
inclusion `V ⟶ U`. Then there is an object `L` of `D(𝒪_X)` with isomorphisms
`σ_U : L|_U ≅ K_U` compatible with the `ρ_{VU}`, and `(L, σ)` is unique up to unique isomorphism
(Stacks 0D6C). Restriction from `X` to `U` is derived pullback along `U ⟶ X`, and the two ways
of restricting to `V` are compared by `resComp` of Stacks 0D5S, as in
`StacksFrontier/AlgebraicGeometry/Modules/DerivedPullbackOpensHomGlueing.lean`.

## Main definitions

* `AlgebraicGeometry.Scheme.DerivedPullbackOpensGlueing.pullbackLEComp`: the composition
  comparison `(W ⟶ V)^*(V ⟶ U)^* M ≅ (W ⟶ U)^* M` through which the cocycle condition is read.
* `AlgebraicGeometry.Scheme.DerivedPullbackOpensGlueing.openResIso`: the restriction of the
  model of Situation 0D67 from `U` to `V`, identified with derived pullback along `V ⟶ U`.
* `AlgebraicGeometry.Scheme.DerivedPullbackOpensGlueing.locallyGiven`: the system of locally
  given derived objects of Situation 0D67 attached to `(K, ρ)`.

## Main results

* `AlgebraicGeometry.Scheme.DerivedPullbackOpensGlueing.openResIso_coherence`: `openResIso` is
  compatible with the comparisons of restriction in two steps of the two models.
* `AlgebraicGeometry.Scheme.DerivedPullbackOpensGlueing.exists_glueing_of_derivedPullback_opens`:
  existence of the glued object (Stacks 0D6C).
* `AlgebraicGeometry.Scheme.DerivedPullbackOpensGlueing.existsUnique_iso_of_derivedPullback_opens`:
  its uniqueness up to unique isomorphism.

## Implementation notes

The statement is transported to the model of Situation 0D67 on the underlying ringed space, where
it is `Stacks.DerivedGlueing.exists_solution_and_unique_solutionIso_of_covers_unconditional`.
There, restriction from `U` to `V` is extension by zero followed by restriction of complexes,
`Stacks.DerivedGlueing.openModuleRestriction`, so what has to be checked is that it is derived
pullback along `V ⟶ U`, compatibly with the comparisons of restriction in two steps.

Restriction from the open subspace `⊤` to `U` is a localization functor: up to the equivalence
of extension by zero along `⊤`, it is restriction to `U`, whose left adjoint, extension by zero,
is fully faithful (`openResTop_isLocalization`). The identification `openResIso` is therefore
defined by descending, along restriction from `⊤`, the composite of the comparisons already at
hand (`openResIsoTop`), and its compatibility with restriction in two steps is checked on objects
restricted from `⊤`, where it is the associativity of the comparisons of either model:
`Stacks.DerivedGlueing.LocallyGiven.restrictionComp_pentagon` and
`Stacks.DerivedPullback.factorIso_assoc`. The comparison maps of the two models never have to be
compared directly.

The derived categories of the opens are spelled in two ways, as
`Stacks.DerivedGlueing.OpenDerivedCategory` and as derived categories of modules on the open
subschemes; the two agree only after unfolding, so the diagram chases are stated with every
object and every morphism a variable (`coherence_chase`, `cocycle_chase`, `compat_chase`) and
applied as terms.

## References

* [Stacks Project, Tag 0D6C](https://stacks.math.columbia.edu/tag/0D6C)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open ExtensionByZeroModules Stacks.DerivedGlueing

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme.DerivedPullbackOpensGlueing

/-! ### Diagram chases -/

section Chases

/-- The diagram chase behind `openResIso_coherence_top`, with every object and every morphism a
variable. -/
theorem coherence_chase {𝒱 𝒲 : Type*} [Category* 𝒱] [Category* 𝒲] (R P : 𝒱 ⥤ 𝒲)
    {a b c e f : 𝒱} {o1 oR oI o8 o10 : 𝒲}
    (rcV : a ≅ b) (κV βVU : b ⟶ c) (dV : a ≅ e) (rCV : f ≅ e) (mU : f ≅ c)
    (K1 : κV = rcV.inv ≫ dV.hom ≫ rCV.inv ≫ 𝟙 f ≫ mU.hom) (H1 : βVU = κV)
    (rcWVU : o1 ⟶ R.obj b) (βWVc : R.obj c ⟶ P.obj c) (βWU κWU : o1 ⟶ o10)
    (lcR : P.obj c ≅ o10) (rcWU : oR ≅ o1) (dW : oR ≅ oI) (rCWU : o8 ≅ oI) (nU : o8 ⟶ o10)
    (H2 : βWU = κWU) (K2 : κWU = rcWU.inv ≫ dW.hom ≫ rCWU.inv ≫ 𝟙 o8 ≫ nU)
    (βWVa κWV : R.obj a ⟶ P.obj a)
    (H4 : R.map (rcV.hom ≫ κV) ≫ βWVc = βWVa ≫ P.map (rcV.hom ≫ κV))
    (H3 : βWVa = κWV) (rcWV : oR ≅ R.obj a) (rCWV : P.obj e ≅ oI)
    (K3 : κWV = rcWV.inv ≫ dW.hom ≫ rCWV.inv ≫ 𝟙 (P.obj e) ≫ P.map dV.inv)
    (hrc : rcWU.hom ≫ rcWVU = rcWV.hom ≫ R.map rcV.hom)
    (lcI : P.obj f ≅ o8) (hpb : lcI.hom ≫ rCWU.hom = P.map rCV.hom ≫ rCWV.hom)
    (hnat : nU ≫ lcR.inv = lcI.inv ≫ P.map mU.hom) :
    rcWVU ≫ R.map βVU ≫ βWVc = βWU ≫ lcR.inv := by
  subst H1 H2 H3 K1 K2 K3
  let T : a ≅ c := dV ≪≫ rCV.symm ≪≫ mU
  have hT : rcV.hom ≫ rcV.inv ≫ dV.hom ≫ rCV.inv ≫ 𝟙 f ≫ mU.hom = T.hom := by simp [T]
  rw [hT] at H4
  have hc : βWVc = R.map T.inv ≫
      (rcWV.inv ≫ dW.hom ≫ rCWV.inv ≫ 𝟙 (P.obj e) ≫ P.map dV.inv) ≫ P.map T.hom :=
    (Iso.eq_inv_comp (R.mapIso T)).mpr H4
  have hrc' : rcWVU = rcWU.inv ≫ rcWV.hom ≫ R.map rcV.hom := by
    rw [← hrc, Iso.inv_hom_id_assoc]
  have hpb' : rCWV.inv ≫ P.map rCV.inv = rCWU.inv ≫ lcI.inv := by
    have := congrArg (fun t => rCWV.inv ≫ P.map rCV.inv ≫ t ≫ rCWU.inv ≫ lcI.inv) hpb
    simpa using this
  rw [hc, hrc']
  simp [T, hnat, reassoc_of% hpb']

/-- The diagram chase behind the cocycle condition of `locallyGiven`. -/
theorem cocycle_chase {𝒱 𝒲 : Type*} [Category* 𝒱] [Category* 𝒲] (R P : 𝒱 ⥤ 𝒲)
    {b p q : 𝒱} {o1 o3 kw : 𝒲} (βVU : b ⟶ p) (ρVU : p ⟶ q) (rcK : o1 ⟶ R.obj b)
    (βWVp : R.obj p ⟶ P.obj p) (βWVq : R.obj q ⟶ P.obj q) (βWU : o1 ⟶ o3) (lc : P.obj p ≅ o3)
    (ρWU : o3 ⟶ kw) (ρWV : P.obj q ⟶ kw)
    (hcoh : rcK ≫ R.map βVU ≫ βWVp = βWU ≫ lc.inv)
    (hnat : R.map ρVU ≫ βWVq = βWVp ≫ P.map ρVU)
    (hρ : ρWU = lc.inv ≫ P.map ρVU ≫ ρWV) :
    βWU ≫ ρWU = rcK ≫ R.map (βVU ≫ ρVU) ≫ (βWVq ≫ ρWV) := by
  rw [Functor.map_comp, Category.assoc, reassoc_of% hnat, reassoc_of% hcoh, hρ]

/-- The diagram chase behind the compatibility clause of
`exists_glueing_of_derivedPullback_opens`. -/
theorem compat_chase {𝒰 𝒱 : Type*} [Category* 𝒰] [Category* 𝒱] (R P : 𝒰 ⥤ 𝒱)
    {ru ku iu : 𝒰} {rv iv kv : 𝒱} (dUinv : iu ⟶ ru) (ArhoU : ru ⟶ ku) (rcA : rv ≅ R.obj ru)
    (βKU : R.obj ku ⟶ P.obj ku) (βRU κ : R.obj ru ⟶ P.obj ru) (dV : rv ≅ iv)
    (rC : P.obj iu ≅ iv) (ρ : P.obj ku ⟶ kv) (ArhoV : rv ⟶ kv)
    (hcomp : rcA.hom ≫ R.map ArhoU ≫ (βKU ≫ ρ) = ArhoV)
    (hnat : R.map ArhoU ≫ βKU = βRU ≫ P.map ArhoU) (hb : βRU = κ)
    (hκ : κ = rcA.inv ≫ dV.hom ≫ rC.inv ≫ 𝟙 _ ≫ P.map dUinv) :
    rC.inv ≫ P.map (dUinv ≫ ArhoU) ≫ ρ = dV.inv ≫ ArhoV := by
  subst hb hκ hcomp
  rw [reassoc_of% hnat]
  simp

/-- A composite of two morphisms whose images are conjugates of identities. -/
theorem map_comp_conj {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (F : 𝒞 ⥤ 𝒟) {x y z : 𝒞}
    {k : 𝒟} (a : x ⟶ y) (b : y ⟶ z) (s : F.obj x ≅ k) (t : F.obj y ≅ k) (r : F.obj z ≅ k)
    (ha : F.map a = s.hom ≫ t.inv) (hb : F.map b = t.hom ≫ r.inv) :
    F.map (a ≫ b) = s.hom ≫ r.inv := by
  rw [F.map_comp, ha, hb]
  simp

/-- The image of an identity is a conjugate of the identity. -/
theorem map_id_conj {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (F : 𝒞 ⥤ 𝒟) (x : 𝒞) {k : 𝒟}
    (s : F.obj x ≅ k) : F.map (𝟙 x) = s.hom ≫ s.inv := by
  simp

/-- Two families of identifications compatible with the same transition isomorphism differ by a
family of morphisms compatible with restriction. -/
theorem conj_compat {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (P : 𝒞 ⥤ 𝒟)
    {mU mU' kU : 𝒞} {mV mV' kV : 𝒟} (rM : P.obj mU ≅ mV) (rM' : P.obj mU' ≅ mV')
    (τU : mU ≅ kU) (τU' : mU' ≅ kU) (τV : mV ≅ kV) (τV' : mV' ≅ kV) (ρ : P.obj kU ≅ kV)
    (h : rM.inv ≫ P.map τU.hom ≫ ρ.hom = τV.hom)
    (h' : rM'.inv ≫ P.map τU'.hom ≫ ρ.hom = τV'.hom) :
    rM.inv ≫ P.map (τU.hom ≫ τU'.inv) ≫ rM'.hom = τV.hom ≫ τV'.inv := by
  have h'' : τV'.inv = ρ.inv ≫ P.map τU'.inv ≫ rM'.hom := by
    rw [← cancel_epi τV'.hom, Iso.hom_inv_id, ← h']
    simp
  rw [← h, h'']
  simp

end Chases

variable {X : Scheme.{u}}

/-! ### The comparison of derived pullbacks along two inclusions of opens -/

/-- The composition comparison of Stacks 0D5S read through an equality of composites is the
comparison attached to the factorization. -/
theorem derivedPullbackCompObj_trans_congrObj {Y Z T : Scheme.{u}} (a : Y ⟶ Z) (b : Z ⟶ T)
    (c : Y ⟶ T) (h : a ≫ b = c) (K : DerivedCategory T.Modules) :
    Scheme.derivedPullbackCompObj a b K ≪≫ Scheme.derivedPullbackCongrObj h K =
      (Stacks.DerivedPullback.schemeFactorIso a b c h).app K := by
  subst h
  exact Iso.ext (Category.comp_id _)

variable {U V W : X.Opens}

/-- **Restricting from `U` to `V` and then to `W` is restricting from `U` to `W`**: the composite
of the derived pullbacks along `W ⟶ V` and `V ⟶ U` is the derived pullback along `W ⟶ U`. -/
def pullbackLEComp (hWV : W ≤ V) (hVU : V ≤ U) (M : DerivedCategory U.toScheme.Modules) :
    (pullbackLE hWV).obj ((pullbackLE hVU).obj M) ≅ (pullbackLE (hWV.trans hVU)).obj M :=
  Scheme.derivedPullbackCompObj (X.homOfLE hWV) (X.homOfLE hVU) M ≪≫
    Scheme.derivedPullbackCongrObj (X.homOfLE_homOfLE hWV hVU) M

/-- The comparisons `pullbackLEComp` and `resComp` are associative. -/
theorem pullbackLEComp_hom_resComp_hom (hWV : W ≤ V) (hVU : V ≤ U)
    (N : DerivedCategory X.Modules) :
    (pullbackLEComp hWV hVU ((derivedPullback U.ι.toLRSHom.toShHom).obj N)).hom ≫
        (resComp (hWV.trans hVU) N).hom =
      (pullbackLE hWV).map (resComp hVU N).hom ≫ (resComp hWV N).hom := by
  have h := Stacks.DerivedPullback.factorIso_assoc (X.homOfLE hWV).toLRSHom.toShHom
    (X.homOfLE hVU).toLRSHom.toShHom U.ι.toLRSHom.toShHom V.ι.toLRSHom.toShHom
    (X.homOfLE (hWV.trans hVU)).toLRSHom.toShHom W.ι.toLRSHom.toShHom
    (congrArg (fun m : V.toScheme ⟶ X ↦ m.toLRSHom.toShHom) (X.homOfLE_ι hVU))
    (congrArg (fun m : W.toScheme ⟶ U.toScheme ↦ m.toLRSHom.toShHom)
      (X.homOfLE_homOfLE hWV hVU))
    (congrArg (fun m : W.toScheme ⟶ X ↦ m.toLRSHom.toShHom) (X.homOfLE_ι (hWV.trans hVU)))
    (congrArg (fun m : W.toScheme ⟶ X ↦ m.toLRSHom.toShHom) (X.homOfLE_ι hWV)) N
  have e₁ := congrArg Iso.hom (derivedPullbackCompObj_trans_congrObj _ _ _
    (X.homOfLE_homOfLE hWV hVU) ((derivedPullback U.ι.toLRSHom.toShHom).obj N))
  have e₂ := congrArg Iso.hom
    (derivedPullbackCompObj_trans_congrObj _ _ _ (X.homOfLE_ι (hWV.trans hVU)) N)
  have e₃ := congrArg Iso.hom (derivedPullbackCompObj_trans_congrObj _ _ _ (X.homOfLE_ι hVU) N)
  have e₄ := congrArg Iso.hom (derivedPullbackCompObj_trans_congrObj _ _ _ (X.homOfLE_ι hWV) N)
  exact (congrArg₂ (· ≫ ·) e₁ e₂).trans ((congrArg Iso.hom h).trans
    (congrArg₂ (· ≫ ·) (congrArg (pullbackLE hWV).map e₃) e₄).symm)

/-- `pullbackLEComp` is natural in the object. -/
theorem pullbackLEComp_inv_naturality (hWV : W ≤ V) (hVU : V ≤ U)
    {M M' : DerivedCategory U.toScheme.Modules} (x : M ⟶ M') :
    (pullbackLE (hWV.trans hVU)).map x ≫ (pullbackLEComp hWV hVU M').inv =
      (pullbackLEComp hWV hVU M).inv ≫ (pullbackLE hWV).map ((pullbackLE hVU).map x) := by
  have e := fun M => congrArg Iso.inv (derivedPullbackCompObj_trans_congrObj _ _ _
    (X.homOfLE_homOfLE hWV hVU) M)
  rw [show (pullbackLEComp hWV hVU M').inv = _ from e M',
    show (pullbackLEComp hWV hVU M).inv = _ from e M]
  exact (Stacks.DerivedPullback.schemeFactorIso _ _ _
    (X.homOfLE_homOfLE hWV hVU)).inv.naturality x

/-! ### The model of Situation 0D67 -/

variable (X) in
/-- Extension by zero along the open subspace `⊤`, from the derived category of the open
subscheme `⊤` to `D(𝒪_X)`; an equivalence (`Stacks.DerivedGlueing.topExtensionDerivedEquivalence`).
-/
def topExtension :
    DerivedCategory (⊤ : X.Opens).toScheme.Modules ⥤ DerivedCategory X.Modules :=
  (jShriek (⊤ : X.Opens) (underlyingRingSheaf X.toRingedSpace)).mapDerivedCategory

/-- Restriction from `U` to `V` in the model of Situation 0D67: extension by zero followed by
restriction of complexes. -/
def openRes (hVU : V ≤ U) :
    DerivedCategory U.toScheme.Modules ⥤ DerivedCategory V.toScheme.Modules :=
  (restrictionDatum X.toRingedSpace).restriction V U hVU

/-- The comparison of restriction in two steps with direct restriction, in the model of
Situation 0D67. -/
def openResComp (W V U : X.Opens) (hWV : W ≤ V) (hVU : V ≤ U) :
    openRes (hWV.trans hVU) ≅ openRes hVU ⋙ openRes hWV :=
  (restrictionDatum X.toRingedSpace).restrictionComp W V U hWV hVU

/-- The comparisons `openResComp` are associative. -/
theorem openResComp_pentagon (W T O U : X.Opens) (hWT : W ≤ T) (hTO : T ≤ O) (hOU : O ≤ U)
    (K : DerivedCategory U.toScheme.Modules) :
    (openResComp W O U (hWT.trans hTO) hOU).hom.app K ≫
        (openResComp W T O hWT hTO).hom.app ((openRes hOU).obj K) =
      (openResComp W T U hWT (hTO.trans hOU)).hom.app K ≫
        (openRes hWT).map ((openResComp T O U hTO hOU).hom.app K) :=
  (restrictionDatum X.toRingedSpace).restrictionComp_pentagon W T O U hWT hTO hOU K

/-- Restriction from `⊤` to `U` in the model of Situation 0D67 is extension by zero along `⊤`
followed by restriction to `U`. -/
def openResTopIsoJStar (U : X.Opens) : openRes (le_top : U ≤ ⊤) ≅ topExtension X ⋙ jStarDerived U :=
  (mapDerivedCategoryCongr (eqToIso (openModuleRestriction_top_eq U))).symm ≪≫
    (mapDerivedCategoryCompIso (jShriek (⊤ : X.Opens) (underlyingRingSheaf X.toRingedSpace))
      (SheafOfModules.overFunctor.{u} (underlyingRingSheaf X.toRingedSpace) U ⋙
        sliceToSubspace (underlyingRingSheaf X.toRingedSpace) U)).symm

/-- Restriction from `⊤` to `U` in the model of Situation 0D67 is extension by zero along `⊤`
followed by derived pullback along `U ⟶ X`. -/
def openResTopIso (U : X.Opens) :
    openRes (le_top : U ≤ ⊤) ≅ topExtension X ⋙ derivedPullback U.ι.toLRSHom.toShHom :=
  openResTopIsoJStar U ≪≫ Functor.isoWhiskerLeft (topExtension X) (jStarDerivedIso U ≪≫ sliceIso U)

/-- The morphism property at which restriction from `⊤` to `U` is a localization. -/
abbrev openResTopW (U : X.Opens) :
    MorphismProperty (DerivedCategory (⊤ : X.Opens).toScheme.Modules) :=
  (MorphismProperty.isomorphisms _).inverseImage (topExtension X ⋙ jStarDerived U)

/-- **Restriction from `⊤` to `U` is a localization functor**: up to the equivalence of
extension by zero along `⊤`, it is restriction to `U`, whose left adjoint, extension by zero, is
fully faithful. -/
theorem openResTop_isLocalization (U : X.Opens) :
    (openRes (le_top : U ≤ ⊤)).IsLocalization (openResTopW U) := by
  have hff := (fullyFaithful_jShriek_mapDerivedCategory
    (structureSheafRing X.toRingedSpace) U).comp
      (topExtensionDerivedEquivalence (X := X.toRingedSpace)).symm.fullyFaithfulFunctor
  have := hff.full
  have := hff.faithful
  have adj := (Adjunction.mapDerivedCategory
    (jShriekAdjunction U (structureSheafRing X.toRingedSpace))).comp
      (topExtensionDerivedEquivalence (X := X.toRingedSpace)).symm.toAdjunction
  have h : (topExtension X ⋙ jStarDerived U).IsLocalization (openResTopW U) :=
    adj.isLocalization'
  exact @Functor.IsLocalization.of_iso _ _ _ _ (openResTopW U) _ _ (openResTopIsoJStar U).symm h

/-! ### Restriction in the model of Situation 0D67 is derived pullback -/

/-- The identification of the two readings of restriction from `U` to `V`, on objects restricted
from `⊤`: through restriction from `⊤` to `V` in both models. -/
def openResIsoTop (hVU : V ≤ U) :
    openRes (le_top : U ≤ ⊤) ⋙ openRes hVU ≅ openRes (le_top : U ≤ ⊤) ⋙ pullbackLE hVU :=
  (openResComp V U ⊤ hVU le_top).symm ≪≫ openResTopIso V ≪≫
    Functor.isoWhiskerLeft (topExtension X) (resCompIso hVU).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (openResTopIso U).symm (pullbackLE hVU)

/-- `openResIsoTop` at an object. -/
theorem openResIsoTop_hom_app (hVU : V ≤ U) (A : DerivedCategory (⊤ : X.Opens).toScheme.Modules) :
    (openResIsoTop hVU).hom.app A =
      (openResComp V U ⊤ hVU le_top).inv.app A ≫ (openResTopIso V).hom.app A ≫
        (resComp hVU ((topExtension X).obj A)).inv ≫ 𝟙 _ ≫
          (pullbackLE hVU).map ((openResTopIso U).inv.app A) :=
  rfl

/-- **Restriction from `U` to `V` in the model of Situation 0D67 is derived pullback along
`V ⟶ U`.** It is `openResIsoTop`, descended along the localization functor of restriction from
`⊤` to `U`. -/
def openResIso (hVU : V ≤ U) : openRes hVU ≅ pullbackLE hVU :=
  haveI := openResTop_isLocalization U
  Localization.liftNatIso (openRes (le_top : U ≤ ⊤)) (openResTopW U) _ _ _ _
    (h₁ := Localization.Lifting.compLeft _ _ _) (h₂ := Localization.Lifting.compLeft _ _ _)
    (openResIsoTop hVU)

/-- `openResIso` at an object restricted from `⊤` is `openResIsoTop`. -/
theorem openResIso_hom_app (hVU : V ≤ U) (A : DerivedCategory (⊤ : X.Opens).toScheme.Modules) :
    (openResIso hVU).hom.app ((openRes (le_top : U ≤ ⊤)).obj A) =
      (openResIsoTop hVU).hom.app A := by
  have := openResTop_isLocalization U
  exact (@Localization.liftNatTrans_app _ _ _ _ (openRes (le_top : U ≤ ⊤)) (openResTopW U) _ _ _
    _ _ (openRes hVU) (pullbackLE hVU)
    (Localization.Lifting.compLeft _ _ _) (Localization.Lifting.compLeft _ _ _)
    (openResIsoTop hVU).hom A).trans ((Category.id_comp _).trans (Category.comp_id _))

/-- `openResIso_coherence` on objects restricted from `⊤`. -/
theorem openResIso_coherence_top (hWV : W ≤ V) (hVU : V ≤ U)
    (A : DerivedCategory (⊤ : X.Opens).toScheme.Modules) :
    (openResComp W V U hWV hVU).hom.app ((openRes (le_top : U ≤ ⊤)).obj A) ≫
        (openRes hWV).map ((openResIso hVU).hom.app ((openRes (le_top : U ≤ ⊤)).obj A)) ≫
        (openResIso hWV).hom.app ((pullbackLE hVU).obj ((openRes (le_top : U ≤ ⊤)).obj A)) =
      (openResIso (hWV.trans hVU)).hom.app ((openRes (le_top : U ≤ ⊤)).obj A) ≫
        (pullbackLEComp hWV hVU ((openRes (le_top : U ≤ ⊤)).obj A)).inv :=
  coherence_chase (openRes hWV) (pullbackLE hWV)
    ((openResComp V U ⊤ hVU le_top).app A) ((openResIsoTop hVU).hom.app A)
    ((openResIso hVU).hom.app ((openRes (le_top : U ≤ ⊤)).obj A))
    ((openResTopIso V).app A) (resComp hVU ((topExtension X).obj A))
    ((pullbackLE hVU).mapIso ((openResTopIso U).app A).symm)
    (openResIsoTop_hom_app hVU A) (openResIso_hom_app hVU A)
    ((openResComp W V U hWV hVU).hom.app ((openRes (le_top : U ≤ ⊤)).obj A))
    ((openResIso hWV).hom.app ((pullbackLE hVU).obj ((openRes (le_top : U ≤ ⊤)).obj A)))
    ((openResIso (hWV.trans hVU)).hom.app ((openRes (le_top : U ≤ ⊤)).obj A))
    ((openResIsoTop (hWV.trans hVU)).hom.app A)
    (pullbackLEComp hWV hVU ((openRes (le_top : U ≤ ⊤)).obj A))
    ((openResComp W U ⊤ (hWV.trans hVU) le_top).app A) ((openResTopIso W).app A)
    (resComp (hWV.trans hVU) ((topExtension X).obj A))
    ((pullbackLE (hWV.trans hVU)).map ((openResTopIso U).inv.app A))
    (openResIso_hom_app (hWV.trans hVU) A) (openResIsoTop_hom_app (hWV.trans hVU) A)
    ((openResIso hWV).hom.app ((openRes (le_top : V ≤ ⊤)).obj A))
    ((openResIsoTop hWV).hom.app A)
    ((openResIso hWV).hom.naturality _) (openResIso_hom_app hWV A)
    ((openResComp W V ⊤ hWV le_top).app A) (resComp hWV ((topExtension X).obj A))
    (openResIsoTop_hom_app hWV A)
    (openResComp_pentagon W V U ⊤ hWV hVU le_top A)
    (pullbackLEComp hWV hVU ((derivedPullback U.ι.toLRSHom.toShHom).obj ((topExtension X).obj A)))
    (pullbackLEComp_hom_resComp_hom hWV hVU ((topExtension X).obj A))
    (pullbackLEComp_inv_naturality hWV hVU ((openResTopIso U).inv.app A))

/-- **The identification `openResIso` is compatible with restriction in two steps**: through it,
the comparison `openResComp` of the model of Situation 0D67 is the comparison `pullbackLEComp` of
derived pullbacks. -/
theorem openResIso_coherence (hWV : W ≤ V) (hVU : V ≤ U) (M : DerivedCategory U.toScheme.Modules) :
    (openResComp W V U hWV hVU).hom.app M ≫ (openRes hWV).map ((openResIso hVU).hom.app M) ≫
        (openResIso hWV).hom.app ((pullbackLE hVU).obj M) =
      (openResIso (hWV.trans hVU)).hom.app M ≫ (pullbackLEComp hWV hVU M).inv := by
  have := openResTop_isLocalization U
  have e : ∀ M, (pullbackLEComp hWV hVU M).inv = (Stacks.DerivedPullback.schemeFactorIso _ _ _
      (X.homOfLE_homOfLE hWV hVU)).inv.app M := fun M =>
    congrArg Iso.inv (derivedPullbackCompObj_trans_congrObj _ _ _ (X.homOfLE_homOfLE hWV hVU) M)
  have h := Localization.natTrans_ext (openRes (le_top : U ≤ ⊤)) (openResTopW U)
    (τ := (openResComp W V U hWV hVU).hom ≫
      Functor.whiskerRight (openResIso hVU).hom (openRes hWV) ≫
      Functor.whiskerLeft (pullbackLE hVU) (openResIso hWV).hom)
    (τ' := (openResIso (hWV.trans hVU)).hom ≫ (Stacks.DerivedPullback.schemeFactorIso _ _ _
      (X.homOfLE_homOfLE hWV hVU)).inv)
    (fun A => (openResIso_coherence_top hWV hVU A).trans
      (congrArg (_ ≫ ·) (e ((openRes (le_top : U ≤ ⊤)).obj A))))
  exact (congr_app h M).trans (congrArg (_ ≫ ·) (e M).symm)

/-! ### The glueing -/

section Glueing

variable (B : Set X.Opens) (K : ∀ U ∈ B, DerivedCategory U.toScheme.Modules)
  (ρ : ∀ (V U : X.Opens) (hVU : V ≤ U) (hU : U ∈ B) (hV : V ∈ B),
    (pullbackLE hVU).obj (K U hU) ≅ K V hV)

/-- **The system of locally given derived objects attached to `(K, ρ)`** (Situation 0D67): the
objects `K_U`, with the transition isomorphisms `ρ_{VU}` read through `openResIso`. -/
def locallyGiven
    (hρ : ∀ (W V U : X.Opens) (hWV : W ≤ V) (hVU : V ≤ U) (hU : U ∈ B) (hV : V ∈ B)
      (hW : W ∈ B), (ρ W U (hWV.trans hVU) hU hW).hom =
        (pullbackLEComp hWV hVU (K U hU)).inv ≫ (pullbackLE hWV).map (ρ V U hVU hU hV).hom ≫
          (ρ W V hWV hV hW).hom) :
    LocallyGiven X.toRingedSpace :=
  { restrictionDatum X.toRingedSpace with
    opens := B
    obj := K
    rho := fun V U hVU hU hV => (openResIso hVU).app (K U hU) ≪≫ ρ V U hVU hU hV
    cocycle := fun W V U hWV hVU hU hV hW =>
      cocycle_chase (openRes hWV) (pullbackLE hWV) ((openResIso hVU).hom.app (K U hU))
        (ρ V U hVU hU hV).hom ((openResComp W V U hWV hVU).hom.app (K U hU))
        ((openResIso hWV).hom.app ((pullbackLE hVU).obj (K U hU)))
        ((openResIso hWV).hom.app (K V hV)) ((openResIso (hWV.trans hVU)).hom.app (K U hU))
        (pullbackLEComp hWV hVU (K U hU)) (ρ W U (hWV.trans hVU) hU hW).hom
        (ρ W V hWV hV hW).hom (openResIso_coherence hWV hVU (K U hU))
        ((openResIso hWV).hom.naturality _) (hρ W V U hWV hVU hU hV hW) }

/-- **The BBD glueing lemma for schemes, existence** (Stacks 0D6C). Let `ℬ` be a collection of
opens of a scheme `X` covering `X`, such that the intersection of two members is the union of the
members it contains. Let `K_U ∈ D(𝒪_U)` for `U ∈ ℬ`, with `Ext^n(K_U, K_U) = 0` for `n < 0`, and
let `ρ_{VU} : K_U|_V ≅ K_V` for `V ≤ U` in `ℬ` satisfy the cocycle condition, restriction being
derived pullback along `V ⟶ U`. Then there are `L ∈ D(𝒪_X)` and isomorphisms `σ_U : L|_U ≅ K_U`
with `ρ_{VU} ∘ σ_U|_V = σ_V`, restriction from `X` being derived pullback along `U ⟶ X` and
`σ_U|_V` being read through `resComp`. -/
theorem exists_glueing_of_derivedPullback_opens (hcover : sSup B = ⊤)
    (hinter : ∀ U ∈ B, ∀ V ∈ B, U ⊓ V = sSup {W | W ∈ B ∧ W ≤ U ⊓ V})
    (hρ : ∀ (W V U : X.Opens) (hWV : W ≤ V) (hVU : V ≤ U) (hU : U ∈ B) (hV : V ∈ B)
      (hW : W ∈ B), (ρ W U (hWV.trans hVU) hU hW).hom =
        (pullbackLEComp hWV hVU (K U hU)).inv ≫ (pullbackLE hWV).map (ρ V U hVU hU hV).hom ≫
          (ρ W V hWV hV hW).hom)
    (hExt : ∀ (U : X.Opens) (hU : U ∈ B), ∀ n : ℤ, n < 0 →
      Subsingleton (ShiftedHom (K U hU) (K U hU) n)) :
    ∃ (L : DerivedCategory X.Modules)
      (σ : ∀ (U : X.Opens) (hU : U ∈ B), (derivedPullback U.ι.toLRSHom.toShHom).obj L ≅ K U hU),
      ∀ (V U : X.Opens) (hVU : V ≤ U) (hU : U ∈ B) (hV : V ∈ B),
        (resComp hVU L).inv ≫ (pullbackLE hVU).map (σ U hU).hom ≫ (ρ V U hVU hU hV).hom =
          (σ V hV).hom := by
  obtain ⟨A⟩ := (exists_solution_and_unique_solutionIso_of_covers_unconditional
    (locallyGiven B K ρ hρ) hcover hinter hExt).1
  refine ⟨(topExtension X).obj A.obj,
    fun U hU => ((openResTopIso U).app A.obj).symm ≪≫ A.rho U hU, fun V U hVU hU hV => ?_⟩
  exact compat_chase (openRes hVU) (pullbackLE hVU) ((openResTopIso U).inv.app A.obj)
    (A.rho U hU).hom ((openResComp V U ⊤ hVU le_top).app A.obj)
    ((openResIso hVU).hom.app (K U hU))
    ((openResIso hVU).hom.app ((openRes (le_top : U ≤ ⊤)).obj A.obj))
    ((openResIsoTop hVU).hom.app A.obj) ((openResTopIso V).app A.obj)
    (resComp hVU ((topExtension X).obj A.obj)) (ρ V U hVU hU hV).hom (A.rho V hV).hom
    (A.compatibility V U hVU hU hV) ((openResIso hVU).hom.naturality _)
    (openResIso_hom_app hVU A.obj) (openResIsoTop_hom_app hVU A.obj)

/-- **The BBD glueing lemma for schemes, uniqueness** (Stacks 0D6C). In the situation of
`exists_glueing_of_derivedPullback_opens`, two glued objects `(L, σ)` and `(L', σ')` are
identified by exactly one isomorphism `ψ : L ≅ L'` compatible with the `σ_U` and `σ'_U`. The
cocycle condition is not needed for this. -/
theorem existsUnique_iso_of_derivedPullback_opens (hcover : sSup B = ⊤)
    (hinter : ∀ U ∈ B, ∀ V ∈ B, U ⊓ V = sSup {W | W ∈ B ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : X.Opens) (hU : U ∈ B), ∀ n : ℤ, n < 0 →
      Subsingleton (ShiftedHom (K U hU) (K U hU) n))
    {L L' : DerivedCategory X.Modules}
    (σ : ∀ (U : X.Opens) (hU : U ∈ B), (derivedPullback U.ι.toLRSHom.toShHom).obj L ≅ K U hU)
    (σ' : ∀ (U : X.Opens) (hU : U ∈ B), (derivedPullback U.ι.toLRSHom.toShHom).obj L' ≅ K U hU)
    (hσ : ∀ (V U : X.Opens) (hVU : V ≤ U) (hU : U ∈ B) (hV : V ∈ B),
      (resComp hVU L).inv ≫ (pullbackLE hVU).map (σ U hU).hom ≫ (ρ V U hVU hU hV).hom =
        (σ V hV).hom)
    (hσ' : ∀ (V U : X.Opens) (hVU : V ≤ U) (hU : U ∈ B) (hV : V ∈ B),
      (resComp hVU L').inv ≫ (pullbackLE hVU).map (σ' U hU).hom ≫ (ρ V U hVU hU hV).hom =
        (σ' V hV).hom) :
    ∃! ψ : L ≅ L', ∀ (U : X.Opens) (hU : U ∈ B),
      (derivedPullback U.ι.toLRSHom.toShHom).map ψ.hom ≫ (σ' U hU).hom = (σ U hU).hom := by
  have key : ∀ {M M' : DerivedCategory X.Modules}
      (τ : ∀ (U : X.Opens) (hU : U ∈ B), (derivedPullback U.ι.toLRSHom.toShHom).obj M ≅ K U hU)
      (τ' : ∀ (U : X.Opens) (hU : U ∈ B),
        (derivedPullback U.ι.toLRSHom.toShHom).obj M' ≅ K U hU),
      (∀ (V U : X.Opens) (hVU : V ≤ U) (hU : U ∈ B) (hV : V ∈ B),
        (resComp hVU M).inv ≫ (pullbackLE hVU).map (τ U hU).hom ≫ (ρ V U hVU hU hV).hom =
          (τ V hV).hom) →
      (∀ (V U : X.Opens) (hVU : V ≤ U) (hU : U ∈ B) (hV : V ∈ B),
        (resComp hVU M').inv ≫ (pullbackLE hVU).map (τ' U hU).hom ≫ (ρ V U hVU hU hV).hom =
          (τ' V hV).hom) →
      ∃! ψ : M ⟶ M', ∀ (U : X.Opens) (hU : U ∈ B),
        (derivedPullback U.ι.toLRSHom.toShHom).map ψ = (τ U hU).hom ≫ (τ' U hU).inv :=
    fun τ τ' hτ hτ' => existsUnique_hom_of_derivedPullback_opens B hcover hinter
      (fun U hU n hn => subsingleton_shiftedHom_of_iso (τ U hU) (τ' U hU) n (hExt U hU n hn))
      (fun U hU => (τ U hU).hom ≫ (τ' U hU).inv)
      (fun U hU V hV hVU => conj_compat (pullbackLE hVU) (resComp hVU _)
        (resComp hVU _) (τ U hU) (τ' U hU) (τ V hV) (τ' V hV) (ρ V U hVU hU hV)
        (hτ V U hVU hU hV) (hτ' V U hVU hU hV))
  have hinv : ∀ {M M' : DerivedCategory X.Modules}
      (τ : ∀ (U : X.Opens) (hU : U ∈ B), (derivedPullback U.ι.toLRSHom.toShHom).obj M ≅ K U hU)
      (τ' : ∀ (U : X.Opens) (hU : U ∈ B),
        (derivedPullback U.ι.toLRSHom.toShHom).obj M' ≅ K U hU) (f : M ⟶ M') (g : M' ⟶ M),
      (∀ (U : X.Opens) (hU : U ∈ B),
        (derivedPullback U.ι.toLRSHom.toShHom).map f = (τ U hU).hom ≫ (τ' U hU).inv) →
      (∀ (U : X.Opens) (hU : U ∈ B),
        (derivedPullback U.ι.toLRSHom.toShHom).map g = (τ' U hU).hom ≫ (τ U hU).inv) →
      (∃! w : M ⟶ M, ∀ (U : X.Opens) (hU : U ∈ B),
        (derivedPullback U.ι.toLRSHom.toShHom).map w = (τ U hU).hom ≫ (τ U hU).inv) →
      f ≫ g = 𝟙 M := by
    intro M M' τ τ' f g hf hg hu
    obtain ⟨_, -, hid⟩ := hu
    exact (hid _ fun U hU => map_comp_conj _ f g (τ U hU) (τ' U hU) (τ U hU) (hf U hU)
      (hg U hU)).trans (hid _ fun U hU => map_id_conj _ M (τ U hU)).symm
  obtain ⟨ψ, hψ, huniq⟩ := key σ σ' hσ hσ'
  obtain ⟨ψ', hψ', -⟩ := key σ' σ hσ' hσ
  have h₁ := hinv σ σ' ψ ψ' hψ hψ' (key σ σ hσ hσ)
  have h₂ := hinv σ' σ ψ' ψ hψ' hψ (key σ' σ' hσ' hσ')
  refine ⟨⟨ψ, ψ', h₁, h₂⟩, fun U hU => (Iso.eq_comp_inv (σ' U hU)).mp (hψ U hU),
    fun χ hχ => Iso.ext (huniq χ.hom fun U hU => (Iso.eq_comp_inv (σ' U hU)).mpr (hχ U hU))⟩

end Glueing

end AlgebraicGeometry.Scheme.DerivedPullbackOpensGlueing
