module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismObstructionNatural
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismObstructionSourceIdealAmbient
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismObstructionPush
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismSixTermExactInterior
public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionAlgebraExtensionBridge

/-!
# The ideal of the source thickening in the obstruction of Stacks 0E3V

Let `f : X ⟶ Y` be a morphism of schemes over a field `k`, and let `Y'` be a deformation of `Y`
over the square-zero base `k ⊕ M`. On `|X|` the inverse image `f⁻¹𝒪_{Y'}` is a thickening of
`f⁻¹𝒪_Y`, and its ideal maps canonically to the coefficient sheaf `𝒪_X ⊗_k M`. This file builds
that map and the global sections `1 ⊗ m` of the coefficient sheaf through which it is computed.

## Main definitions

* `Deformation.Examples.coefficientSheafSection`: the global section `1 ⊗ m` of `p^* M^~` for a
  scheme `p : X ⟶ Spec k` and `m ∈ M`.

## Main results

* `Deformation.Examples.coefficientSheafSection_map`: the sections `1 ⊗ m` are natural in `M`.

## References

* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Deformation.Examples

variable {k : Type u} [Field k]

/-- The global section of `M^~` on `Spec k` given by a vector `m ∈ M`. -/
def tildeTopSection (M : FGModuleCat.{u} k) (m : M) :
    (tilde (R := CommRingCat.of k) M.obj).val.obj (op ⊤) :=
  (tilde.toOpen (R := CommRingCat.of k) M.obj ⊤).hom m

/-- The global section of `M^~` given by `m` is natural in `M`: the map `g^~` sends it to the
global section given by `g m`. -/
theorem tildeTopSection_map {M N : FGModuleCat.{u} k} (g : M ⟶ N) (m : M) :
    (((tilde.functor (CommRingCat.of k)).map g.hom).val.app (op ⊤)).hom (tildeTopSection M m) =
      tildeTopSection N (g.hom m) :=
  congrArg (fun φ => φ.hom m) (tilde.toOpen_map_app (R := CommRingCat.of k) g.hom ⊤)

/-- The global section of `M^~` given by `m` is additive in `m`. -/
theorem tildeTopSection_add (M : FGModuleCat.{u} k) (m m' : M) :
    tildeTopSection M (m + m') = tildeTopSection M m + tildeTopSection M m' :=
  map_add (tilde.toOpen (R := CommRingCat.of k) M.obj ⊤).hom m m'

/-- **The global section `1 ⊗ m` of `𝒪_X ⊗_k M`.** For a scheme `p : X ⟶ Spec k` and a vector
`m` of a finite-dimensional `k`-vector space `M`, the image of `m`, read as a global section of
`M^~` on `Spec k`, under the unit `M^~ ⟶ p_* p^* M^~` of the pullback adjunction. -/
def coefficientSheafSection {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    (M : FGModuleCat.{u} k) (m : M) :
    ((Scheme.Modules.pullback p).obj (tilde M.obj)).val.obj (op ⊤) :=
  (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app (tilde M.obj)).val.app
    (op ⊤)).hom (tildeTopSection M m)

/-- **The sections `1 ⊗ m` are natural in `M`**: the map of coefficient sheaves induced by
`g : M ⟶ N` sends `1 ⊗ m` to `1 ⊗ g m`. -/
theorem coefficientSheafSection_map {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    {M N : FGModuleCat.{u} k} (g : M ⟶ N) (m : M) :
    (((coefficientSheafFunctor p).map g).val.app (op ⊤)).hom (coefficientSheafSection p M m) =
      coefficientSheafSection p N (g.hom m) :=
  (congrArg (fun φ => (φ.val.app (op ⊤)).hom (tildeTopSection M m))
    ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.naturality
      ((tilde.functor (CommRingCat.of k)).map g.hom))).symm.trans
    (congrArg (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app
      (tilde N.obj)).val.app (op ⊤)).hom (tildeTopSection_map g m))

/-- The section `1 ⊗ m` of `𝒪_X ⊗_k M` is additive in `m`. -/
theorem coefficientSheafSection_add {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    (M : FGModuleCat.{u} k) (m m' : M) :
    coefficientSheafSection p M (m + m') =
      coefficientSheafSection p M m + coefficientSheafSection p M m' := by
  unfold coefficientSheafSection
  rw [tildeTopSection_add]
  exact map_add _ _ _

/-! ### The ideal of the source thickening -/

section SourceIdeal

open Stacks.Sites.Conormal Stacks.Sites.Conormal.IdealRestriction Stacks.Topology
open AlgebraicGeometry.RingedSpaceThickening
open Stacks.SheafOfModules (ringedSpaceStructureMap)
open RingedSpaceModuleAdjunction

variable {Λ : Type u} [CommRing Λ] [Algebra Λ k]

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
  {M : FGModuleCat.{u} k}
  (yε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)).Fiber
    ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))

/-- The deformation `Y'` of `Y` over `k ⊕ M`, read as a solution of the deformation problem of
Stacks 08U7 on `Y`: its ideal is identified with the pulled-back ideal of the closed point. -/
abbrev sourceSolution :=
  fiberSolution (maximalIdeal_squareZeroExtensionArtinian_pow_two (Λ := Λ) M) yε

/-- The ideal of `Y` in `Y'`, as the pushforward of the pulled-back ideal of the closed point. -/
abbrev sourceIdealModule :=
  (modulePushforward (sourceSolution pY yε).i).obj
    (SchemeDeformationCategory.pulledIdeal ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
      (Over.mk pY))

variable {H : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)}
  (θ : SchemeDeformationCategory.pulledIdeal ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
      (Over.mk pY) ⟶ (modulePushforward f.toLRSHom.toShHom).obj H)

variable (H) in
/-- The `𝒪_X`-module `H`, read as a module over `f⁻¹𝒪_Y` through `f^♯`. -/
abbrev sourceIdealCoefficients :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (J := Opens.grothendieckTopology X.carrier)
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.toLRSHom.toShHom.hom.base).obj Y.sheaf)) :=
  (modulePushforward (RingedSpace.inverseImageSourceInclusion f.toLRSHom.toShHom)).obj H

/-- The value relation of the canonical map on the ideal of `f⁻¹𝒪_{Y'} ⟶ f⁻¹𝒪_Y`: a kernel
section induced by the section `incl q` of the ideal of `Y` in `Y'` goes to the image of `q`
under `θ`. -/
def sourceIdealRel (V : Opens X.carrier)
    (a : ↥(kernelIdeal (Scheme.liftSourceReduction yε.1.specialMap f).hom (op V)))
    (h : ↥((sourceIdealCoefficients f H).val.obj (op V))) : Prop :=
  ∃ (W : Opens yε.1.scheme.carrier)
    (hV : V ≤ (Opens.map (f ≫ yε.1.specialMap).toLRSHom.toShHom.hom.base).obj W)
    (q : ↥((sourceIdealModule pY yε).val.obj (op W))),
    a.1 = ambientSection (f ≫ yε.1.specialMap).toLRSHom.toShHom.hom.base yε.1.scheme.sheaf hV
      ((sourceSolution pY yε).incl q) ∧
    h = H.val.map (homOfLE hV).op
      (θ.val.app (op ((Opens.map yε.1.specialMap.toLRSHom.toShHom.hom.base).obj W)) q)

variable {f pY yε θ}

/-- For a presheaf of commutative rings on a topological space, restricting along `k₁` and then
along `k₂` agrees with restricting along any `k : A ⟶ C`. -/
theorem ringPresheaf_map_map {T : TopCat.{u}} (F : TopCat.Presheaf CommRingCat.{u} T)
    {A B C : (Opens T)ᵒᵖ} (k₁ : A ⟶ B) (k₂ : B ⟶ C) (k : A ⟶ C) (x : F.obj A) :
    (F.map k₂).hom ((F.map k₁).hom x) = (F.map k).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  exact congrArg (fun m => (F.map m).hom x) (Subsingleton.elim _ _)

/-- The relation `sourceIdealRel` is stable under restriction to a smaller open `W ≤ V`. -/
theorem sourceIdealRel_res {V W : Opens X.carrier} (hWV : W ≤ V)
    {a : ↥(kernelIdeal (Scheme.liftSourceReduction yε.1.specialMap f).hom (op V))}
    {h : ↥((sourceIdealCoefficients f H).val.obj (op V))}
    (hR : sourceIdealRel f pY yε θ V a h) :
    sourceIdealRel f pY yε θ W (kernelRes _ hWV a)
      (((sourceIdealCoefficients f H).val.map (homOfLE hWV).op) h) := by
  obtain ⟨W₁, hV₁, q, ha, hh⟩ := hR
  refine ⟨W₁, hWV.trans hV₁, q, ?_, ?_⟩
  · exact (congrArg (((Scheme.liftSource yε.1.specialMap f).obj.map (homOfLE hWV).op).hom)
      ha).trans (ambientSection_res_apply _ _ hV₁ hWV _)
  · rw [hh]
    exact map_map_eq_map H _ _ _ _

/-- Applying `θ` to the restriction of `q` from `W` to `W' ≤ W` and restricting to `V` agrees with
applying `θ` to `q` and restricting to `V`. -/
theorem sourceIdealTheta_res {W W' : Opens yε.1.scheme.carrier} (hW : W' ≤ W)
    {V : Opens X.carrier}
    (hV : V ≤ (Opens.map (f ≫ yε.1.specialMap).toLRSHom.toShHom.hom.base).obj W')
    (q : ↥((sourceIdealModule pY yε).val.obj (op W))) :
    H.val.map (homOfLE hV).op
        (θ.val.app (op ((Opens.map yε.1.specialMap.toLRSHom.toShHom.hom.base).obj W'))
          ((sourceIdealModule pY yε).val.map (homOfLE hW).op q)) =
      H.val.map (homOfLE (hV.trans ((Opens.map _).monotone hW))).op
        (θ.val.app (op ((Opens.map yε.1.specialMap.toLRSHom.toShHom.hom.base).obj W)) q) :=
  (congrArg (H.val.map (homOfLE hV).op) (PresheafOfModules.naturality_apply θ.val
    (homOfLE ((Opens.map yε.1.specialMap.toLRSHom.toShHom.hom.base).monotone hW)).op q)).trans
    (map_map_eq_map H _ _ _ _)

/-- The relation `sourceIdealRel` is additive: if `a` is related to `h` and `b` to `h'`, then
`a + b` is related to `h + h'`. -/
theorem sourceIdealRel_add {V : Opens X.carrier}
    {a b : ↥(kernelIdeal (Scheme.liftSourceReduction yε.1.specialMap f).hom (op V))}
    {h h' : ↥((sourceIdealCoefficients f H).val.obj (op V))}
    (ha : sourceIdealRel f pY yε θ V a h) (hb : sourceIdealRel f pY yε θ V b h') :
    sourceIdealRel f pY yε θ V (a + b) (h + h') := by
  obtain ⟨W₁, hV₁, q₁, ha₁, hh₁⟩ := ha
  obtain ⟨W₂, hV₂, q₂, hb₂, hh₂⟩ := hb
  refine ⟨W₁ ⊓ W₂, le_inf hV₁ hV₂,
    (sourceIdealModule pY yε).val.map (homOfLE inf_le_left).op q₁ +
      (sourceIdealModule pY yε).val.map (homOfLE inf_le_right).op q₂, ?_, ?_⟩
  · have e1 : (sourceSolution pY yε).incl
        ((sourceIdealModule pY yε).val.map (homOfLE inf_le_left).op q₁ +
          (sourceIdealModule pY yε).val.map (homOfLE inf_le_right).op q₂) =
        (yε.1.scheme.presheaf.map (homOfLE (inf_le_left : W₁ ⊓ W₂ ≤ W₁)).op).hom
            ((sourceSolution pY yε).incl q₁) +
          (yε.1.scheme.presheaf.map (homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂)).op).hom
            ((sourceSolution pY yε).incl q₂) :=
      (DeformationSolution.incl_add _ _).trans (congrArg₂ (· + ·)
        (DeformationSolution.incl_naturality _ _) (DeformationSolution.incl_naturality _ _))
    refine Eq.trans ?_ ((congrArg (ambientSection (f ≫ yε.1.specialMap).toLRSHom.toShHom.hom.base
      yε.1.scheme.sheaf (le_inf hV₁ hV₂)).hom e1).trans
      (map_add (ambientSection (f ≫ yε.1.specialMap).toLRSHom.toShHom.hom.base
        yε.1.scheme.sheaf (le_inf hV₁ hV₂)).hom _ _)).symm
    exact congrArg₂ (· + ·) (ha₁.trans (ambientSection_map_apply' _ _ _ _ _).symm)
      (hb₂.trans (ambientSection_map_apply' _ _ _ _ _).symm)
  · refine (congrArg₂ (· + ·)
      (hh₁.trans (sourceIdealTheta_res (θ := θ) (hW := (inf_le_left : W₁ ⊓ W₂ ≤ W₁))
        (le_inf hV₁ hV₂) q₁).symm)
      (hh₂.trans (sourceIdealTheta_res (θ := θ) (hW := (inf_le_right : W₁ ⊓ W₂ ≤ W₂))
        (le_inf hV₁ hV₂) q₂).symm)).trans ?_
    refine (map_add (H.val.map (homOfLE (le_inf hV₁ hV₂)).op).hom _ _).symm.trans ?_
    exact congrArg (H.val.map (homOfLE (le_inf hV₁ hV₂)).op).hom
      (map_add (θ.val.app _).hom _ _).symm

/-- The relation `sourceIdealRel` is functional: a kernel section is related to at most one
section of the coefficients. -/
theorem sourceIdealRel_unique {V : Opens X.carrier}
    {a : ↥(kernelIdeal (Scheme.liftSourceReduction yε.1.specialMap f).hom (op V))}
    {h h' : ↥((sourceIdealCoefficients f H).val.obj (op V))}
    (hR : sourceIdealRel f pY yε θ V a h) (hR' : sourceIdealRel f pY yε θ V a h') : h = h' := by
  obtain ⟨W₁, hV₁, q₁, ha₁, hh₁⟩ := hR
  obtain ⟨W₂, hV₂, q₂, ha₂, hh₂⟩ := hR'
  have hV : V ≤ (Opens.map (f ≫ yε.1.specialMap).toLRSHom.toShHom.hom.base).obj (W₁ ⊓ W₂) :=
    le_inf hV₁ hV₂
  have he : ambientSection (f ≫ yε.1.specialMap).toLRSHom.toShHom.hom.base yε.1.scheme.sheaf hV
      ((yε.1.scheme.presheaf.map (homOfLE (inf_le_left : W₁ ⊓ W₂ ≤ W₁)).op).hom
        ((sourceSolution pY yε).incl q₁)) =
      ambientSection (f ≫ yε.1.specialMap).toLRSHom.toShHom.hom.base yε.1.scheme.sheaf hV
      ((yε.1.scheme.presheaf.map (homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂)).op).hom
        ((sourceSolution pY yε).incl q₂)) :=
    ((ambientSection_map_apply' _ _ _ _ _).trans ha₁.symm).trans
      (ha₂.trans (ambientSection_map_apply' _ _ _ _ _).symm)
  choose W' hW' hxW' heq using fun x : V =>
    exists_map_eq_of_ambientSection_eq _ _ hV _ _ he x.1 x.2
  refine TopCat.Sheaf.eq_of_locally_eq' (⟨H.val.presheaf, H.isSheaf⟩ : TopCat.Sheaf _ _)
    (fun x : V => V ⊓ (Opens.map (f ≫ yε.1.specialMap).toLRSHom.toShHom.hom.base).obj (W' x))
    V (fun x => homOfLE inf_le_left) (fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, hx, hxW' ⟨x, hx⟩⟩)
    h h' fun x => ?_
  have hq : (sourceIdealModule pY yε).val.map (homOfLE ((hW' x).trans inf_le_left)).op q₁ =
      (sourceIdealModule pY yε).val.map (homOfLE ((hW' x).trans inf_le_right)).op q₂ := by
    refine (sourceSolution pY yε).incl_injective ?_
    refine (DeformationSolution.incl_naturality _ _).trans (Eq.trans ?_
      (DeformationSolution.incl_naturality _ _).symm)
    exact (ringPresheaf_map_map _ _ _ _ _).symm.trans ((heq x).trans
      (ringPresheaf_map_map _ _ _ _ _))
  have hVx : V ⊓ (Opens.map (f ≫ yε.1.specialMap).toLRSHom.toShHom.hom.base).obj (W' x) ≤
      (Opens.map (f ≫ yε.1.specialMap).toLRSHom.toShHom.hom.base).obj (W' x) := inf_le_right
  have e₁ := sourceIdealTheta_res (θ := θ) (hW := (hW' x).trans inf_le_left) hVx q₁
  have e₂ := sourceIdealTheta_res (θ := θ) (hW := (hW' x).trans inf_le_right) hVx q₂
  rw [hq] at e₁
  change H.val.map (homOfLE inf_le_left).op h = H.val.map (homOfLE inf_le_left).op h'
  rw [hh₁, hh₂]
  exact ((map_map_eq_map H (homOfLE hV₁).op (homOfLE inf_le_left).op _ _).trans e₁.symm).trans
    (e₂.trans (map_map_eq_map H (homOfLE hV₂).op (homOfLE inf_le_left).op _ _).symm)

/-- Every kernel section `a` over `U` is, near each point `x ∈ U`, related by `sourceIdealRel` to
some section of the coefficients: there is an open `x ∈ V ≤ U` on which the restriction of `a`
has an image. -/
theorem sourceIdealRel_exists {U : Opens X.carrier}
    (a : ↥(kernelIdeal (Scheme.liftSourceReduction yε.1.specialMap f).hom (op U))) (x : X.carrier)
    (hx : x ∈ U) :
    ∃ (V : Opens X.carrier) (hVU : V ≤ U), x ∈ V ∧ ∃ h, sourceIdealRel f pY yε θ V
      (kernelRes (Scheme.liftSourceReduction yε.1.specialMap f) hVU a) h := by
  have : IsClosedImmersion yε.1.specialMap := deformationSpecialMap_isClosedImmersion yε.1
  obtain ⟨W, V, hVU, hVW, hxV, t, ht⟩ := exists_res_eq_ambientSection
    (f ≫ yε.1.specialMap).toLRSHom.toShHom.hom.base yε.1.scheme.sheaf a.1 x hx
  have hVW' : V ≤ (Opens.map f.toLRSHom.toShHom.hom.base).obj
      ((Opens.map yε.1.specialMap.toLRSHom.toShHom.hom.base).obj W) := hVW
  have h0 : ambientSection f.toLRSHom.toShHom.hom.base Y.sheaf hVW'
      ((yε.1.specialMap.toLRSHom.toShHom.hom.c.app (op W)).hom t) =
      ambientSection f.toLRSHom.toShHom.hom.base Y.sheaf hVW' 0 :=
    (Scheme.liftSourceReduction_ambientSection _ _ hVW t).symm.trans
      ((congrArg ((Scheme.liftSourceReduction yε.1.specialMap f).hom.app (op V)).hom ht.symm).trans
        ((kernelRes (Scheme.liftSourceReduction yε.1.specialMap f) hVU a).2.trans
          (map_zero _).symm))
  obtain ⟨O, hO, hxO, hOe⟩ := exists_map_eq_of_ambientSection_eq _ _ hVW' _ _ h0 x hxV
  obtain ⟨W'', hW''o, hW''⟩ :=
    yε.1.specialMap.isClosedEmbedding.isInducing.isOpen_iff.1 O.isOpen
  let W₂ : Opens yε.1.scheme.carrier := W ⊓ ⟨W'', hW''o⟩
  have hW₂O : (Opens.map yε.1.specialMap.toLRSHom.toShHom.hom.base).obj W₂ ≤ O := by
    intro y hy
    change y ∈ (O : Set Y.carrier)
    rw [← hW'']
    exact hy.2
  let t₂ := (yε.1.scheme.presheaf.map (homOfLE (inf_le_left : W₂ ≤ W)).op).hom t
  have hred : (sourceSolution pY yε).reduction t₂ = 0 := by
    change (yε.1.specialMap.toLRSHom.toShHom.hom.c.app (op W₂)).hom t₂ = 0
    have hn : (yε.1.specialMap.toLRSHom.toShHom.hom.c.app (op W₂)).hom t₂ =
        (Y.presheaf.map (homOfLE ((Opens.map yε.1.specialMap.toLRSHom.toShHom.hom.base).monotone
          (inf_le_left : W₂ ≤ W))).op).hom
          ((yε.1.specialMap.toLRSHom.toShHom.hom.c.app (op W)).hom t) :=
      NatTrans.naturality_apply yε.1.specialMap.toLRSHom.toShHom.hom.c
        (homOfLE (inf_le_left : W₂ ≤ W)).op t
    refine hn.trans ?_
    refine (ringPresheaf_map_map Y.presheaf (homOfLE hO).op (homOfLE hW₂O).op _ _).symm.trans ?_
    exact (congrArg (Y.presheaf.map (homOfLE hW₂O).op).hom hOe).trans
      ((congrArg (Y.presheaf.map (homOfLE hW₂O).op).hom (map_zero _)).trans (map_zero _))
  obtain ⟨q, hq⟩ := (sourceSolution pY yε).exists_incl t₂ hred
  have hxW₂ : x ∈ V ⊓ (Opens.map (f ≫ yε.1.specialMap).toLRSHom.toShHom.hom.base).obj W₂ := by
    refine ⟨hxV, hVW hxV, ?_⟩
    change yε.1.specialMap.base (f.base x) ∈ W''
    rw [← Set.mem_preimage, hW'']
    exact hxO
  refine ⟨_, inf_le_left.trans hVU, hxW₂, _, W₂, inf_le_right, q, ?_, rfl⟩
  rw [hq]
  refine Eq.trans ?_ (ambientSection_map_apply' _ _ _ _ _).symm
  refine (ringPresheaf_map_map _ (homOfLE hVU).op (homOfLE inf_le_left).op _ _).symm.trans ?_
  refine (congrArg _ ht).trans ?_
  exact ambientSection_res_apply _ _ hVW inf_le_left t

/-- The relation `sourceIdealRel` is locally compatible with scalars: if `a` is related to `h`,
then near each point `x ∈ V` the restriction of `r • a` is related to the restriction of the
image of `r` acting on `h`. -/
theorem sourceIdealRel_smul {V : Opens X.carrier}
    {a : ↥(kernelIdeal (Scheme.liftSourceReduction yε.1.specialMap f).hom (op V))}
    {h : ↥((sourceIdealCoefficients f H).val.obj (op V))}
    (hR : sourceIdealRel f pY yε θ V a h)
    (r : ↥((Scheme.liftSource yε.1.specialMap f).obj.obj (op V))) (x : X.carrier) (hx : x ∈ V) :
    ∃ (V₂ : Opens X.carrier) (hV₂ : V₂ ≤ V), x ∈ V₂ ∧
      sourceIdealRel f pY yε θ V₂ (kernelRes _ hV₂ (r • a))
        (((sourceIdealCoefficients f H).val.map (homOfLE hV₂).op)
          (presentationScalar (Scheme.liftSourceReduction yε.1.specialMap f) (op V) r • h)) := by
  obtain ⟨W, hV, q, ha, hh⟩ := hR
  obtain ⟨Wb, V₂, hV₂, hV₂b, hxV₂, b, hb⟩ := exists_res_eq_ambientSection
    (f ≫ yε.1.specialMap).toLRSHom.toShHom.hom.base yε.1.scheme.sheaf r x hx
  have hV₃ : V₂ ≤ (Opens.map (f ≫ yε.1.specialMap).toLRSHom.toShHom.hom.base).obj (W ⊓ Wb) :=
    le_inf (hV₂.trans hV) hV₂b
  let b₃ : (sourceSolution pY yε).X'.presheaf.obj (op (W ⊓ Wb)) :=
    (yε.1.scheme.presheaf.map (homOfLE (inf_le_right : W ⊓ Wb ≤ Wb)).op).hom b
  let q₃ : ↥((sourceIdealModule pY yε).val.obj (op (W ⊓ Wb))) :=
    (sourceIdealModule pY yε).val.map (homOfLE (inf_le_left : W ⊓ Wb ≤ W)).op q
  refine ⟨V₂, hV₂, hxV₂, W ⊓ Wb, hV₃, b₃ • q₃, ?_, ?_⟩
  · have e2 := (congrArg (ambientSection (f ≫ yε.1.specialMap).toLRSHom.toShHom.hom.base
      yε.1.scheme.sheaf hV₃).hom
        (DeformationSolution.mul_incl (Q := sourceSolution pY yε) b₃ q₃).symm).trans
      (map_mul _ _ _)
    refine (map_mul ((Scheme.liftSource yε.1.specialMap f).obj.map (homOfLE hV₂).op).hom
      r a.1).trans (Eq.trans ?_ e2.symm)
    refine congrArg₂ (· * ·) (hb.trans (ambientSection_map_apply' _ _ _ _ _).symm) ?_
    refine (congrArg _ ha).trans ((ambientSection_res_apply _ _ hV hV₂ _).trans ?_)
    refine (ambientSection_map_apply' _ _ inf_le_left hV₃ _).symm.trans ?_
    exact congrArg _ (DeformationSolution.incl_naturality (Q := sourceSolution pY yε)
      (homOfLE (inf_le_left : W ⊓ Wb ≤ W)).op q).symm
  · have hcomp := ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app (op V₂))
      (Scheme.liftSourceReduction_comp yε.1.specialMap f))
      (((Scheme.liftSource yε.1.specialMap f).obj.map (homOfLE hV₂).op).hom r)
    have hL : (X.presheaf.map (homOfLE hV₂).op).hom
        (((ringedSpaceStructureMap f.toLRSHom.toShHom).hom.app (op V)).hom
          ((Scheme.liftSourceReduction yε.1.specialMap f).hom.app (op V) r)) =
        (X.presheaf.map (homOfLE hV₂b).op).hom
          (((f ≫ yε.1.specialMap).toLRSHom.toShHom.hom.c.app (op Wb)).hom b) := by
      refine (NatTrans.naturality_apply (ringedSpaceStructureMap f.toLRSHom.toShHom).hom
        (homOfLE hV₂).op _).symm.trans ?_
      refine (congrArg _ (NatTrans.naturality_apply
        (Scheme.liftSourceReduction yε.1.specialMap f).hom (homOfLE hV₂).op r).symm).trans ?_
      refine (CommRingCat.comp_apply _ _ _).symm.trans (hcomp.trans ?_)
      exact (congrArg _ hb).trans
        (ringedSpaceStructureMap_ambientSection (f ≫ yε.1.specialMap).toLRSHom.toShHom hV₂b b)
    have hR : (X.presheaf.map (homOfLE hV₃).op).hom
        (((f ≫ yε.1.specialMap).toLRSHom.toShHom.hom.c.app (op (W ⊓ Wb))).hom b₃) =
        (X.presheaf.map (homOfLE hV₂b).op).hom
          (((f ≫ yε.1.specialMap).toLRSHom.toShHom.hom.c.app (op Wb)).hom b) := by
      refine (congrArg _ (NatTrans.naturality_apply
        (f ≫ yε.1.specialMap).toLRSHom.toShHom.hom.c
        (homOfLE (inf_le_right : W ⊓ Wb ≤ Wb)).op b)).trans ?_
      exact ringPresheaf_map_map _ _ _ _ _
    let c₀ : (structureSheafRing X.toRingedSpace).obj.obj (op V) :=
      ((ringedSpaceStructureMap f.toLRSHom.toShHom).hom.app (op V)).hom
        ((Scheme.liftSourceReduction yε.1.specialMap f).hom.app (op V) r)
    let h₀ : H.val.obj (op V) := h
    let c₁ : (structureSheafRing X.toRingedSpace).obj.obj
        (op ((Opens.map (f ≫ yε.1.specialMap).toLRSHom.toShHom.hom.base).obj (W ⊓ Wb))) :=
      ((f ≫ yε.1.specialMap).toLRSHom.toShHom.hom.c.app (op (W ⊓ Wb))).hom b₃
    let θ₃ : H.val.obj
        (op ((Opens.map (f ≫ yε.1.specialMap).toLRSHom.toShHom.hom.base).obj (W ⊓ Wb))) :=
      θ.val.app (op ((Opens.map yε.1.specialMap.toLRSHom.toShHom.hom.base).obj (W ⊓ Wb))) q₃
    have eA : ((sourceIdealCoefficients f H).val.map (homOfLE hV₂).op)
        (presentationScalar (Scheme.liftSourceReduction yε.1.specialMap f) (op V) r • h) =
        H.val.map (homOfLE hV₂).op (c₀ • h₀) := rfl
    have eB : θ.val.app (op ((Opens.map yε.1.specialMap.toLRSHom.toShHom.hom.base).obj (W ⊓ Wb)))
        (b₃ • q₃) = c₁ • θ₃ :=
      (θ.val.app _).hom.map_smul _ _
    refine eA.trans (Eq.trans ?_ (congrArg (H.val.map (homOfLE hV₃).op).hom eB).symm)
    refine (PresheafOfModules.map_smul H.val (homOfLE hV₂).op c₀ h₀).trans (Eq.trans ?_
      (PresheafOfModules.map_smul H.val (homOfLE hV₃).op c₁ θ₃).symm)
    refine congrArg₂ (· • ·) (hL.trans hR.symm) ?_
    change H.val.map (homOfLE hV₂).op h = H.val.map (homOfLE hV₃).op θ₃
    rw [hh]
    exact (map_map_eq_map H (homOfLE hV).op (homOfLE hV₂).op _ _).trans
      (sourceIdealTheta_res (θ := θ) (hW := (inf_le_left : W ⊓ Wb ≤ W)) hV₃ q).symm

variable (f pY yε θ)

/-- The local rule of the canonical map on the ideal of `f⁻¹𝒪_{Y'} ⟶ f⁻¹𝒪_Y`. -/
def sourceIdealRule :
    LocalRule (Scheme.liftSourceReduction yε.1.specialMap f) (sourceIdealCoefficients f H) where
  R := sourceIdealRel f pY yε θ
  exists_local a x hx := sourceIdealRel_exists a x hx
  unique := sourceIdealRel_unique
  res hWV _ _ hR := sourceIdealRel_res hWV hR
  add := sourceIdealRel_add
  smul hR r x hx := sourceIdealRel_smul hR r x hx

/-- **The canonical map on the ideal of the source thickening**, for an arbitrary map `θ` out of
the pulled-back ideal: the restriction datum `Ker(f⁻¹𝒪_{Y'} ⟶ f⁻¹𝒪_Y) ⟶ H` which takes the
section induced by `incl q` to `θ(q)`. -/
def sourceIdealRestrictionOf :
    IdealRestriction.{u, u, u, u} (Scheme.liftSourceReduction yε.1.specialMap f)
      (sourceIdealCoefficients f H) :=
  (sourceIdealRule f pY yε θ).toIdealRestriction

variable {f pY yε θ}

/-- The map `sourceIdealRestrictionOf` sends a kernel section `a` to any section `h` related to
it by `sourceIdealRel`. -/
theorem sourceIdealRestrictionOf_app_eq {V : Opens X.carrier}
    {a : ↥(kernelIdeal (Scheme.liftSourceReduction yε.1.specialMap f).hom (op V))}
    {h : ↥((sourceIdealCoefficients f H).val.obj (op V))}
    (hR : sourceIdealRel f pY yε θ V a h) : (sourceIdealRestrictionOf f pY yε θ).app (op V) a = h :=
  LocalRule.toIdealRestriction_app_eq _ hR

/-! ### The transfer of the coefficients along `f`, and the generators `ũ(m)` -/

variable (f pY M) in
/-- The map `p_Y^* M^~ ⟶ f_*((f ≫ p_Y)^* M^~)` of `𝒪_Y`-modules: the transpose, along
`p_Y^* ⊣ p_{Y,*}`, of the unit of `(f ≫ p_Y)^* ⊣ (f ≫ p_Y)_*`. It sends `1 ⊗ m` to `1 ⊗ m`. -/
def coefficientTransfer :
    (Scheme.Modules.pullback pY).obj (tilde M.obj) ⟶
      (modulePushforward f.toLRSHom.toShHom).obj (schemeMorphismCoefficientSheaf f pY M) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction pY).homEquiv _ _).symm
    ((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ pY)).unit.app (tilde M.obj) ≫
      (Scheme.Modules.pushforwardComp f pY).inv.app _)

/-- **The transfer sends `1 ⊗ m` to `1 ⊗ m`.** -/
theorem coefficientTransfer_section (m : M) :
    ((coefficientTransfer f pY M).val.app (op ((Opens.map pY.base).obj ⊤))).hom
        (coefficientSheafSection pY M m) =
      coefficientSheafSection (f ≫ pY) M m := by
  have h := (Scheme.Modules.pullbackPushforwardAdjunction pY).homEquiv_unit (tilde M.obj)
    ((modulePushforward f.toLRSHom.toShHom).obj (schemeMorphismCoefficientSheaf f pY M))
    (coefficientTransfer f pY M)
  rw [coefficientTransfer, Equiv.apply_symm_apply] at h
  exact (congrArg (fun φ => (φ.val.app (op ⊤)).hom (tildeTopSection M m)) h).symm

end SourceIdeal

end Deformation.Examples

end
