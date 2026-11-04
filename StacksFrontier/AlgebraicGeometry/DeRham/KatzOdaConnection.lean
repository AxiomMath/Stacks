module

public import StacksFrontier.AlgebraicGeometry.DeRham.FormsTensorWedge
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothCohomologySheaves

/-!
# The Katz–Oda Leibniz rule: derivations of `Ω^•_{Y/S} ⊗ ℱ` as connections and de Rham complexes

Let `g : Y ⟶ S` be a morphism of schemes and `ℱ` a sheaf of `𝒪_Y`-modules. A family of maps
`δ_p : Ω^p_{Y/S} ⊗ ℱ ⟶ Ω^{p+1}_{Y/S} ⊗ ℱ` of sheaves of `g^{-1}𝒪_S`-modules is compatible with
the left action of `Ω^•_{Y/S}` in the sense of Katz–Oda if it obeys the graded Leibniz rule

`δ(ω ⊗ s) = dω ⊗ s + (-1)^p ω ∧ δ(1 ⊗ s)`     (`ω` a local `p`-form, `s` a local section).

For such a family:

* the degree-zero map, read through `Ω^0 ⊗ ℱ = ℱ` and `Ω^1 ⊗ ℱ ≅ ℱ ⊗ Ω_{Y/S}`, is a connection
  `∇` on `ℱ`, with `∇(b s) = b ∇(s) + s ⊗ d b`;
* the map in degree `p`, read through the symmetry `Ω^p ⊗ ℱ ≅ ℱ ⊗ Ω^p`, is the twisted de Rham
  differential of `∇`, with `d(s ⊗ ω) = ∇(s) ∧ ω + s ⊗ d ω`;
* if consecutive maps compose to zero, the twisted de Rham sequence is a complex and `∇` is
  integrable.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.formsTensorTerm`: `Ω^p_{Y/S} ⊗ ℱ` as a sheaf of
  `g^{-1}𝒪_S`-modules.
* `AlgebraicGeometry.Scheme.Hom.IsKatzOdaLeibniz`: the Katz–Oda compatibility of a family
  `δ_p : Ω^p ⊗ ℱ ⟶ Ω^{p+1} ⊗ ℱ`.
* `AlgebraicGeometry.Scheme.Hom.katzOdaConnection`: the connection `∇` of a Katz–Oda family.
* `AlgebraicGeometry.Scheme.Hom.katzOdaTwistedDifferential`: its twisted de Rham differential,
  whose arrow in degree `p` is the transported `δ_p`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.katzOdaConnectionApp_smul`: `∇(b s) = b ∇(s) + s ⊗ d b`.
* `AlgebraicGeometry.Scheme.Hom.katzOdaTwistedMap_twistedTmul`:
  `d(s ⊗ ω) = ∇(s) ∧ ω + s ⊗ d ω`.
* `AlgebraicGeometry.Scheme.Hom.katzOdaTwistedDifferential_isComplex` and
  `AlgebraicGeometry.Scheme.Hom.isIntegrable_katzOdaConnection`: if `δ ∘ δ = 0`, then the twisted
  de Rham sequence is a complex and `∇` is integrable.

## References

* [Stacks Project, Tag 0FMN](https://stacks.math.columbia.edu/tag/0FMN)
* [Stacks Project, Tag 07I0](https://stacks.math.columbia.edu/tag/07I0)
* N. Katz, T. Oda, *On the differentiation of de Rham cohomology classes with respect to
  parameters*, J. Math. Kyoto Univ. 8 (1968).
-/

@[expose] public section

open CategoryTheory MonoidalCategory TopologicalSpace Opposite
open Stacks.PullbackTensorCoherence (tmul)
open Stacks.DeRhamDirectImage (inverseImageBase toInverseImageBase)

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
  Stacks.PullbackTensorCoherence.braidedCategory

variable {Y S : Scheme.{u}} (g : Y ⟶ S) (H : Y.Modules)

/-- `Ω^p_{Y/S} ⊗_{𝒪_Y} ℱ` as a sheaf of `g^{-1}𝒪_S`-modules, by restriction of scalars along
`g^{-1}𝒪_S ⟶ 𝒪_Y`. -/
abbrev formsTensorTerm (p : ℤ) : _root_.Modules (inverseImageBase g) :=
  (_root_.pushforward (toInverseImageBase g)).obj (formsTensor g H p)

/-- The Katz–Oda compatibility of a family `δ_p : Ω^p ⊗ ℱ ⟶ Ω^{p+1} ⊗ ℱ` of morphisms of
sheaves of `g^{-1}𝒪_S`-modules: the graded Leibniz rule
`δ(ω ⊗ s) = dω ⊗ s + (-1)^p ω ∧ δ(1 ⊗ s)` for local `p`-forms `ω` and local sections `s`. -/
def IsKatzOdaLeibniz (δ : ∀ p : ℤ, formsTensorTerm g H p ⟶ formsTensorTerm g H (p + 1)) :
    Prop :=
  ∀ (p : ℕ) (U : (Y.Opens)ᵒᵖ) (ω : (relativeDifferentialForms g (p : ℤ)).val.obj U)
    (s : H.val.obj U),
    (formsTensorSuccIso g H p).hom.val.app U ((δ p).val.app U (formsTensorTmul g H p U ω s)) =
      formsTensorTmul g H ((p + 1 : ℕ) : ℤ) U (relativeDeRhamDifferentialSection g p U ω) s +
        (-1 : ℤ) ^ p • (formsTensorSuccIso g H p).hom.val.app U
          (formsTensorWedgeSection g H p 1 U ω ((δ 0).val.app U (formsTensorUnitTmul g H U s)))

variable {g H}

/-- The value `δ_0(1 ⊗ s)` on a local section `s`, switched to `ℱ ⊗ Ω_{Y/S}`. -/
def katzOdaConnectionApp (δ : ∀ p : ℤ, formsTensorTerm g H p ⟶ formsTensorTerm g H (p + 1))
    (U : (Y.Opens)ᵒᵖ) (s : H.val.obj U) : (moduleConnectionTarget g H).val.obj U :=
  (formsTensorConnectionIso g H).hom.val.app U ((δ 0).val.app U (formsTensorUnitTmul g H U s))

/-- The renaming of degrees `formsTensorSuccIso` acts as the identity on local sections. -/
theorem formsTensorSuccIso_hom_val_app (q : ℕ) (U : (Y.Opens)ᵒᵖ)
    (x : (formsTensor g H ((q : ℤ) + 1)).val.obj U) :
    (formsTensorSuccIso g H q).hom.val.app U x = x :=
  rfl

/-- `katzOdaConnectionApp` is additive. -/
theorem katzOdaConnectionApp_add
    (δ : ∀ p : ℤ, formsTensorTerm g H p ⟶ formsTensorTerm g H (p + 1))
    (U : (Y.Opens)ᵒᵖ) (s s' : H.val.obj U) :
    katzOdaConnectionApp δ U (s + s') =
      katzOdaConnectionApp δ U s + katzOdaConnectionApp δ U s' := by
  unfold katzOdaConnectionApp
  exact (congrArg (fun z ↦ (formsTensorConnectionIso g H).hom.val.app U ((δ 0).val.app U z))
    (formsTensorTmul_add_right g H 0 U _ s s')).trans
    ((congrArg (fun z ↦ (formsTensorConnectionIso g H).hom.val.app U z) (map_add _ _ _)).trans
      (map_add _ _ _))

/-- `katzOdaConnectionApp` commutes with restriction. -/
theorem katzOdaConnectionApp_restrict
    (δ : ∀ p : ℤ, formsTensorTerm g H p ⟶ formsTensorTerm g H (p + 1))
    {U V : (Y.Opens)ᵒᵖ} (k : U ⟶ V) (s : H.val.obj U) :
    (moduleConnectionTarget g H).val.map k (katzOdaConnectionApp δ U s) =
      katzOdaConnectionApp δ V (H.val.map k s) := by
  unfold katzOdaConnectionApp
  refine
    (PresheafOfModules.naturality_apply (formsTensorConnectionIso g H).hom.val k _).symm.trans ?_
  refine congrArg _ ((PresheafOfModules.naturality_apply (δ 0).val k _).symm.trans ?_)
  refine congrArg _ ((formsTensorTmul_restrict g H 0 k _ s).trans ?_)
  exact congrArg (fun z ↦ formsTensorTmul g H 0 V z (H.val.map k s))
    ((relativeDifferentialFormsAlgebra g).one.2 k)

/-- The connection of a Katz–Oda family, as additive maps on local sections. -/
def katzOdaConnectionHom
    (δ : ∀ p : ℤ, formsTensorTerm g H p ⟶ formsTensorTerm g H (p + 1)) (U : (Y.Opens)ᵒᵖ) :
    H.val.obj U →+ (moduleConnectionTarget g H).val.obj U :=
  AddMonoidHom.mk' (katzOdaConnectionApp δ U) (katzOdaConnectionApp_add δ U)

/-- A local function on `Y`, as a section of `Stacks.RingedSpace.structureRingSheaf`. It is the
identity. -/
abbrev ringSectionOnRing (U : (Y.Opens)ᵒᵖ) (b : Y.ringCatSheaf.obj.obj U) :
    (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace).obj.obj U :=
  b

/-- The degree-one differential of a function `b`, read as `d(b · 1)` on the degree-zero form
`b · 1`, is the universal relative derivation of `b` sent to `Ω^1_{Y/S}`. -/
theorem formsTensorTmul_deRham_smul_one (U : (Y.Opens)ᵒᵖ) (b : Y.sheaf.obj.obj U)
    (s : H.val.obj U) :
    formsTensorTmul g H ((0 + 1 : ℕ) : ℤ) U
        (relativeDeRhamDifferentialSection g 0 U (b • (deRhamAlgebras g).exterior.one.eval U)) s =
      formsTensorTmul g H 1 U
        ((Scheme.Modules.exteriorGenerator (relativeDifferentials g)).val.app U
          ((universalRelativeDerivation g).d (X := U) b)) s :=
  eq_of_heq (formsTensorTmul_heq g H (by norm_num) U _ _ (deRhamComplex_degreeZero g U b) s)

/-- The Katz–Oda Leibniz rule in degree zero: for a Katz–Oda family `δ`,
`δ_0(1 ⊗ b s) = d b ⊗ s + b · δ_0(1 ⊗ s)`. -/
theorem IsKatzOdaLeibniz.degree_zero
    {δ : ∀ p : ℤ, formsTensorTerm g H p ⟶ formsTensorTerm g H (p + 1)}
    (hδ : IsKatzOdaLeibniz g H δ) (U : (Y.Opens)ᵒᵖ) (b : Y.ringCatSheaf.obj.obj U)
    (s : H.val.obj U) :
    (δ 0).val.app U (formsTensorUnitTmul g H U (b • s)) =
      formsTensorTmul g H 1 U
          ((Scheme.Modules.exteriorGenerator (relativeDifferentials g)).val.app U
            ((universalRelativeDerivation g).d (X := U) b)) s +
        ringSectionOnRing U b • (show (formsTensor g H 1).val.obj U from
          (δ 0).val.app U (formsTensorUnitTmul g H U s)) := by
  have h1 : formsTensorUnitTmul g H U (b • s) =
      formsTensorTmul g H 0 U
        (ringSectionOnRing U b • (relativeDifferentialFormsAlgebra g).one.eval U) s :=
    (formsTensorTmul_smul_left g H 0 U (ringSectionOnRing U b) _ s).symm
  have h2 := hδ 0 U (ringSectionOnRing U b • (relativeDifferentialFormsAlgebra g).one.eval U) s
  have h3 : formsTensorWedgeSection g H (0 : ℕ) 1 U
      (ringSectionOnRing U b • (relativeDifferentialFormsAlgebra g).one.eval U)
        ((δ 0).val.app U (formsTensorUnitTmul g H U s)) =
      ringSectionOnRing U b • (show (formsTensor g H 1).val.obj U from
          (δ 0).val.app U (formsTensorUnitTmul g H U s)) :=
    (formsTensorWedgeSection_smul_left g H 0 1 U _ _ _).trans
      (congrArg (fun z ↦ ringSectionOnRing U b • z)
        (eq_of_heq (formsTensorWedgeSection_one g H 1 U _)))
  rw [h1]
  refine h2.trans ?_
  rw [pow_zero, one_smul, formsTensorSuccIso_hom_val_app, h3]
  exact congrArg (· + _) (formsTensorTmul_deRham_smul_one (g := g) (H := H) U b s)

/-- The Leibniz rule `∇(b s) = b ∇(s) + s ⊗ d b` for the connection of a Katz–Oda family. -/
theorem katzOdaConnectionApp_smul
    {δ : ∀ p : ℤ, formsTensorTerm g H p ⟶ formsTensorTerm g H (p + 1)}
    (hδ : IsKatzOdaLeibniz g H δ) (U : (Y.Opens)ᵒᵖ) (b : Y.ringCatSheaf.obj.obj U)
    (s : H.val.obj U) :
    katzOdaConnectionApp δ U (b • s) =
      b • katzOdaConnectionApp δ U s +
        connectionTmul g H U s ((universalRelativeDerivation g).d (X := U) b) := by
  refine (congrArg (fun z ↦ (formsTensorConnectionIso g H).hom.val.app U z)
    (hδ.degree_zero U b s)).trans ((map_add _ _ _).trans ?_)
  rw [add_comm]
  exact congrArg₂ (· + ·) (map_smul _ _ _)
    (formsTensorConnectionIso_hom_tmul g H U _ s)

/-- The connection of a Katz–Oda family `δ_p : Ω^p ⊗ ℱ ⟶ Ω^{p+1} ⊗ ℱ`: the degree-zero map
`ℱ = Ω^0 ⊗ ℱ ⟶ Ω^1 ⊗ ℱ ≅ ℱ ⊗ Ω_{Y/S}`, as a connection on `ℱ` relative to `g`. -/
def katzOdaConnection
    {δ : ∀ p : ℤ, formsTensorTerm g H p ⟶ formsTensorTerm g H (p + 1)}
    (hδ : IsKatzOdaLeibniz g H δ) : ModuleConnection g H where
  d U := katzOdaConnectionHom δ U
  d_restrict k s := katzOdaConnectionApp_restrict δ k s
  leibniz U b s := katzOdaConnectionApp_smul hδ U b s

/-- The connection of a Katz–Oda family on a local section `s` is `δ_0(1 ⊗ s)`, switched to
`ℱ ⊗ Ω_{Y/S}`. -/
theorem katzOdaConnection_d
    {δ : ∀ p : ℤ, formsTensorTerm g H p ⟶ formsTensorTerm g H (p + 1)}
    (hδ : IsKatzOdaLeibniz g H δ) (U : (Y.Opens)ᵒᵖ) (s : H.val.obj U) :
    (katzOdaConnection hδ).d U s =
      (formsTensorConnectionIso g H).hom.val.app U
        ((δ 0).val.app U (formsTensorUnitTmul g H U s)) :=
  rfl

/-! ### The twisted de Rham differential of a Katz–Oda family -/

/-- The transported map: `δ_q : Ω^q ⊗ ℱ ⟶ Ω^{q+1} ⊗ ℱ` read on `ℱ ⊗ Ω^q ⟶ ℱ ⊗ Ω^{q+1}` through
the symmetry constraint of the tensor product, as a morphism of sheaves of `g^{-1}𝒪_S`-modules
between the terms of the twisted de Rham complex. -/
def katzOdaTwistedMap (δ : ∀ p : ℤ, formsTensorTerm g H p ⟶ formsTensorTerm g H (p + 1))
    (q : ℕ) : twistedTerm g H q ⟶ twistedTerm g H (q + 1) :=
  (_root_.pushforward (toInverseImageBase g)).map
      (β_ (modulesOnRing H) (formsOnRing g q)).hom ≫ δ q ≫
    (_root_.pushforward (toInverseImageBase g)).map
      ((formsTensorSuccIso g H q).hom ≫
        (β_ (formsOnRing g ((q + 1 : ℕ) : ℤ)) (modulesOnRing H)).hom)

/-- `(-1)^q · (-1)^q = 1`, as the scalar action on an additive group. -/
private theorem neg_one_pow_zsmul_zsmul {M : Type*} [AddCommGroup M] (q : ℕ) (x : M) :
    (-1 : ℤ) ^ q • (-1 : ℤ) ^ q • x = x := by
  rw [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

/-- The Leibniz rule `d(s ⊗ ω) = ∇(s) ∧ ω + s ⊗ d ω` for the transported map of a Katz–Oda
family, where `∇` is `katzOdaConnection`. -/
theorem katzOdaTwistedMap_twistedTmul
    {δ : ∀ p : ℤ, formsTensorTerm g H p ⟶ formsTensorTerm g H (p + 1)}
    (hδ : IsKatzOdaLeibniz g H δ) (q : ℕ) (U : (Y.Opens)ᵒᵖ) (s : H.val.obj U)
    (ω : (relativeDifferentialForms g (q : ℤ)).val.obj U) :
    (katzOdaTwistedMap δ q).val.app U (twistedTmul g H q U s ω) =
      twistedFormsWedgeSection g H q U ((katzOdaConnection hδ).d U s) ω +
        twistedTmul g H (q + 1) U s (relativeDeRhamDifferentialSection g q U ω) := by
  have hsign := braiding_formsTensorWedgeSection g H q U ω
    (show (formsTensor g H 1).val.obj U from (δ 0).val.app U (formsTensorUnitTmul g H U s))
  have hl : (katzOdaTwistedMap δ q).val.app U (twistedTmul g H q U s ω) =
      (β_ (formsOnRing g ((q + 1 : ℕ) : ℤ)) (modulesOnRing H)).hom.val.app U
        ((formsTensorSuccIso g H q).hom.val.app U
          ((δ q).val.app U (formsTensorTmul g H q U ω s))) := by
    refine congrArg (fun z ↦ (β_ (formsOnRing g ((q + 1 : ℕ) : ℤ)) (modulesOnRing H)).hom.val.app
      U ((formsTensorSuccIso g H q).hom.val.app U ((δ q).val.app U z))) ?_
    exact Stacks.PullbackTensorCoherence.braiding_tmul Y.toRingedSpace _ _ U s ω
  rw [hl, hδ q U ω s, map_add, map_zsmul, Stacks.PullbackTensorCoherence.braiding_tmul]
  refine (add_comm (G := (twistedForms g H (q + 1)).val.obj U) _ _).trans
    (congrArg (fun z ↦
      z + twistedTmul g H (q + 1) U s (relativeDeRhamDifferentialSection g q U ω)) ?_)
  exact (congrArg (fun z ↦ (-1 : ℤ) ^ q • z) hsign).trans (neg_one_pow_zsmul_zsmul q _)

/-- The twisted de Rham differential of `katzOdaConnection` for a Katz–Oda family: the wedge
pairing is `twistedFormsWedgeSection` and the differential in degree `q` is `δ_q` transported
along the symmetry constraint. -/
def katzOdaTwistedDifferential
    {δ : ∀ p : ℤ, formsTensorTerm g H p ⟶ formsTensorTerm g H (p + 1)}
    (hδ : IsKatzOdaLeibniz g H δ) : TwistedDeRhamDifferential (katzOdaConnection hδ) where
  wedge q U η ω := twistedFormsWedgeSection g H q U η ω
  wedge_add q U η η' ω := twistedFormsWedgeSection_add g H q U η η' ω
  wedge_restrict q _ _ k η ω := twistedFormsWedgeSection_restrict g H q k η ω
  wedge_tmul q U s α ω := twistedFormsWedgeSection_tmul g H q U s α ω
  d q := katzOdaTwistedMap δ q
  d_tmul q U s ω := katzOdaTwistedMap_twistedTmul hδ q U s ω

/-- The arrow of the twisted de Rham differential of a Katz–Oda family in degree `q` is `δ_q`,
transported along the symmetry constraint `ℱ ⊗ Ω^q ≅ Ω^q ⊗ ℱ`. -/
theorem katzOdaTwistedDifferential_d
    {δ : ∀ p : ℤ, formsTensorTerm g H p ⟶ formsTensorTerm g H (p + 1)}
    (hδ : IsKatzOdaLeibniz g H δ) (q : ℕ) :
    (katzOdaTwistedDifferential hδ).d q =
      (_root_.pushforward (toInverseImageBase g)).map
          (β_ (modulesOnRing H) (formsOnRing g q)).hom ≫ δ q ≫
        (_root_.pushforward (toInverseImageBase g)).map
          ((formsTensorSuccIso g H q).hom ≫
            (β_ (formsOnRing g ((q + 1 : ℕ) : ℤ)) (modulesOnRing H)).hom) :=
  rfl

/-- If `δ ∘ δ = 0`, the twisted de Rham sequence of a Katz–Oda family is a complex. -/
theorem katzOdaTwistedDifferential_isComplex
    {δ : ∀ p : ℤ, formsTensorTerm g H p ⟶ formsTensorTerm g H (p + 1)}
    (hδ : IsKatzOdaLeibniz g H δ) (hδδ : ∀ p : ℤ, δ p ≫ δ (p + 1) = 0) :
    (katzOdaTwistedDifferential hδ).IsComplex := by
  intro q
  have hβ : (β_ (formsOnRing g ((q + 1 : ℕ) : ℤ)) (modulesOnRing H)).hom ≫
      (β_ (modulesOnRing H) (formsOnRing g ((q + 1 : ℕ) : ℤ))).hom = 𝟙 _ :=
    @SymmetricCategory.symmetry _ _ _ (Stacks.PullbackTensorCoherence.symmetricCategory
      Y.toRingedSpace) _ _
  have e : (q : ℤ) + 1 = ((q + 1 : ℕ) : ℤ) := by push_cast; rfl
  have hmid : (_root_.pushforward (toInverseImageBase g)).map
        ((formsTensorSuccIso g H q).hom ≫
          (β_ (formsOnRing g ((q + 1 : ℕ) : ℤ)) (modulesOnRing H)).hom) ≫
      (_root_.pushforward (toInverseImageBase g)).map
        (β_ (modulesOnRing H) (formsOnRing g ((q + 1 : ℕ) : ℤ))).hom =
      eqToHom (congrArg (formsTensorTerm g H) e) := by
    have hin : ((formsTensorSuccIso g H q).hom ≫
          (β_ (formsOnRing g ((q + 1 : ℕ) : ℤ)) (modulesOnRing H)).hom) ≫
        (β_ (modulesOnRing H) (formsOnRing g ((q + 1 : ℕ) : ℤ))).hom =
        eqToHom (congrArg (formsTensor g H) e) := by
      rw [Category.assoc, hβ, Category.comp_id]
      rfl
    exact (Functor.map_comp (_root_.pushforward (toInverseImageBase g)) _ _).symm.trans
      ((congrArg (_root_.pushforward (toInverseImageBase g)).map hin).trans
        (eqToHom_map (_root_.pushforward (toInverseImageBase g)) _))
  have key : ∀ {a b : ℤ} (h : a = b), eqToHom (congrArg (formsTensorTerm g H) h) ≫ δ b =
      δ a ≫ eqToHom (congrArg (fun p ↦ formsTensorTerm g H (p + 1)) h) := by
    rintro a b rfl
    simp
  change ((_root_.pushforward (toInverseImageBase g)).map
      (β_ (modulesOnRing H) (formsOnRing g q)).hom ≫ δ q ≫
    (_root_.pushforward (toInverseImageBase g)).map
      ((formsTensorSuccIso g H q).hom ≫
        (β_ (formsOnRing g ((q + 1 : ℕ) : ℤ)) (modulesOnRing H)).hom)) ≫
    ((_root_.pushforward (toInverseImageBase g)).map
      (β_ (modulesOnRing H) (formsOnRing g ((q + 1 : ℕ) : ℤ))).hom ≫ δ ((q + 1 : ℕ) : ℤ) ≫
    (_root_.pushforward (toInverseImageBase g)).map
      ((formsTensorSuccIso g H (q + 1)).hom ≫
        (β_ (formsOnRing g ((q + 1 + 1 : ℕ) : ℤ)) (modulesOnRing H)).hom)) = 0
  simp only [Category.assoc]
  rw [reassoc_of% hmid, reassoc_of% (key e), reassoc_of% (hδδ (q : ℤ)), Limits.zero_comp,
    Limits.comp_zero]

/-- A Katz–Oda family with `δ ∘ δ = 0` gives an integrable connection. -/
theorem isIntegrable_katzOdaConnection
    {δ : ∀ p : ℤ, formsTensorTerm g H p ⟶ formsTensorTerm g H (p + 1)}
    (hδ : IsKatzOdaLeibniz g H δ) (hδδ : ∀ p : ℤ, δ p ≫ δ (p + 1) = 0) :
    (katzOdaConnection hδ).IsIntegrable (katzOdaTwistedDifferential hδ) :=
  (katzOdaTwistedDifferential_isComplex hδ hδδ).isIntegrable

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.DeRhamSmooth

/-- The first-page term `Ω^p_{Y/S} ⊗_{𝒪_Y} ℋ^q_dR(X/Y)` of the flat case of [Stacks, Tag 0FMN]
is `AlgebraicGeometry.Scheme.Hom.formsTensorTerm` at `ℱ = ℋ^q_dR(X/Y)`. -/
theorem deRhamFirstPageFlat_eq_formsTensorTerm {X Y S : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) (p q : ℤ) :
    deRhamFirstPageFlat f g p q =
      AlgebraicGeometry.Scheme.Hom.formsTensorTerm g (deRhamCohomologySheaf f q) p :=
  rfl

end Stacks.DeRhamSmooth
