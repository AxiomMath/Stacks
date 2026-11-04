module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPushforwardQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackOpenImmersionSupport
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Stacks.ObjectPropertyOpenImmersion

/-!
# The direct image along an open immersion is an open immersion of stacks (Stacks 0DNA)

Let `B` be an algebraic space and let `π : X ⟶ Y` be an open immersion of algebraic spaces which
are separated and of finite presentation over `B`.  Stacks 0DNA asserts that the morphism
`Coh_{X/B} ⟶ Coh_{Y/B}` of Stacks 0DN9, `(T, F) ↦ (T, π_{T,*}F)`, is an open immersion.  The
source omits the proof, with the hint that for an object `(T, G)` of `Coh_{Y/B}` the condition
`Supp(G_t) ⊆ |X_t|` on `t ∈ T` is open.  This file carries the proof out.

A 1-morphism of categories fibred in groupoids over the big fppf site is representable by
algebraic spaces and an open immersion as soon as it is fully faithful and, over every
scheme-valued point `y` of the target over a scheme `U`, its essential image is cut out by an open
subscheme of `U`
(`AlgebraicGeometry.Stack.isOpenImmersion_and_isRepresentableByAlgebraicSpaces_of_hasOpenLocus`).
Both hold here.

* **Full faithfulness.**  A morphism `(h, φ)` of `Coh_{X/B}` goes to `(h, θ_h ≫ π_{T,*}φ)` with
  `θ_h` the base change isomorphism of Stacks 0DN9, so the morphism is fully faithful as soon as
  every `π_{T,*}` is
  (`CoherentPushforwardSituation.fullyFaithfulPushforwardFunctorOfFullyFaithful`), which holds
  because `π_T` is an open immersion.
* **The essential image.**  An object `(T, G)` of `Coh_{Y/B}` is isomorphic over `T` to the image
  of an object of `Coh_{X/B}` exactly when `Supp(G) ⊆ |X_T|`.  If `G ≅ π_{T,*}F` then the support
  of `G` lies in the image of the support of `F`, closed because `Y ⟶ B` is separated.
  Conversely the restriction `π_T^*G` is an object of `Coh_{X/B}` and the unit
  `G ⟶ π_{T,*}π_T^*G` is an isomorphism.
* **The open locus.**  The condition `Supp(G) ⊆ |X_T|` is pulled back along a morphism of test
  schemes from the open locus `{t ∈ |T| : Supp(G) ∩ |Y_t| ⊆ |X_t|}` of the hint, which is open
  because `Supp(G)` is proper over `T`.

## Main definitions

* `AlgebraicGeometry.Space.CoherentPushforwardSituation.ofIsOpenImmersion`: the standing data of
  Stacks 0DN9 for an open immersion, whose quasi-finiteness is proved rather than assumed.
* `AlgebraicGeometry.Space.CoherentPushforwardSituation.restrictObject`: the restriction
  `(T, π_T^*G)` of an object of `Coh_{Y/B}` whose module is supported in `X_T`.
* `AlgebraicGeometry.Space.CoherentPushforwardSituation.toPushforwardRestrict`: the isomorphism
  `(T, G) ⟶ (T, π_{T,*}π_T^*G)` lying over the identity.

## Main results

* `AlgebraicGeometry.Space.CoherentPushforwardSituation.fullyFaithfulPushforwardFunctor`: the
  morphism of Stacks 0DN9 is fully faithful when `π` is an open immersion.
* `CoherentPushforwardSituation.exists_twoFibreProductFst_pushforwardBased_iff`: its essential
  image is the objects whose module is supported in `X_T`.
* `AlgebraicGeometry.Space.CoherentPushforwardSituation.hasOpenLocus_pushforwardBased`: that
  essential image is cut out by an open subscheme on every scheme-valued point.
* `AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_and_isOpenImmersion_cohPushforward`:
  **Stacks 0DNA.**

## Implementation notes

The morphism of Stacks 0DN9 is a 1-morphism of categories over the big fppf site,
`AlgebraicGeometry.Space.CoherentPushforwardSituation.cohPushforward`; both its source and its
target are fibred in groupoids (Stacks 08W5), and the open-immersion predicate of Stacks 04XB is
read at the 1-morphism of categories fibred in groupoids it underlies.  The source's hypotheses
are those of `AlgebraicGeometry.Space.CoherentPushforwardSituation.ofIsOpenImmersion`: an open
immersion `π` and the separatedness and finite presentation of `X` and `Y` over `B`, the
structure morphism of `X` being `π` followed by that of `Y`.  Separatedness of `Y ⟶ B` is what
puts the support of a direct image `π_{T,*}F` inside `|X_T|`.

Full faithfulness compares module comparisons over two base maps which agree only after
unfolding a definition.  Each such comparison is made heterogeneously, through a lemma
quantified over the base maps and proved by substitution
(`AlgebraicGeometry.Space.CoherentPushforwardSituation.heq_baseChangeIso_hom_comp_map`,
`AlgebraicGeometry.Space.CoherentPushforwardSituation.heq_of_heq_baseChangeIso_hom_comp_map`),
rather than by unfolding beneath the types of the two comparisons, which does not terminate
within the heartbeat budget.

## References

* [Stacks Project, Tag 0DNA](https://stacks.math.columbia.edu/tag/0DNA)
* [Stacks Project, Tag 0DN9](https://stacks.math.columbia.edu/tag/0DN9)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 08W5](https://stacks.math.columbia.edu/tag/08W5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace CoherentPushforwardSituation

variable {D : CoherentPushforwardSituation B S hS}

/-- The base change `π_T` of an open immersion is an open immersion. -/
theorem isOpenImmersion_mapAt (hopen : IsOpenImmersion B S hS D.π.hom) (T : SchemesOver D.base) :
    IsOpenImmersion B S hS (D.mapAt T).hom :=
  D.target.isOpenImmersion_baseChangeOfMap rfl hopen T

/-- The direct image `π_{T,*}` along the base change of an open immersion is fully faithful. -/
def fullyFaithfulPushforwardAt (hopen : IsOpenImmersion B S hS D.π.hom)
    (T : SchemesOver D.base) : (modulePushforward B S hS (D.mapAt T)).FullyFaithful :=
  fullyFaithfulModulePushforwardOfIsOpenImmersion B S hS (D.mapAt T)
    (isOpenImmersion_mapAt hopen T)

variable (H : D.PreservesCoherence) (hopen : IsOpenImmersion B S hS D.π.hom)

/-! ### Full faithfulness -/

/-- The base change map `θ_h` of Stacks 0DN9 at the module of an object of `Coh_{X/B}`, as an
isomorphism (claim (b)). -/
def baseChangeIso (A' : CoherentObject D.source) {T : SchemesOver D.base} (h : T ⟶ A'.T) :
    (modulePullback B S hS (D.target.relativeMap h)).obj
        ((modulePushforward B S hS (D.mapAt A'.T)).obj A'.F) ≅
      (modulePushforward B S hS (D.mapAt T)).obj
        ((modulePullback B S hS (D.source.relativeMap h)).obj A'.F) :=
  @asIso _ _ _ _ ((D.baseChange h).app A'.F) (H.isIso_baseChange A' h)

/-- The module comparison of the image of a morphism, through
`AlgebraicGeometry.Space.CoherentPushforwardSituation.baseChangeIso`. -/
theorem pushforwardHom_fibre_eq {A A' : CoherentObject D.source} (m : CoherentHom A A') :
    (pushforwardHom H m).fibre =
      (baseChangeIso H A' m.base).hom ≫ (modulePushforward B S hS (D.mapAt A.T)).map m.fibre :=
  rfl

/-! ### Full faithfulness when every base changed direct image is fully faithful

If for every test scheme `T` the direct image `π_{T,*}` along the base change `π_T : X_T ⟶ Y_T`
is fully faithful, then so is the morphism `Coh_{X/B} ⟶ Coh_{Y/B}` of Stacks 0DN9: a morphism
`(h, ψ) : (T, π_{T,*}ℱ) ⟶ (T', π_{T',*}ℱ')` of `Coh_{Y/B}` comes from the unique `(h, φ)` with
`π_{T,*}φ = θ_h⁻¹ ≫ ψ`.  This holds for an open immersion `π` (below) and for a closed
immersion `π` (Stacks 04CJ), the cases of Stacks 0DNA and Stacks 0DNB. -/

section OfFullyFaithful

variable (hff : ∀ T : SchemesOver D.base, (modulePushforward B S hS (D.mapAt T)).FullyFaithful)

/-- The module comparison of the preimage of a morphism `(h, ψ)` of `Coh_{Y/B}` between two
direct images: the morphism `φ` with `π_{T,*}φ = θ_h⁻¹ ≫ ψ`. -/
def preimageFibreOfFullyFaithful {A A' : CoherentObject D.source} (h : A.T ⟶ A'.T)
    (ψ : (modulePullback B S hS (D.target.relativeMap h)).obj
      ((modulePushforward B S hS (D.mapAt A'.T)).obj A'.F) ⟶
      (modulePushforward B S hS (D.mapAt A.T)).obj A.F) :
    (modulePullback B S hS (D.source.relativeMap h)).obj A'.F ⟶ A.F :=
  (hff A.T).preimage ((baseChangeIso H A' h).inv ≫ ψ)

/-- The direct image of the preimage comparison is `θ_h⁻¹ ≫ ψ`. -/
theorem map_preimageFibreOfFullyFaithful {A A' : CoherentObject D.source} (h : A.T ⟶ A'.T)
    (ψ : (modulePullback B S hS (D.target.relativeMap h)).obj
      ((modulePushforward B S hS (D.mapAt A'.T)).obj A'.F) ⟶
      (modulePushforward B S hS (D.mapAt A.T)).obj A.F) :
    (modulePushforward B S hS (D.mapAt A.T)).map (preimageFibreOfFullyFaithful H hff h ψ) =
      (baseChangeIso H A' h).inv ≫ ψ :=
  Functor.FullyFaithful.map_preimage _ _

/-- The preimage comparison of an isomorphism is an isomorphism. -/
theorem isIso_preimageFibreOfFullyFaithful {A A' : CoherentObject D.source} (h : A.T ⟶ A'.T)
    (ψ : (modulePullback B S hS (D.target.relativeMap h)).obj
      ((modulePushforward B S hS (D.mapAt A'.T)).obj A'.F) ⟶
      (modulePushforward B S hS (D.mapAt A.T)).obj A.F) (hψ : IsIso ψ) :
    IsIso (preimageFibreOfFullyFaithful H hff h ψ) := by
  have : IsIso ((modulePushforward B S hS (D.mapAt A.T)).map
      (preimageFibreOfFullyFaithful H hff h ψ)) := by
    rw [map_preimageFibreOfFullyFaithful]
    infer_instance
  exact (hff A.T).isIso_of_isIso_map _

/-- The image comparison `θ_h ≫ π_{T,*}φ` of the preimage comparison of `ψ` is `ψ`. -/
theorem baseChangeIso_hom_comp_map_preimageFibreOfFullyFaithful {A A' : CoherentObject D.source}
    (h : A.T ⟶ A'.T)
    (ψ : (modulePullback B S hS (D.target.relativeMap h)).obj
      ((modulePushforward B S hS (D.mapAt A'.T)).obj A'.F) ⟶
      (modulePushforward B S hS (D.mapAt A.T)).obj A.F) :
    (baseChangeIso H A' h).hom ≫
      (modulePushforward B S hS (D.mapAt A.T)).map (preimageFibreOfFullyFaithful H hff h ψ) =
        ψ := by
  rw [map_preimageFibreOfFullyFaithful, Iso.hom_inv_id_assoc]

/-- The preimage comparison of an image comparison `θ_h ≫ π_{T,*}φ` is `φ`. -/
theorem preimageFibreOfFullyFaithful_baseChangeIso_hom_comp_map {A A' : CoherentObject D.source}
    (h : A.T ⟶ A'.T) (φ : (modulePullback B S hS (D.source.relativeMap h)).obj A'.F ⟶ A.F) :
    preimageFibreOfFullyFaithful H hff h
      ((baseChangeIso H A' h).hom ≫ (modulePushforward B S hS (D.mapAt A.T)).map φ) = φ := by
  apply (hff A.T).map_injective
  rw [map_preimageFibreOfFullyFaithful, Iso.inv_hom_id_assoc]

/-- The preimage of a morphism `(h, ψ) : (T, π_{T,*}F) ⟶ (T', π_{T',*}F')` of `Coh_{Y/B}`: the
morphism `(h, φ)` of `Coh_{X/B}` with `π_{T,*}φ = θ_h⁻¹ ≫ ψ`. -/
def pushforwardPreimageOfFullyFaithful {A A' : CoherentObject D.source}
    (n : CoherentHom (pushforwardObject H A) (pushforwardObject H A')) : CoherentHom A A' where
  base := n.base
  fibre := preimageFibreOfFullyFaithful H hff n.base n.fibre
  isIso_fibre := isIso_preimageFibreOfFullyFaithful H hff n.base n.fibre n.isIso_fibre

/-- The preimage of a morphism keeps its base map. -/
theorem pushforwardPreimageOfFullyFaithful_base {A A' : CoherentObject D.source}
    (n : CoherentHom (pushforwardObject H A) (pushforwardObject H A')) :
    (pushforwardPreimageOfFullyFaithful H hff n).base = n.base :=
  rfl

/-- The module comparison of the preimage of a morphism is its preimage comparison. -/
theorem pushforwardPreimageOfFullyFaithful_fibre {A A' : CoherentObject D.source}
    (n : CoherentHom (pushforwardObject H A) (pushforwardObject H A')) :
    (pushforwardPreimageOfFullyFaithful H hff n).fibre =
      preimageFibreOfFullyFaithful H hff n.base n.fibre :=
  rfl

/-- A morphism of `Coh_{X/B}` whose base map and module comparison are those of the preimage of
`(b, ψ)` has image `(b, ψ)` on module comparisons. -/
theorem heq_baseChangeIso_hom_comp_map_of_fullyFaithful {A A' : CoherentObject D.source}
    (m : CoherentHom A A')
    (b : A.T ⟶ A'.T)
    (ψ : (modulePullback B S hS (D.target.relativeMap b)).obj (pushforwardObject H A').F ⟶
      (pushforwardObject H A).F)
    (hb : m.base = b) (hf : HEq m.fibre (preimageFibreOfFullyFaithful H hff b ψ)) :
    HEq ((baseChangeIso H A' m.base).hom ≫
      (modulePushforward B S hS (D.mapAt A.T)).map m.fibre) ψ := by
  subst hb
  rw [eq_of_heq hf]
  exact heq_of_eq (baseChangeIso_hom_comp_map_preimageFibreOfFullyFaithful H hff m.base ψ)

/-- The image of the preimage of a morphism is that morphism. -/
theorem pushforwardHom_pushforwardPreimageOfFullyFaithful {A A' : CoherentObject D.source}
    (n : CoherentHom (pushforwardObject H A) (pushforwardObject H A')) :
    pushforwardHom H (pushforwardPreimageOfFullyFaithful H hff n) = n :=
  coherentHom_eq_of_heq rfl ((heq_of_eq (pushforwardHom_fibre_eq H _)).trans
    (heq_baseChangeIso_hom_comp_map_of_fullyFaithful H hff _ n.base n.fibre
      (pushforwardPreimageOfFullyFaithful_base H hff n)
      (heq_of_eq (pushforwardPreimageOfFullyFaithful_fibre H hff n))))

include hff in
/-- The composite `θ_b ≫ π_{T,*}φ` determines `φ`, read heterogeneously along an equality of base
maps: `π_{T,*}` is faithful and `θ_b` is invertible. -/
theorem heq_of_heq_baseChangeIso_hom_comp_map_of_fullyFaithful {A A' : CoherentObject D.source}
    {b b' : A.T ⟶ A'.T} (hb : b = b')
    (φ : (modulePullback B S hS (D.source.relativeMap b)).obj A'.F ⟶ A.F)
    (φ' : (modulePullback B S hS (D.source.relativeMap b')).obj A'.F ⟶ A.F)
    (h : HEq ((baseChangeIso H A' b).hom ≫ (modulePushforward B S hS (D.mapAt A.T)).map φ)
      ((baseChangeIso H A' b').hom ≫ (modulePushforward B S hS (D.mapAt A.T)).map φ')) :
    HEq φ φ' := by
  subst hb
  exact heq_of_eq ((hff A.T).map_injective
    (((baseChangeIso H A' b).cancel_iso_hom_left _ _).1 (eq_of_heq h)))

include hff in
/-- **The morphism of Stacks 0DN9 is injective on morphisms when every `π_{T,*}` is fully
faithful.** -/
theorem pushforwardHom_injective_of_fullyFaithful {A A' : CoherentObject D.source}
    (m m' : CoherentHom A A')
    (h : pushforwardHom H m = pushforwardHom H m') : m = m' := by
  have hb : m.base = m'.base :=
    (pushforwardHom_base H m).symm.trans ((congrArg CoherentHom.base h).trans
      (pushforwardHom_base H m'))
  refine coherentHom_eq_of_heq hb
    (heq_of_heq_baseChangeIso_hom_comp_map_of_fullyFaithful H hff hb m.fibre m'.fibre ?_)
  exact (heq_of_eq (pushforwardHom_fibre_eq H m)).symm.trans
    ((congr_arg_heq CoherentHom.fibre h).trans (heq_of_eq (pushforwardHom_fibre_eq H m')))

/-- The preimage of the image of a morphism is that morphism. -/
theorem pushforwardPreimageOfFullyFaithful_pushforwardHom {A A' : CoherentObject D.source}
    (m : CoherentHom A A') : pushforwardPreimageOfFullyFaithful H hff (pushforwardHom H m) = m :=
  pushforwardHom_injective_of_fullyFaithful H hff _ _
    (pushforwardHom_pushforwardPreimageOfFullyFaithful H hff _)

/-- **The morphism of Stacks 0DN9 is fully faithful when every `π_{T,*}` is.** -/
def fullyFaithfulPushforwardFunctorOfFullyFaithful :
    letI : Category.{u + 1} (CoherentObject D.source) := D.source.categoryData.category
    letI : Category.{u + 1} (CoherentObject D.target) := D.target.categoryData.category
    (pushforwardFunctor H).FullyFaithful :=
  letI : Category.{u + 1} (CoherentObject D.source) := D.source.categoryData.category
  letI : Category.{u + 1} (CoherentObject D.target) := D.target.categoryData.category
  { preimage := fun {A A'} (n : CoherentHom (pushforwardObject H A) (pushforwardObject H A')) =>
      pushforwardPreimageOfFullyFaithful H hff n
    map_preimage := fun {A A'} (n : CoherentHom (pushforwardObject H A) (pushforwardObject H A')) =>
      pushforwardHom_pushforwardPreimageOfFullyFaithful H hff n
    preimage_map := fun {A A'} (m : CoherentHom A A') =>
      pushforwardPreimageOfFullyFaithful_pushforwardHom H hff m }

end OfFullyFaithful

/-! ### Full faithfulness along an open immersion -/

/-- The module comparison of the preimage of a morphism `(h, ψ)` of `Coh_{Y/B}` between two
direct images: the morphism `φ` with `π_{T,*}φ = θ_h⁻¹ ≫ ψ`. -/
def preimageFibre {A A' : CoherentObject D.source} (h : A.T ⟶ A'.T)
    (ψ : (modulePullback B S hS (D.target.relativeMap h)).obj
      ((modulePushforward B S hS (D.mapAt A'.T)).obj A'.F) ⟶
      (modulePushforward B S hS (D.mapAt A.T)).obj A.F) :
    (modulePullback B S hS (D.source.relativeMap h)).obj A'.F ⟶ A.F :=
  preimageFibreOfFullyFaithful H (fullyFaithfulPushforwardAt hopen) h ψ

/-- The direct image of the preimage comparison is `θ_h⁻¹ ≫ ψ`. -/
theorem map_preimageFibre {A A' : CoherentObject D.source} (h : A.T ⟶ A'.T)
    (ψ : (modulePullback B S hS (D.target.relativeMap h)).obj
      ((modulePushforward B S hS (D.mapAt A'.T)).obj A'.F) ⟶
      (modulePushforward B S hS (D.mapAt A.T)).obj A.F) :
    (modulePushforward B S hS (D.mapAt A.T)).map (preimageFibre H hopen h ψ) =
      (baseChangeIso H A' h).inv ≫ ψ :=
  map_preimageFibreOfFullyFaithful H (fullyFaithfulPushforwardAt hopen) h ψ

/-- The preimage comparison of an isomorphism is an isomorphism. -/
theorem isIso_preimageFibre {A A' : CoherentObject D.source} (h : A.T ⟶ A'.T)
    (ψ : (modulePullback B S hS (D.target.relativeMap h)).obj
      ((modulePushforward B S hS (D.mapAt A'.T)).obj A'.F) ⟶
      (modulePushforward B S hS (D.mapAt A.T)).obj A.F) (hψ : IsIso ψ) :
    IsIso (preimageFibre H hopen h ψ) :=
  isIso_preimageFibreOfFullyFaithful H (fullyFaithfulPushforwardAt hopen) h ψ hψ

/-- The image comparison `θ_h ≫ π_{T,*}φ` of the preimage comparison of `ψ` is `ψ`. -/
theorem baseChangeIso_hom_comp_map_preimageFibre {A A' : CoherentObject D.source}
    (h : A.T ⟶ A'.T)
    (ψ : (modulePullback B S hS (D.target.relativeMap h)).obj
      ((modulePushforward B S hS (D.mapAt A'.T)).obj A'.F) ⟶
      (modulePushforward B S hS (D.mapAt A.T)).obj A.F) :
    (baseChangeIso H A' h).hom ≫
      (modulePushforward B S hS (D.mapAt A.T)).map (preimageFibre H hopen h ψ) = ψ :=
  baseChangeIso_hom_comp_map_preimageFibreOfFullyFaithful H (fullyFaithfulPushforwardAt hopen) h ψ

/-- The preimage comparison of an image comparison `θ_h ≫ π_{T,*}φ` is `φ`. -/
theorem preimageFibre_baseChangeIso_hom_comp_map {A A' : CoherentObject D.source}
    (h : A.T ⟶ A'.T) (φ : (modulePullback B S hS (D.source.relativeMap h)).obj A'.F ⟶ A.F) :
    preimageFibre H hopen h
      ((baseChangeIso H A' h).hom ≫ (modulePushforward B S hS (D.mapAt A.T)).map φ) = φ :=
  preimageFibreOfFullyFaithful_baseChangeIso_hom_comp_map H (fullyFaithfulPushforwardAt hopen) h φ

/-- The preimage of a morphism `(h, ψ) : (T, π_{T,*}F) ⟶ (T', π_{T',*}F')` of `Coh_{Y/B}`: the
morphism `(h, φ)` of `Coh_{X/B}` with `π_{T,*}φ = θ_h⁻¹ ≫ ψ`. -/
def pushforwardPreimage {A A' : CoherentObject D.source}
    (n : CoherentHom (pushforwardObject H A) (pushforwardObject H A')) : CoherentHom A A' :=
  pushforwardPreimageOfFullyFaithful H (fullyFaithfulPushforwardAt hopen) n

/-- The preimage of a morphism keeps its base map. -/
theorem pushforwardPreimage_base {A A' : CoherentObject D.source}
    (n : CoherentHom (pushforwardObject H A) (pushforwardObject H A')) :
    (pushforwardPreimage H hopen n).base = n.base :=
  rfl

/-- The module comparison of the preimage of a morphism is its preimage comparison. -/
theorem pushforwardPreimage_fibre {A A' : CoherentObject D.source}
    (n : CoherentHom (pushforwardObject H A) (pushforwardObject H A')) :
    (pushforwardPreimage H hopen n).fibre = preimageFibre H hopen n.base n.fibre :=
  rfl

/-- A morphism of `Coh_{X/B}` whose base map and module comparison are those of the preimage of
`(b, ψ)` has image `(b, ψ)` on module comparisons. -/
theorem heq_baseChangeIso_hom_comp_map {A A' : CoherentObject D.source} (m : CoherentHom A A')
    (b : A.T ⟶ A'.T)
    (ψ : (modulePullback B S hS (D.target.relativeMap b)).obj (pushforwardObject H A').F ⟶
      (pushforwardObject H A).F)
    (hb : m.base = b) (hf : HEq m.fibre (preimageFibre H hopen b ψ)) :
    HEq ((baseChangeIso H A' m.base).hom ≫
      (modulePushforward B S hS (D.mapAt A.T)).map m.fibre) ψ :=
  heq_baseChangeIso_hom_comp_map_of_fullyFaithful H (fullyFaithfulPushforwardAt hopen) m b ψ hb hf

/-- The image of the preimage of a morphism is that morphism. -/
theorem pushforwardHom_pushforwardPreimage {A A' : CoherentObject D.source}
    (n : CoherentHom (pushforwardObject H A) (pushforwardObject H A')) :
    pushforwardHom H (pushforwardPreimage H hopen n) = n :=
  pushforwardHom_pushforwardPreimageOfFullyFaithful H (fullyFaithfulPushforwardAt hopen) n

include hopen in
/-- The composite `θ_b ≫ π_{T,*}φ` determines `φ`, read heterogeneously along an equality of base
maps: `π_{T,*}` is faithful and `θ_b` is invertible. -/
theorem heq_of_heq_baseChangeIso_hom_comp_map {A A' : CoherentObject D.source}
    {b b' : A.T ⟶ A'.T} (hb : b = b')
    (φ : (modulePullback B S hS (D.source.relativeMap b)).obj A'.F ⟶ A.F)
    (φ' : (modulePullback B S hS (D.source.relativeMap b')).obj A'.F ⟶ A.F)
    (h : HEq ((baseChangeIso H A' b).hom ≫ (modulePushforward B S hS (D.mapAt A.T)).map φ)
      ((baseChangeIso H A' b').hom ≫ (modulePushforward B S hS (D.mapAt A.T)).map φ')) :
    HEq φ φ' :=
  heq_of_heq_baseChangeIso_hom_comp_map_of_fullyFaithful H (fullyFaithfulPushforwardAt hopen) hb
    φ φ' h

include hopen in
/-- **The morphism of Stacks 0DN9 is injective on morphisms along an open immersion.** -/
theorem pushforwardHom_injective {A A' : CoherentObject D.source} (m m' : CoherentHom A A')
    (h : pushforwardHom H m = pushforwardHom H m') : m = m' :=
  pushforwardHom_injective_of_fullyFaithful H (fullyFaithfulPushforwardAt hopen) m m' h

/-- The preimage of the image of a morphism is that morphism. -/
theorem pushforwardPreimage_pushforwardHom {A A' : CoherentObject D.source}
    (m : CoherentHom A A') : pushforwardPreimage H hopen (pushforwardHom H m) = m :=
  pushforwardPreimageOfFullyFaithful_pushforwardHom H (fullyFaithfulPushforwardAt hopen) m

/-- **The morphism of Stacks 0DN9 is fully faithful along an open immersion.** -/
def fullyFaithfulPushforwardFunctor :
    letI : Category.{u + 1} (CoherentObject D.source) := D.source.categoryData.category
    letI : Category.{u + 1} (CoherentObject D.target) := D.target.categoryData.category
    (pushforwardFunctor H).FullyFaithful :=
  fullyFaithfulPushforwardFunctorOfFullyFaithful H (fullyFaithfulPushforwardAt hopen)

/-! ### The restriction of an object supported in `X_T` -/

/-- **The restriction `(T, π_T^*G)` of an object `(T, G)` of `Coh_{Y/B}` whose module is supported
in `X_T`**, an object of `Coh_{X/B}`. -/
def restrictObject (A : CoherentObject D.target)
    (hsupp : D.target.support A.T A.F ⊆
      Set.range (pointsMap B S hS (D.source.space A.T).1 (D.mapAt A.T).hom)) :
    CoherentObject D.source where
  T := A.T
  F := (modulePullback B S hS (D.mapAt A.T)).obj A.F
  quasicoherent :=
    haveI := isFinitePresentationOnSite_modulePullback B S hS (D.mapAt A.T) A.F
      A.finitePresentation
    inferInstance
  finitePresentation :=
    isFinitePresentationOnSite_modulePullback B S hS (D.mapAt A.T) A.F A.finitePresentation
  flat :=
    haveI := A.quasicoherent
    D.target.isFlatOver_modulePullback_baseChangeOfMap (π := D.π) (bX := D.π ≫ D.f) rfl hopen
      A.T A.F A.flat
  properSupport := by
    obtain ⟨hp, hU, hproper⟩ := A.properSupport
    have := A.quasicoherent
    have := A.finitePresentation
    have hcomp : (D.mapAt A.T).hom ≫ (D.target.projection A.T).hom =
        (D.source.projection A.T).hom :=
      congrArg (fun m => m.hom) (D.mapAt_comp_projection A.T)
    have hpX : IsLocallyOfFiniteType B S hS (D.source.projection A.T).hom :=
      hcomp ▸ isLocallyOfFiniteType_comp' B S hS _ _ (D.target.space A.T).2
        ((schemeSpaceFunctor B S hS).obj A.T.left).2
        (isLocallyOfFiniteType_of_isEtale' B S hS _
          (isEtale_of_isOpenImmersion B S hS (isOpenImmersion_mapAt hopen A.T))) hp
    have hU' := isClosed_supportOfSheaf_modulePullback B S hS (D.mapAt A.T) A.F inferInstance
    exact ⟨hpX, hU', D.target.isProperOver_supportOfSheaf_modulePullback_baseChangeOfMap
      (π := D.π) (bX := D.π ≫ D.f) rfl hopen A.T A.F hp hpX hU hproper hsupp hU'⟩

include hopen in
/-- The unit `G ⟶ π_{T,*}π_T^*G` is an isomorphism when `G` is supported in `X_T`. -/
theorem isIso_unit_mapAt (A : CoherentObject D.target)
    (hsupp : D.target.support A.T A.F ⊆
      Set.range (pointsMap B S hS (D.source.space A.T).1 (D.mapAt A.T).hom)) :
    IsIso ((modulePullbackAdjunction B S hS (D.mapAt A.T)).unit.app A.F) :=
  isIso_modulePullbackAdjunction_unit_of_supportOfSheaf_subset B S hS (D.mapAt A.T)
    (isOpenImmersion_mapAt hopen A.T) A.F (D.target.isClosed_support A) hsupp

/-- **A module supported in `X_T` is the direct image of its restriction**: the unit
`G ⟶ π_{T,*}π_T^*G` as an isomorphism. -/
def restrictUnitIso (A : CoherentObject D.target)
    (hsupp : D.target.support A.T A.F ⊆
      Set.range (pointsMap B S hS (D.source.space A.T).1 (D.mapAt A.T).hom)) :
    A.F ≅ (modulePushforward B S hS (D.mapAt A.T)).obj
      ((modulePullback B S hS (D.mapAt A.T)).obj A.F) :=
  haveI := isIso_unit_mapAt hopen A hsupp
  asIso ((modulePullbackAdjunction B S hS (D.mapAt A.T)).unit.app A.F)

/-- **The comparison `(T, G) ⟶ (T, π_{T,*}π_T^*G)`**, lying over the identity of `T`: its module
comparison is the inverse of the unit `G ⟶ π_{T,*}π_T^*G`, an isomorphism because `G` is
supported in `X_T`. -/
def toPushforwardRestrict (A : CoherentObject D.target)
    (hsupp : D.target.support A.T A.F ⊆
      Set.range (pointsMap B S hS (D.source.space A.T).1 (D.mapAt A.T).hom)) :
    CoherentHom A (pushforwardObject H (restrictObject hopen A hsupp)) where
  base := 𝟙 A.T
  fibre := ((D.target.idComparison (modulePushforwardCoherence B S hS) A.T).app
      ((modulePushforward B S hS (D.mapAt A.T)).obj
        ((modulePullback B S hS (D.mapAt A.T)).obj A.F)) ≪≫
    (restrictUnitIso hopen A hsupp).symm).hom
  isIso_fibre := Iso.isIso_hom _

/-! ### The essential image -/

/-- The support of the source of a morphism of `Coh_{Y/B}` is the inverse image of the support of
its target. -/
private theorem support_eq_preimage_of_hom {E P : CoherentObject D.target} (m : CoherentHom E P) :
    D.target.support E.T E.F =
      pointsMap B S hS (D.target.space E.T).1 (D.target.relativeMap m.base).hom ⁻¹'
        D.target.support P.T P.F := by
  have hm : IsIso m.fibre := m.isIso_fibre
  have := P.quasicoherent
  have := P.finitePresentation
  rw [← supportOfSheaf_modulePullback_eq B S hS (D.target.relativeMap m.base) P.F
    inferInstance inferInstance]
  exact (supportOfSheaf_eq_of_iso B S hS _ (asIso m.fibre)).symm

/-- **An object of `Coh_{Y/B}` receiving a morphism to a direct image is supported in `X_T`.**
If `(h, ψ) : (T, G) ⟶ (T', π_{T',*}F)` is a morphism of `Coh_{Y/B}`, then the support of `G` —
the inverse image under `Y_h` of the support of `π_{T',*}F`, `ψ` being an isomorphism — lies in
`|X_T|`, because the support of `π_{T',*}F` lies in `|X_{T'}|` (`Y ⟶ B` being separated). -/
theorem support_subset_range_of_hom (E : CoherentObject D.target) (A₀ : CoherentObject D.source)
    (m : CoherentHom E (pushforwardObject H A₀)) :
    D.target.support E.T E.F ⊆
      Set.range (pointsMap B S hS (D.source.space E.T).1 (D.mapAt E.T).hom) := by
  let P := pushforwardObject H A₀
  obtain ⟨hpX, hU, hproper⟩ := A₀.properSupport
  obtain ⟨hpY, -, -⟩ := P.properSupport
  have h₂ : D.target.support P.T P.F ⊆
      Set.range (pointsMap B S hS (D.source.space A₀.T).1 (D.mapAt A₀.T).hom) :=
    D.target.supportOfSheaf_modulePushforward_subset_range (π := D.π) (bX := D.π ≫ D.f) rfl
      D.separated_target A₀.T A₀.F hpX hpY hU hproper
  rw [support_eq_preimage_of_hom m]
  exact (Set.preimage_mono h₂).trans
    (D.target.preimage_range_baseChangeOfMap_subset (π := D.π) (bX := D.π ≫ D.f) rfl m.base)


include hopen in
/-- **The essential image of the morphism of Stacks 0DN9 along an open immersion.**  An object
`T` of the big fppf site of `U` is in the image of the first projection of the 2-fibre product of
`Coh_{X/B} ⟶ Coh_{Y/B}` with a scheme-valued point `y` exactly when the module of `y(T)` is
supported in `X_T`. -/
theorem exists_twoFibreProductFst_pushforwardBased_iff (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ (coherentBasedCategory D.target.categoryData).obj)
    (hy : y ⋙ (coherentBasedCategory D.target.categoryData).p = Over.map U.hom)
    (T : BigFppfOver B U.left.1 U.left.2) :
    (∃ a, (TwoFibreProductOver.fst (Over.map U.hom)
        (coherentBasedCategory D.source.categoryData).p
        (coherentBasedCategory D.target.categoryData).p y
        (pushforwardBased H).toFunctor).obj a = T) ↔
      D.target.support (CoherentObject.T (D := D.target) (y.obj T))
          (CoherentObject.F (D := D.target) (y.obj T)) ⊆
        Set.range (pointsMap B S hS (D.source.space (CoherentObject.T (D := D.target) (y.obj T))).1
          (D.mapAt (CoherentObject.T (D := D.target) (y.obj T))).hom) := by
  constructor
  · rintro ⟨a, rfl⟩
    exact support_subset_range_of_hom H (y.obj a.x) a.y a.iso.hom
  · intro hsupp
    let R := restrictObject hopen (y.obj T) hsupp
    let : Category.{u + 1} (CoherentObject D.target) := D.target.categoryData.category
    let φ : y.obj T ⟶ pushforwardObject H R := toPushforwardRestrict H hopen (y.obj T) hsupp
    have hlift' : (D.target.categoryData.projection ⋙
        CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.target.Y).IsHomLift
          (𝟙 (CoherentObject.T (D := D.target) (y.obj T)).left) φ := by
      have : (D.target.categoryData.projection ⋙
          CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.target.Y).map φ =
            𝟙 (CoherentObject.T (D := D.target) (y.obj T)).left := rfl
      rw [← this]
      exact Functor.IsHomLift.map (p := D.target.categoryData.projection ⋙
        CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.target.Y) φ
    have hiso : IsIso φ := Functor.isIso_of_isHomLift_id' _
      D.target.projection_isFiberedInGroupoids φ hlift'
    have hp : (D.target.categoryData.projection ⋙
        CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.target.Y) =
          (coherentBasedCategory D.target.categoryData).p :=
      coherentSiteProjection_eq D.target.categoryData
    have hlift : (coherentBasedCategory D.target.categoryData).p.IsHomLift
        (𝟙 ((coherentBasedCategory D.target.categoryData).p.obj (y.obj T))) φ := by
      rw [← hp]
      exact hlift'
    exact ⟨{ base := (coherentBasedCategory D.target.categoryData).p.obj (y.obj T)
             x := T
             y := R
             hx := (Functor.congr_obj hy T).symm
             hy := rfl
             iso := @asIso _ _ _ _ φ hiso
             vertical := hlift }, rfl⟩

/-! ### The open locus -/

include hopen in
/-- **Stacks 0DNA, the open locus.**  For every scheme-valued point `y` of `Coh_{Y/B}` over an
object `U` of the big fppf site of `S`, there is an open subscheme `V ⊆ U` through which an object
`T` of the big fppf site of `U` factors exactly when `y(T)` comes from `Coh_{X/B}`.

`V` is the open subscheme on the locus `{t ∈ |T₀| : Supp(G) ∩ |Y_t| ⊆ |X_t|}` of the source's
hint, where `(T₀, G) = y(U)`, transported to the scheme of `U`. -/
theorem hasOpenLocus_pushforwardBased :
    Stack.HasOpenLocus B S hS (pushforwardBased H) := by
  intro U y hy
  let U₀ : BigFppfOver B U.left.1 U.left.2 := Over.mk (𝟙 _)
  let A : CoherentObject D.target := y.obj U₀
  let Ω := D.target.supportLocus (π := D.π) (bX := D.π ≫ D.f) rfl A.T A.F
  have hΩ : IsOpen Ω := D.target.isOpen_supportLocus (π := D.π) (bX := D.π ≫ D.f) rfl hopen A
  let O : Set ((BigFppfOver.toScheme B S hS).obj A.T.left) :=
    pointsToScheme B S hS A.T.left '' Ω
  have hO : IsOpen O := (schemePointsHomeomorph B S hS A.T.left).isOpenMap Ω hΩ
  have hA : (BigFppfOver.toScheme B S hS).obj A.T.left =
      (BigFppfOver.toScheme B S hS).obj ((Over.map U.hom).obj U₀) :=
    congrArg (BigFppfOver.toScheme B S hS).obj (Functor.congr_obj hy U₀)
  let e₀ : (BigFppfOver.toScheme B S hS).obj ((Over.map U.hom).obj U₀) ⟶
      (BigFppfOver.toScheme B S hS).obj A.T.left := eqToHom hA.symm
  let O' : U.left.1.Opens := ⟨e₀.base ⁻¹' O, hO.preimage e₀.base.hom.continuous⟩
  refine ⟨BigFppfOver.opensObj B U.left.1 U.left.2 O', ?_, fun T => ?_⟩
  · rw [BigFppfOver.opensObj_hom_hom]
    infer_instance
  · rw [nonempty_hom_opensObj_iff, exists_twoFibreProductFst_pushforwardBased_iff H hopen U y hy T]
    let t : T ⟶ U₀ := Over.homMk T.hom (Category.comp_id _)
    let m : CoherentHom (D := D.target) (y.obj T) A := y.map t
    rw [support_eq_preimage_of_hom m]
    refine Iff.trans ?_
      (D.target.range_subset_supportLocus_iff (π := D.π) (bX := D.π ≫ D.f) rfl m.base A.F)
    show _ ↔ Set.range (pointsMap B S hS
      (yoneda.obj (CoherentObject.T (D := D.target) (y.obj T)).left)
      (yoneda.map m.base.left)) ⊆ Ω
    rw [range_pointsMap_yoneda_subset_iff B S hS m.base.left Ω]
    have h₃ := congrArg (fun k => (BigFppfOver.toScheme B S hS).map k) (Functor.congr_hom hy t)
    simp only [Functor.map_comp, eqToHom_map] at h₃
    exact (range_subset_iff_of_eq_eqToHom _ hA _ _ h₃ O).symm

/-! ### Stacks 0DNA -/

include hopen in
/-- **The morphism of Stacks 0DN9 along an open immersion is representable by algebraic spaces and
an open immersion**, for any claims (a) and (b) of the proof of Stacks 0DN9: it is fully faithful
and its essential image is cut out by an open subscheme on every scheme-valued point. -/
theorem isOpenImmersion_mkHom_pushforwardBased :
    Stack.IsRepresentableByAlgebraicSpaces B S hS
        (Bicategory.InducedBicategory.mkHom (pushforwardBased H) :
          coherentCFG D.source ⟶ coherentCFG D.target).hom ∧
      Stack.IsOpenImmersion B S hS
        (Bicategory.InducedBicategory.mkHom (pushforwardBased H) :
          coherentCFG D.source ⟶ coherentCFG D.target) :=
  (Stack.isOpenImmersion_and_isRepresentableByAlgebraicSpaces_of_hasOpenLocus B S hS
    (Bicategory.InducedBicategory.mkHom (pushforwardBased H) :
      coherentCFG D.source ⟶ coherentCFG D.target)
    (by
      let := D.source.categoryData.category
      let := D.target.categoryData.category
      exact (fullyFaithfulPushforwardFunctor H hopen).full)
    (by
      let := D.source.categoryData.category
      let := D.target.categoryData.category
      exact (fullyFaithfulPushforwardFunctor H hopen).faithful)
    (hasOpenLocus_pushforwardBased H hopen)).symm

end CoherentPushforwardSituation

/-- The standing data of Stacks 0DN9 for an open immersion `π : X ⟶ Y` of algebraic spaces which
are separated and of finite presentation over `B`.  An open immersion is locally quasi-finite,
being étale (Stacks 03XU), and it is quasi-compact because `X` is quasi-compact over `B` and `Y` is
quasi-separated over `B` (Stacks 03KS); so `π` is quasi-finite. -/
def CoherentPushforwardSituation.ofIsOpenImmersion {A X Y : AlgebraicSpaces B S hS}
    (π : X ⟶ Y) (f : Y ⟶ A) (hopen : IsOpenImmersion B S hS π.hom)
    (hsepX : IsSeparated B S hS (π ≫ f).hom) (hfpX : IsFinitePresentation B S hS (π ≫ f).hom)
    (hsepY : IsSeparated B S hS f.hom) (hfpY : IsFinitePresentation B S hS f.hom) :
    CoherentPushforwardSituation B S hS where
  base := A
  X := X
  Y := Y
  π := π
  f := f
  quasiFinite :=
    ⟨isLocallyQuasiFinite_of_isEtale B S hS Y.2 (isEtale_of_isOpenImmersion B S hS hopen),
      isQuasiCompact_of_comp_of_isQuasiSeparated B S hS π.hom f.hom X.2 A.2 hfpX.2.1
        (isQuasiSeparated_of_isSeparated B S hS hsepY)⟩
  separated_source := hsepX
  finitePresentation_source := hfpX
  separated_target := hsepY
  finitePresentation_target := hfpY

/-- **Stacks 0DNA.**  Let `B` be an algebraic space and let `π : X ⟶ Y` be an open immersion of
algebraic spaces which are separated and of finite presentation over `B`, the structure morphism
of `X` being `π ≫ f` for the structure morphism `f : Y ⟶ B`.  Then the morphism
`Coh_{X/B} ⟶ Coh_{Y/B}` of Stacks 0DN9,
`AlgebraicGeometry.Space.CoherentPushforwardSituation.cohPushforward`, is an open immersion: it
is representable by algebraic spaces, and every algebraic space representing its base change
along a scheme-valued point of `Coh_{Y/B}` is an open subspace of that scheme (Stacks 04XB at open
immersions), which together are Stacks 04YL (1).

The morphism is fully faithful because `π_{T,*}` is, `π_T` being an open immersion; its essential
image over a test scheme `T` is the objects `(T, G)` with `Supp(G) ⊆ |X_T|`; and over every
scheme-valued point `(T₀, G)` of `Coh_{Y/B}` that condition is cut out by the open subscheme on
`{t ∈ |T₀| : Supp(G) ∩ |Y_t| ⊆ |X_t|}`, the locus of the source's hint. -/
@[stacks 0DNA "the whole statement: for an open immersion π : X → Y of algebraic spaces \
separated and of finite presentation over B, the morphism Cohstack_{X/B} → Cohstack_{Y/B} of \
Tag 0DN9 is representable by algebraic spaces and an open immersion in the sense of Tag 04XB, \
which together are representability by open immersions (Tag 04YL (1))"]
theorem isRepresentableByAlgebraicSpaces_and_isOpenImmersion_cohPushforward
    {A X Y : AlgebraicSpaces B S hS} (π : X ⟶ Y) (f : Y ⟶ A)
    (hopen : IsOpenImmersion B S hS π.hom)
    (hsepX : IsSeparated B S hS (π ≫ f).hom) (hfpX : IsFinitePresentation B S hS (π ≫ f).hom)
    (hsepY : IsSeparated B S hS f.hom) (hfpY : IsFinitePresentation B S hS f.hom) :
    let D := CoherentPushforwardSituation.ofIsOpenImmersion π f hopen hsepX hfpX hsepY hfpY
    Stack.IsRepresentableByAlgebraicSpaces B S hS
        (Bicategory.InducedBicategory.mkHom D.cohPushforward :
          coherentCFG D.source ⟶ coherentCFG D.target).hom ∧
      Stack.IsOpenImmersion B S hS
        (Bicategory.InducedBicategory.mkHom D.cohPushforward :
          coherentCFG D.source ⟶ coherentCFG D.target) :=
  CoherentPushforwardSituation.isOpenImmersion_mkHom_pushforwardBased
    (CoherentPushforwardSituation.preservesCoherence _) hopen

end AlgebraicGeometry.Space

end
