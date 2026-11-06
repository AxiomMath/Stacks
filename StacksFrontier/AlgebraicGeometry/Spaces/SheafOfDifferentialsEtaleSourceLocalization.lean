module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivationsIntoDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleInverseImageStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHomInverseImage
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.Differentials

/-!
# Étale localization of the sheaf of differentials in the source

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and let `a : U ⟶ X` be an
*étale* morphism.  Stacks 04CU identifies the restriction of `Ω_{X/Y}` to the small étale site
of `U` — the pullback `a^*` of `𝒪_X`-modules, by the abuse of notation of Stacks' Equation 03LW
— with the sheaf of differentials of the composite:

`a^*Ω_{X/Y} ≅ Ω_{U/Y}`.

This is the first of the two steps of the source's proof, the one that
`AlgebraicGeometry.Space.sheafOfDifferentialsEtaleLocalizationIso` consumes directly; the second
step, the identification of the base, is
`AlgebraicGeometry.Space.sheafOfDifferentialsIsoOfSharpIso`.

The proof is by corepresentability, which is how this development builds every comparison of
sheaves of differentials (Stacks 04BO and 08TQ are both built this way).  Both sides corepresent
the functor of `Y`-derivations of `𝒪_U`:

* `Ω_{U/Y}` does so by its own universal property, Stacks 04CT, in the form
  `AlgebraicGeometry.Space.differentialsHomEquiv`;
* `a^*Ω_{X/Y}` does so by the composite of four bijections — the adjunction `a^* ⊣ a_*` of
  Stacks 03D7, the universal property of `Ω_{X/Y}`, the transposition of derivations along the
  morphism of small étale topoi of `a` (the module-level half of Stacks 08TQ,
  `Stacks.Sheaves.RingedToposModules.inverseImageDerivationEquiv`), and the transport of
  derivations along an isomorphism of the ring data,
  `AlgebraicGeometry.SheafOfModules.derivationEquivOfRingDataIso`.

Étaleness of `a` enters exactly once, in the last of those four bijections: it is the clause
`a^{-1}𝒪_X = 𝒪_U` of Stacks 03LV,
`AlgebraicGeometry.Space.isIso_fSharpInverseImage_of_isEtale`, which
makes the comparison of the two structure sheaves on the small étale site of `U` invertible.
That is precisely the comparison which the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsQuasicoherent.lean` record as the
missing input.  The other half of the ring data, the comparison
`a^{-1}f^{-1}𝒪_Y ≅ (a ≫ f)^{-1}𝒪_Y` together with its compatibility with the structure maps, is
the composition law of Stacks 03G8 in inverse-image form,
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_compInverseImageRingIso` and
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_compInverseImageRingIso_fSharpInverseImage`.

## Main definitions

* `AlgebraicGeometry.Space.inverseImageStructureSheafCompIso` is the comparison
  `a^{-1}f^{-1}𝒪_Y ≅ (a ≫ f)^{-1}𝒪_Y` of Stacks 03G8 at the structure sheaf of `Y`.
* `AlgebraicGeometry.Space.etaleSourcePushforward` and
  `AlgebraicGeometry.Space.etaleSourceRestrictScalars` are the two functors the transposition of
  derivations is stated at: the direct image of `𝒪_U`-modules in the untransported shape of
  Stacks 03D6, part (1), and the restriction of scalars along `a♯ : a^{-1}𝒪_X ⟶ 𝒪_U` it is built
  from.
* `AlgebraicGeometry.Space.etaleSourceAdjEquiv`,
  `AlgebraicGeometry.Space.etaleSourceTransposeEquiv` and
  `AlgebraicGeometry.Space.etaleSourceRingDataEquiv` are three of the four bijections — the
  remaining one is the universal property of `Ω_{X/Y}` — and
  `AlgebraicGeometry.Space.derivationEtalePullbackEquiv` is their composite with the universal
  property of `Ω_{X/Y}`: the morphisms `a^*Ω_{X/Y} ⟶ C` are the `Y`-derivations of `𝒪_U` with
  values in `C`.
* `AlgebraicGeometry.Space.etaleSourceLocalizationHom` and
  `AlgebraicGeometry.Space.etaleSourceLocalizationInv` are the two comparison morphisms, each
  being the morphism through which one universal derivation factors.
* `AlgebraicGeometry.Space.sheafOfDifferentialsEtaleSourceLocalizationIso` is the identification
  `a^*Ω_{X/Y} ≅ Ω_{U/Y}` itself.

## Main results

* `AlgebraicGeometry.Space.inverseImageStructureSharp_square`: the ring data of the transport is
  a commutative square — the inverse image of `f♯` followed by `a♯` is the comparison of the two
  inverse images followed by `(a ≫ f)♯`.
* `AlgebraicGeometry.Space.derivationEtalePullbackEquiv_comp`: the composite bijection is natural
  in the coefficient module, which is what makes it a corepresentation.  It is assembled from the
  naturality of its four factors, `AlgebraicGeometry.Space.etaleSourceAdjEquiv_comp`,
  `AlgebraicGeometry.Space.differentialsHomEquiv_comp`,
  `AlgebraicGeometry.Space.etaleSourceTransposeEquiv_postcomp` and
  `AlgebraicGeometry.Space.etaleSourceRingDataEquiv_postcomp`.
* `AlgebraicGeometry.Space.sheafOfDifferentialsEtaleSourceLocalizationIso`: **Stacks 04CU**, the
  étale-source localization `a^*Ω_{X/Y} ≅ Ω_{U/Y}`.
* `AlgebraicGeometry.Space.derivationEtalePullbackEquiv_etaleSourceLocalizationHom` and
  `AlgebraicGeometry.Space.universalDerivation_etaleSourceLocalizationHom`: the forward map of
  the identification, read as a `Y`-derivation of `𝒪_U` through the four bijections, is the
  universal `Y`-derivation `d_{U/Y}`, on sections.  So the identification is the canonical
  comparison and not merely some isomorphism.
* `AlgebraicGeometry.Space.differentialsHomEquiv_etaleSourceLocalizationInv`: the matching
  statement for the backward map.

## Implementation notes

The comparison is not obtained from
`AlgebraicGeometry.SheafOfModules.overDifferentialsIso` (Stacks 04BO) nor from
`Stacks.Sheaves.RingedToposModules.inverseImageDifferentialsIso` (Stacks 08TQ), the two
ready-made identifications of exactly this shape, and the sheaves of differentials here are not
`AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsOfSite`.  The reason is the one recorded in
the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentials.lean`: the small étale site of an
algebraic space has its objects one universe above its morphisms and its structure rings, while
those three constructions put the module sections at the maximum of all three universes, so none
of them can produce a module whose sections live at the universe of the structure rings.  What
*does* apply, its sheaf-of-sets universes being free, is
`Stacks.Sheaves.RingedToposModules.inverseImageDerivationEquiv`, the module-level half of
Stacks 08TQ; it is the one general input used here, and the universal property of the sheaf of
differentials is taken in the hand-built form
`AlgebraicGeometry.Space.differentialsHomEquiv` throughout.

Three definitional identifications are used silently, each discharged by the elaborator:
`AlgebraicGeometry.Space.modulePullback` along `a` is
`Stacks.Sheaves.RingedToposModules.pullbackModules` of the morphism of small étale ringed topoi;
`AlgebraicGeometry.Space.etaleSourcePushforward` is
`AlgebraicGeometry.Space.etaleSourceRestrictScalars` followed by the geometric direct image of
modules, which is the shape
`inverseImageDerivationEquiv` is stated at; and the forgetful image of the clause
`a^{-1}𝒪_X = 𝒪_U` of Stacks 03LV is the morphism that
`AlgebraicGeometry.Space.etaleSourceRestrictScalars` restricts scalars along.  Because of the
first of these the adjunction used is
`Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules` rather than
`AlgebraicGeometry.Space.modulePullbackAdjunction`: the latter is the former transported along
`AlgebraicGeometry.Space.modulePushforwardIso`, and the untransported form is the one whose right
adjoint is literally the composite that `inverseImageDerivationEquiv` speaks about.

The isomorphism is assembled by hand rather than through
`AlgebraicGeometry.SheafOfModules.corepresentableByIso`, which would need the functor of
derivations as an actual functor: `CategoryTheory.Functor.CorepresentableBy` compares the value of
that functor with a type written out, and the two spellings of the small étale site — through the
projections of `AlgebraicGeometry.Space.smallEtaleRingedSite` and through
`AlgebraicGeometry.Space.SmallEtale.topology` — are definitionally but not syntactically equal, so
the comparison is not made at the transparency the elaborator uses there.  The two
identities of the isomorphism are then the argument of `corepresentableByIso` inlined: each is the
injectivity of one of the two bijections followed by their naturality.

The three calculations with derivations that this needs are stated here rather than imported: the
two generic ones about postcomposition, and the naturality of the transport along the ring data.
This keeps the file independent of
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsEtaleLocalization.lean`, which carries
the complementary étale-base step; each is one `rfl` after extensionality.

## References

* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU)
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT), the sheaf of
  differentials of a morphism of algebraic spaces and its universal property.
* [Stacks Project, Tag 08TQ](https://stacks.math.columbia.edu/tag/08TQ), the inverse image of the
  sheaf of relative differentials along a morphism of topoi, whose module-level half is the
  transposition of derivations used here.
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV), the clause
  `a^{-1}𝒪_X = 𝒪_U` for an étale morphism `a`.
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW), the abuse of notation
  `G|_{U_étale} = a^*G`.
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the morphism of small
  étale ringed topoi of a morphism of algebraic spaces and its composition law.
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU) and
  [Tag 03D7](https://stacks.math.columbia.edu/tag/03D7), the adjunction `a^* ⊣ a_*`.
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.RingedToposModules (pushforwardModules pullbackAdjPushforwardModules
  inverseImageDerivationEquiv inverseImageDerivationEquiv_symm_postcomp)
open AlgebraicGeometry.SheafOfModules (derivationEquivOfRingDataIso)

universe t₀ w₀ v₀ u₀ u

/-! ### Calculations with derivations -/

namespace PresheafOfModulesOfCommRing.Derivation'

variable {E : Type u₀} [Category.{v₀} E] {S₁ R : Eᵒᵖ ⥤ CommRingCat.{w₀}}
  {M N L : PresheafOfModules.{t₀} (R ⋙ forget₂ CommRingCat.{w₀} RingCat.{w₀})}
  {a₁ : S₁ ⟶ R}

/-- Postcomposition of a relative derivation by a composite is the composite of the
postcompositions. -/
lemma postcomp_comp (D : PresheafOfModulesOfCommRing.Derivation' M a₁) (α : M ⟶ N) (β : N ⟶ L) :
    D.postcomp (α ≫ β) = (D.postcomp α).postcomp β := by
  apply PresheafOfModulesOfCommRing.Derivation.ext
  ext Z z
  rfl

/-- Postcomposition of a relative derivation by the identity returns it. -/
lemma postcomp_id (D : PresheafOfModulesOfCommRing.Derivation' M a₁) : D.postcomp (𝟙 M) = D := by
  apply PresheafOfModulesOfCommRing.Derivation.ext
  ext Z z
  rfl

end PresheafOfModulesOfCommRing.Derivation'

namespace AlgebraicGeometry.Space

/-- Transport of a relative derivation along an isomorphism of the ring data is natural in the
coefficient module: both operations act on the underlying family of additive maps alone. -/
lemma derivationEquivOfRingDataIso_postcomp {E : Type u₀} [Category.{v₀} E]
    {J : GrothendieckTopology E} {A A' P P' : Sheaf J CommRingCat.{w₀}} (α : A ≅ A') (β : P ≅ P')
    {g : A ⟶ P} {g' : A' ⟶ P'} (hg : g ≫ β.hom = α.hom ≫ g')
    {M N : SheafOfModules.{w₀} ((Stacks.SheafOfModules.Tensor.ringSheaf.{u₀, v₀, w₀} (J := J)) P')}
    (k : M ⟶ N)
    (D : PresheafOfModulesOfCommRing.Derivation' ((SheafOfModules.restrictScalars
      ((Stacks.forgetCommRingSheaf.{v₀, u₀, w₀} J).map β.hom)).obj M).val g.hom) :
    derivationEquivOfRingDataIso α β hg N
        (D.postcomp ((SheafOfModules.restrictScalars
          ((Stacks.forgetCommRingSheaf.{v₀, u₀, w₀} J).map β.hom)).map k).val) =
      (derivationEquivOfRingDataIso α β hg M D).postcomp k.val := by
  apply PresheafOfModulesOfCommRing.Derivation.ext
  ext Z z
  rfl

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y U : AlgebraicSpaces B S hS}

/-- The universal property of the sheaf of differentials is natural in the coefficient module:
reading a composite `Ω_{X/Y} ⟶ F ⟶ G` as a `Y`-derivation postcomposes the derivation of the
first factor with the second. -/
lemma differentialsHomEquiv_comp (p : X ⟶ Y) {F G : Modules.{u, u} B S hS X.1 X.2}
    (k : sheafOfDifferentials B S hS p ⟶ F) (g : F ⟶ G) :
    differentialsHomEquiv B S hS p G (k ≫ g) =
      (differentialsHomEquiv B S hS p F k).postcomp g.val :=
  PresheafOfModulesOfCommRing.Derivation'.postcomp_comp (universalDerivation B S hS p) k.val g.val

/-! ### The ring data of the comparison -/

/-- **Stacks 03G8 at the structure sheaf of the target.**  The inverse image along `a` of
`f^{-1}𝒪_Y` is the inverse image of `𝒪_Y` along the composite:

`a^{-1}f^{-1}𝒪_Y ≅ (a ≫ f)^{-1}𝒪_Y`,

as sheaves of commutative rings on the small étale site of `U`. -/
def inverseImageStructureSheafCompIso (a : U ⟶ X) (f : X ⟶ Y) :
    (smallEtaleInverseImageRing B S hS a).obj (inverseImageStructureSheaf B S hS f) ≅
      inverseImageStructureSheaf B S hS (a ≫ f) :=
  (smallEtaleRingedToposHom_compInverseImageRingIso B S hS a f).app
    (smallEtaleRingedTopos B S hS Y).O

/-- **The ring data of the étale-source comparison is a commutative square.**  The inverse image
along `a` of the structure map `f♯ : f^{-1}𝒪_Y ⟶ 𝒪_X`, followed by the clause
`a^{-1}𝒪_X = 𝒪_U` of Stacks 03LV, is the comparison `a^{-1}f^{-1}𝒪_Y ≅ (a ≫ f)^{-1}𝒪_Y` followed
by the structure map `(a ≫ f)♯`.

This is
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_compInverseImageRingIso_fSharpInverseImage`,
the composition law of Stacks 03G8 in inverse-image form, read in the direction in which the
transport of derivations consumes it. -/
theorem inverseImageStructureSharp_square (a : U ⟶ X) (ha : IsEtale B S hS a.hom) (f : X ⟶ Y) :
    (smallEtaleInverseImageRing B S hS a).map (structureSharpInverseImage B S hS f) ≫
        (etaleInverseImageStructureSheafIso B S hS a ha).hom =
      (inverseImageStructureSheafCompIso B S hS a f).hom ≫
        structureSharpInverseImage B S hS (a ≫ f) :=
  (smallEtaleRingedToposHom_compInverseImageRingIso_fSharpInverseImage B S hS a f).symm

/-! ### The four bijections -/

/-- Restriction of scalars along the inverse-image form `a♯ : a^{-1}𝒪_X ⟶ 𝒪_U` of the structure
map of `a`: an `𝒪_U`-module read as an `a^{-1}𝒪_X`-module. -/
abbrev etaleSourceRestrictScalars (a : U ⟶ X) :=
  SheafOfModules.restrictScalars (smallEtaleRingedToposModulesHom B S hS a).fSharpInverseImage

/-- The direct image of `𝒪_U`-modules along `a` in the untransported shape of Stacks 03D6,
part (1): restriction of scalars along `a♯` followed by the geometric direct image of modules of
Stacks 03D1.  This is the right adjoint of
`Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules`, and
`AlgebraicGeometry.Space.modulePushforward` is it up to
`AlgebraicGeometry.Space.modulePushforwardIso`. -/
abbrev etaleSourcePushforward (a : U ⟶ X) :=
  pushforwardModules (X := smallEtaleRingedTopos B S hS U)
    (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposModulesHom B S hS a)

/-- **The first bijection: the adjunction `a^* ⊣ a_*` of Stacks 03D7.**  A morphism
`a^*Ω_{X/Y} ⟶ C` of `𝒪_U`-modules is a morphism `Ω_{X/Y} ⟶ a_*C` of `𝒪_X`-modules. -/
def etaleSourceAdjEquiv (a : U ⟶ X) (f : X ⟶ Y) (C : Modules.{u, u} B S hS U.1 U.2) :
    ((modulePullback B S hS a).obj (sheafOfDifferentials B S hS f) ⟶ C) ≃
      (sheafOfDifferentials B S hS f ⟶ (etaleSourcePushforward B S hS a).obj C) :=
  (pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS U)
      (Y := smallEtaleRingedTopos B S hS X)
      (smallEtaleRingedToposModulesHom B S hS a)).homEquiv
    (sheafOfDifferentials B S hS f) C

/-- The first bijection is natural in the coefficient module. -/
lemma etaleSourceAdjEquiv_comp (a : U ⟶ X) (f : X ⟶ Y)
    {C C' : Modules.{u, u} B S hS U.1 U.2} (g : C ⟶ C')
    (k : (modulePullback B S hS a).obj (sheafOfDifferentials B S hS f) ⟶ C) :
    etaleSourceAdjEquiv B S hS a f C' (k ≫ g) =
      etaleSourceAdjEquiv B S hS a f C k ≫ (etaleSourcePushforward B S hS a).map g :=
  Adjunction.homEquiv_naturality_right _ k g

/-- **The third bijection: the transposition of derivations of Stacks 08TQ.**  A `Y`-derivation of
`𝒪_X` with values in `a_*C` is an `a^{-1}f^{-1}𝒪_Y`-derivation of `a^{-1}𝒪_X` with values in `C`,
by the adjunction `a^{-1} ⊣ a_*` on the small étale topoi. -/
abbrev etaleSourceTransposeEquiv (a : U ⟶ X) (f : X ⟶ Y)
    (C : Modules.{u, u} B S hS U.1 U.2) :=
  (inverseImageDerivationEquiv (smallEtaleRingedToposHom B S hS a).toToposHom
    (structureSharpInverseImage B S hS f)
    ((etaleSourceRestrictScalars B S hS a).obj C)).symm

/-- The third bijection is natural in the coefficient module. -/
lemma etaleSourceTransposeEquiv_postcomp (a : U ⟶ X) (f : X ⟶ Y)
    {C C' : Modules.{u, u} B S hS U.1 U.2} (g : C ⟶ C')
    (D : PresheafOfModulesOfCommRing.Derivation' ((etaleSourcePushforward B S hS a).obj C).val
      (structureSharpInverseImage B S hS f).hom) :
    etaleSourceTransposeEquiv B S hS a f C'
        (D.postcomp ((etaleSourcePushforward B S hS a).map g).val) =
      (etaleSourceTransposeEquiv B S hS a f C D).postcomp
        ((etaleSourceRestrictScalars B S hS a).map g).val :=
  (inverseImageDerivationEquiv_symm_postcomp (smallEtaleRingedToposHom B S hS a).toToposHom
    (structureSharpInverseImage B S hS f) ((etaleSourceRestrictScalars B S hS a).map g) D).symm

/-- **The fourth bijection: the transport along the ring data.**  For an étale `a` the two
comparisons of `AlgebraicGeometry.Space.inverseImageStructureSharp_square` are invertible — the
first by the composition law of Stacks 03G8, the second by the clause `a^{-1}𝒪_X = 𝒪_U` of
Stacks 03LV — so an `a^{-1}f^{-1}𝒪_Y`-derivation of `a^{-1}𝒪_X` with values in `C` is a
`Y`-derivation of `𝒪_U` with values in `C`. -/
abbrev etaleSourceRingDataEquiv (a : U ⟶ X) (ha : IsEtale B S hS a.hom) (f : X ⟶ Y)
    (C : Modules.{u, u} B S hS U.1 U.2) :=
  derivationEquivOfRingDataIso (inverseImageStructureSheafCompIso B S hS a f)
    (etaleInverseImageStructureSheafIso B S hS a ha)
    (inverseImageStructureSharp_square B S hS a ha f) C

/-- **The third and fourth bijections are natural in the coefficient module.**  The two are
stated together because the type of a derivation over the transported ring data, which is where
the third bijection lands, is not expressible without naming the transport. -/
lemma etaleSourceRingDataEquiv_postcomp (a : U ⟶ X) (ha : IsEtale B S hS a.hom) (f : X ⟶ Y)
    {C C' : Modules.{u, u} B S hS U.1 U.2} (g : C ⟶ C')
    (D : PresheafOfModulesOfCommRing.Derivation' ((etaleSourcePushforward B S hS a).obj C).val
      (structureSharpInverseImage B S hS f).hom) :
    etaleSourceRingDataEquiv B S hS a ha f C'
        (etaleSourceTransposeEquiv B S hS a f C'
          (D.postcomp ((etaleSourcePushforward B S hS a).map g).val)) =
      (etaleSourceRingDataEquiv B S hS a ha f C
        (etaleSourceTransposeEquiv B S hS a f C D)).postcomp g.val :=
  (congrArg (fun z ↦ etaleSourceRingDataEquiv B S hS a ha f C' z)
      (etaleSourceTransposeEquiv_postcomp B S hS a f g D)).trans
    (derivationEquivOfRingDataIso_postcomp (inverseImageStructureSheafCompIso B S hS a f)
      (etaleInverseImageStructureSheafIso B S hS a ha)
      (inverseImageStructureSharp_square B S hS a ha f) g
      (etaleSourceTransposeEquiv B S hS a f C D))

/-! ### The étale restriction of the differentials corepresents the derivations -/

/-- **The morphisms out of `a^*Ω_{X/Y}` are the `Y`-derivations of `𝒪_U`.**  For an étale
`a : U ⟶ X` and any `f : X ⟶ Y`, the composite of the four bijections above: the adjunction
`a^* ⊣ a_*` of Stacks 03D7, the universal property of `Ω_{X/Y}` of Stacks 04CT, the transposition
of derivations along the morphism of small étale topoi of `a` (Stacks 08TQ at the level of
modules), and the transport of derivations along the ring data of
`AlgebraicGeometry.Space.inverseImageStructureSharp_square`. -/
def derivationEtalePullbackEquiv (a : U ⟶ X) (ha : IsEtale B S hS a.hom) (f : X ⟶ Y)
    (C : Modules.{u, u} B S hS U.1 U.2) :
    ((modulePullback B S hS a).obj (sheafOfDifferentials B S hS f) ⟶ C) ≃
      PresheafOfModulesOfCommRing.Derivation' C.val
        (structureSharpInverseImage B S hS (a ≫ f)).hom :=
  (etaleSourceAdjEquiv B S hS a f C).trans
    ((differentialsHomEquiv B S hS f ((etaleSourcePushforward B S hS a).obj C)).trans
      ((etaleSourceTransposeEquiv B S hS a f C).trans
        (etaleSourceRingDataEquiv B S hS a ha f C)))

/-- The composite bijection, spelled out as the four bijections applied in turn. -/
lemma derivationEtalePullbackEquiv_apply (a : U ⟶ X) (ha : IsEtale B S hS a.hom) (f : X ⟶ Y)
    (C : Modules.{u, u} B S hS U.1 U.2)
    (k : (modulePullback B S hS a).obj (sheafOfDifferentials B S hS f) ⟶ C) :
    derivationEtalePullbackEquiv B S hS a ha f C k =
      etaleSourceRingDataEquiv B S hS a ha f C
        (etaleSourceTransposeEquiv B S hS a f C
          (differentialsHomEquiv B S hS f ((etaleSourcePushforward B S hS a).obj C)
            (etaleSourceAdjEquiv B S hS a f C k))) :=
  rfl

/-- **The bijection of `AlgebraicGeometry.Space.derivationEtalePullbackEquiv` is natural in the
coefficient module**, each of its four factors being so.  This is what makes `a^*Ω_{X/Y}` a
corepresenting object of the functor of `Y`-derivations of `𝒪_U`. -/
theorem derivationEtalePullbackEquiv_comp (a : U ⟶ X) (ha : IsEtale B S hS a.hom) (f : X ⟶ Y)
    {C C' : Modules.{u, u} B S hS U.1 U.2} (g : C ⟶ C')
    (k : (modulePullback B S hS a).obj (sheafOfDifferentials B S hS f) ⟶ C) :
    derivationEtalePullbackEquiv B S hS a ha f C' (k ≫ g) =
      (derivationEtalePullbackEquiv B S hS a ha f C k).postcomp g.val := by
  have h₁ : differentialsHomEquiv B S hS f ((etaleSourcePushforward B S hS a).obj C')
        (etaleSourceAdjEquiv B S hS a f C' (k ≫ g)) =
      (differentialsHomEquiv B S hS f ((etaleSourcePushforward B S hS a).obj C)
          (etaleSourceAdjEquiv B S hS a f C k)).postcomp
        ((etaleSourcePushforward B S hS a).map g).val :=
    (congrArg (fun z ↦ differentialsHomEquiv B S hS f
          ((etaleSourcePushforward B S hS a).obj C') z)
        (etaleSourceAdjEquiv_comp B S hS a f g k)).trans
      (differentialsHomEquiv_comp B S hS f (etaleSourceAdjEquiv B S hS a f C k)
        ((etaleSourcePushforward B S hS a).map g))
  refine Eq.trans (derivationEtalePullbackEquiv_apply B S hS a ha f C' (k ≫ g)) ?_
  refine Eq.trans (congrArg (fun z ↦ etaleSourceRingDataEquiv B S hS a ha f C'
    (etaleSourceTransposeEquiv B S hS a f C' z)) h₁) ?_
  refine Eq.trans (etaleSourceRingDataEquiv_postcomp B S hS a ha f g
    (differentialsHomEquiv B S hS f ((etaleSourcePushforward B S hS a).obj C)
      (etaleSourceAdjEquiv B S hS a f C k))) ?_
  exact congrArg (fun z ↦ PresheafOfModulesOfCommRing.Derivation.postcomp z g.val)
    (derivationEtalePullbackEquiv_apply B S hS a ha f C k).symm

/-! ### Stacks 04CU, the étale-source localization -/

/-- The forward comparison `a^*Ω_{X/Y} ⟶ Ω_{U/Y}`: the morphism through which the universal
`Y`-derivation `d_{U/Y}` factors, by
`AlgebraicGeometry.Space.derivationEtalePullbackEquiv`. -/
def etaleSourceLocalizationHom (a : U ⟶ X) (ha : IsEtale B S hS a.hom) (f : X ⟶ Y) :
    (modulePullback B S hS a).obj (sheafOfDifferentials B S hS f) ⟶
      sheafOfDifferentials B S hS (a ≫ f) :=
  (derivationEtalePullbackEquiv B S hS a ha f (sheafOfDifferentials B S hS (a ≫ f))).symm
    (universalDerivation B S hS (a ≫ f))

/-- The backward comparison `Ω_{U/Y} ⟶ a^*Ω_{X/Y}`: the morphism through which the universal
element of the corepresentation of `a^*Ω_{X/Y}` — the `Y`-derivation attached to the identity —
factors, by the universal property of `Ω_{U/Y}`. -/
def etaleSourceLocalizationInv (a : U ⟶ X) (ha : IsEtale B S hS a.hom) (f : X ⟶ Y) :
    sheafOfDifferentials B S hS (a ≫ f) ⟶
      (modulePullback B S hS a).obj (sheafOfDifferentials B S hS f) :=
  (differentialsHomEquiv B S hS (a ≫ f)
      ((modulePullback B S hS a).obj (sheafOfDifferentials B S hS f))).symm
    (derivationEtalePullbackEquiv B S hS a ha f
      ((modulePullback B S hS a).obj (sheafOfDifferentials B S hS f))
      (𝟙 ((modulePullback B S hS a).obj (sheafOfDifferentials B S hS f))))

/-- **The defining property of the forward comparison.**  Read as a `Y`-derivation of `𝒪_U`
through the four bijections, it is the universal `Y`-derivation `d_{U/Y}`. -/
@[stacks 04CU "the étale-source comparison is the one matching the universal derivations"]
theorem derivationEtalePullbackEquiv_etaleSourceLocalizationHom (a : U ⟶ X)
    (ha : IsEtale B S hS a.hom) (f : X ⟶ Y) :
    derivationEtalePullbackEquiv B S hS a ha f (sheafOfDifferentials B S hS (a ≫ f))
        (etaleSourceLocalizationHom B S hS a ha f) =
      universalDerivation B S hS (a ≫ f) :=
  Equiv.apply_symm_apply _ _

/-- **The defining property of the backward comparison.** -/
theorem differentialsHomEquiv_etaleSourceLocalizationInv (a : U ⟶ X)
    (ha : IsEtale B S hS a.hom) (f : X ⟶ Y) :
    differentialsHomEquiv B S hS (a ≫ f)
        ((modulePullback B S hS a).obj (sheafOfDifferentials B S hS f))
        (etaleSourceLocalizationInv B S hS a ha f) =
      derivationEtalePullbackEquiv B S hS a ha f
        ((modulePullback B S hS a).obj (sheafOfDifferentials B S hS f))
        (𝟙 ((modulePullback B S hS a).obj (sheafOfDifferentials B S hS f))) :=
  Equiv.apply_symm_apply _ _

/-- **Stacks 04CU, the étale-source localization.**  Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S` and let `a : U ⟶ X` be étale.  The restriction of `Ω_{X/Y}` to the small étale
site of `U` — the pullback of `𝒪_X`-modules along `a`, by the abuse of notation of Stacks'
Equation 03LW — is the sheaf of differentials of the composite:

`a^*Ω_{X/Y} ≅ Ω_{U/Y}`.

Both sides corepresent the functor of `Y`-derivations of `𝒪_U`, the left-hand side by
`AlgebraicGeometry.Space.derivationEtalePullbackEquiv` and the right-hand side by its own
universal property, so they are canonically isomorphic; the two morphisms are the ones through
which the two universal derivations factor.

This is the clause of Stacks 04CU that
`AlgebraicGeometry.Space.sheafOfDifferentialsEtaleLocalizationIso` consumes directly.  Together
with the étale-base step `AlgebraicGeometry.Space.sheafOfDifferentialsIsoOfSharpIso` it gives the
identification `Ω_{X/Y}|_{U_étale} ≅ Ω_{U/V}` on a square of étale charts that the source
states. -/
@[stacks 04CU "the étale-source localization `a^*Ω_{X/Y} ≅ Ω_{U/Y}` along an étale `a : U ⟶ X`:
  the first step of the source's proof, Properties of Spaces 03LP and Equation 03LQ together with
  Modules on Sites 04BO"]
def sheafOfDifferentialsEtaleSourceLocalizationIso (a : U ⟶ X) (ha : IsEtale B S hS a.hom)
    (f : X ⟶ Y) :
    (modulePullback B S hS a).obj (sheafOfDifferentials B S hS f) ≅
      sheafOfDifferentials B S hS (a ≫ f) where
  hom := etaleSourceLocalizationHom B S hS a ha f
  inv := etaleSourceLocalizationInv B S hS a ha f
  hom_inv_id := by
    refine (derivationEtalePullbackEquiv B S hS a ha f
      ((modulePullback B S hS a).obj (sheafOfDifferentials B S hS f))).injective ?_
    rw [derivationEtalePullbackEquiv_comp,
      derivationEtalePullbackEquiv_etaleSourceLocalizationHom]
    exact differentialsHomEquiv_etaleSourceLocalizationInv B S hS a ha f
  inv_hom_id := by
    refine (differentialsHomEquiv B S hS (a ≫ f)
      (sheafOfDifferentials B S hS (a ≫ f))).injective ?_
    rw [differentialsHomEquiv_comp, differentialsHomEquiv_etaleSourceLocalizationInv,
      ← derivationEtalePullbackEquiv_comp, Category.id_comp,
      derivationEtalePullbackEquiv_etaleSourceLocalizationHom]
    exact (PresheafOfModulesOfCommRing.Derivation'.postcomp_id
      (universalDerivation B S hS (a ≫ f))).symm

/-- **Stacks 04CU, the étale-source localization on local sections.**  Reading the forward map of
the identification `a^*Ω_{X/Y} ≅ Ω_{U/Y}` as a `Y`-derivation of `𝒪_U`, by the four bijections of
`AlgebraicGeometry.Space.derivationEtalePullbackEquiv`, returns the universal differential
`d_{U/Y}(x)` of every local section `x` of `𝒪_U`.  So the identification is the canonical
comparison and not merely some isomorphism. -/
@[stacks 04CU "the étale-source localization carries the universal derivation of the restriction
  to the universal derivation `d_{U/Y}`, on local sections"]
theorem universalDerivation_etaleSourceLocalizationHom (a : U ⟶ X) (ha : IsEtale B S hS a.hom)
    (f : X ⟶ Y) {W : (SmallEtale B S hS U.1)ᵒᵖ}
    (x : (structureRingSheaf B S hS U).obj.obj W) :
    (derivationEtalePullbackEquiv B S hS a ha f (sheafOfDifferentials B S hS (a ≫ f))
        (sheafOfDifferentialsEtaleSourceLocalizationIso B S hS a ha f).hom).d x =
      (universalDerivation B S hS (a ≫ f)).d x :=
  PresheafOfModulesOfCommRing.Derivation.congr_d
    (derivationEtalePullbackEquiv_etaleSourceLocalizationHom B S hS a ha f) x

end AlgebraicGeometry.Space

end
